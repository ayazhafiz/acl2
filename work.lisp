; vim: foldmethod=marker
(include-book "books/acl2s/cgen/top")
(include-book "books/kestrel/std/system/add-suffix-to-fn-or-const")
(include-book "books/std/util/defprojection")
(include-book "books/std/util/defmapappend")

(ubt! 'fndata-p)
(acl2s-defaults :set verbosity-level 4)

(defun rev2 (x)
  (declare (xargs :guard (listp x) :VERIFY-GUARDS NIL))
  (if (consp x)
      (append (rev2 (cdr x)) (car x))
      nil))

; (test? (equal (rev (rev x)) x))

(defun getvars (form state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (declare (ignorable state))
  (cw  "~|vars: ~x0~|" (all-vars form))
  )

(defmacro getvarsM (form &rest kwd-val-lst)
  (let* ((vl-entry (assoc-keyword :verbosity-level kwd-val-lst))
         (vl (and vl-entry (cadr vl-entry)))
         (debug (and (natp vl) (cgen::debug-flag vl))))
        `(with-output
          :stack :push
          ,(if debug :on :off) :all
          :gag-mode ,(not debug)
          (make-event
           (getvars ',form state)))))

(defun getfuncs (form state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (declare (ignorable state))
  (cw  "~|vars: ~x0~|" (all-fnnames form)))

(defmacro getfuncsM (form)
  `(with-output
    :stack :push
    ,:on :all
    :gag-mode ,(not t)
    (make-event
     (getfuncs ',form state))))

(defun fndata-p (d)
  (declare (xargs :guard t))
  (and (symbol-alistp d)
       (assoc 'arity d)
       (assoc 'guard d)
       (assoc 'formals d)))

(defun fn-datas (fns state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (endp fns)
      nil
      (b* ((fn (car fns))
           (wrld (w state))
           (arity (acons 'arity (arity fn wrld) nil))
           (guard (acons 'guard (guard fn nil wrld) nil))
           (formals (acons 'formals (formals fn wrld) nil)))
          (acons fn (append arity guard formals) (fn-datas (cdr fns) state)))))

;; Returns a list of numbers [1..=n]
(defun list-of-n (n)
  (declare (xargs :mode :program))
  (if (= n 1) (list 1) (cons n (list-of-n (- n 1)))))


;;;;; GEN STATE {{{

(defun st-new (fn-data nmax-vars)
  (declare (xargs :guard (fndata-p fn-data) :verify-guards nil))
  (b* ((fns (acons 'fns fn-data nil))
       (cached-terms (acons 'cached-terms nil nil))
       (max-vars (acons 'max-vars nmax-vars nil)))
      (append fns cached-terms max-vars)))

(defun st-p (st)
  (declare (xargs :guard t))
  (and (symbol-alistp st)
       (assoc 'fns st)
       (assoc 'cached-terms st)
       (assoc 'max-vars st)))

(defun aget (key l)
  (declare (xargs :mode :program :guard (alistp l) :verify-guards nil))
  (cdr (assoc key l)))

(defun st-get (key st)
  (declare (xargs :mode :program :guard (st-p st) :verify-guards nil))
  (aget key st))

(defun st-all-fns (st)
  (declare (xargs :mode :program :guard (st-p st) :verify-guards nil))
  (strip-cars (st-get 'fns st)))

(defun st-fn-exists (st fn)
  (declare (xargs :mode :program :guard (st-p st) :verify-guards nil))
  (if (assoc fn (st-get 'fns st)) t nil))

(defun st-fn-data (st fn what)
  (declare (xargs :mode :program :guard (and (st-p st) (symbolp what))))
  (aget what (aget fn (st-get 'fns st ))))

(defun st-get-terms (st size)
  (declare (xargs :mode :program :guard (st-p st) :verify-guards nil))
  (aget size (st-get 'cached-terms st)))

(defun st-cache-terms (st size terms)
  (declare (xargs :mode :program :guard (st-p st) :verify-guards nil))
  (b* ((oldt (st-get 'cached-terms st))
       (newt (put-assoc size terms oldt)))
      (put-assoc 'cached-terms newt st)))

; }}}

(defun reflow-head-with-rests (st head rests)
  (declare (xargs :mode :program))
  (if (endp rests)
      nil
      (let* ((tail (car rests))
             (tail (if (listp tail) tail (list tail))) ; force listify tail if needed
             (inst (if (eq (st-fn-exists st (car tail)) nil)
                       (cons head tail)
                       (cons head (list tail)))) ; wrap function calls
             (res (cons inst (reflow-head-with-rests st head (cdr rests)))))
            ;(prog2$ (cw "~% reflowhead: head:~x0 tail:~x1 :: ~x2~%" head (car rests) res)
            res
            ;)
            ))
  )

(defun reflow-heads-with-rests (st heads rests)
  (declare (xargs :mode :program))
  (if (endp heads)
      nil
      (let* ((res (append (reflow-head-with-rests st (car heads) rests) (reflow-heads-with-rests st (cdr heads) rests))))
            ;(prog2$ (cw "~% after reflows[heads: ~x0, tails: ~x1]: ~x2~%" heads rests res)
            res
            ;)
            )))

(defun enlist (lst)
  (declare (xargs :mode :program))
  (if (endp lst)
      nil
      (cons (list (car lst)) (enlist (cdr lst)))))

(def-const *GEN-HOLE* '_HOLE_)

; (def-const *base-var-names*
;   '(X Y Z A B C D G L K M N))

(defun fresh-name (base avoid)
  (declare (xargs :mode :program))
  (if (member base avoid)
      (fresh-name (add-suffix-to-fn-or-const base '$) avoid)
      base))

; (defun n-fresh-names (howmany avoid basis)
;   (declare (xargs :mode :program))
;   (if (zerop howmany)
;       nil
;       (cons (fresh-name (car basis) avoid) (n-fresh-names (1- howmany) avoid (cdr basis)))))

;;;;; HOLED TERM GENERATION {{{

(mutual-recursion
 ;; Creates a term sequence, given the possible sizes for the head term.
 ;; Specifically, map over the head sizes, for each size creating a head term of
 ;; that size and terms in the rest of the sequence of the remaining sequence
 ;; size.
 (defun make-term--seq-map-over-head (st heads num-terms size)
   (declare (xargs :mode :program ))
   (if (endp heads)
       (mv nil st)
       (b* (((mv head-terms st) (make-term st (car heads)))
            ((mv tail-terms st) (make-term--seq-permute-over-size st
                                                                  (1- num-terms)
                                                                  (- size (car heads)))))
           (cond
            ((zerop num-terms) (mv nil st))
            ((= num-terms 1) (mv head-terms st))
            ; ((xor (endp head-terms) (endp tail-terms)) nil)
            (t (b* ((insts-for-headsize (reflow-heads-with-rests st head-terms tail-terms))
                    ((mv allrest st) (make-term--seq-map-over-head st (cdr heads) num-terms size)))
                   ; (prog2$ (cw  "~%heads: ~x0    tails: ~x1     instances: ~x2~|" head-terms tail-terms insts-for-headsize)
                   (mv (append insts-for-headsize allrest) st)
                   ;)
                   ))))))
 
 ;; Creates a list of sequences of terms, list(S), where the number of terms in
 ;; S is equal to "num-terms" and the sum of their sizes is equal to "size".
 ;; This is just a permutation over the ways to arrange "num-terms" terms in a
 ;; sequence s.t. their sizes respect the invariant sum "size".
 (defun make-term--seq-permute-over-size (st num-terms size)
   (declare (xargs :mode :program ))
   (cond
    ((zerop num-terms) (mv nil st))
    (t (b* ((num-tail-terms (1- num-terms))
            (max-head-size (- size num-tail-terms))
            (head-sizes (list-of-n max-head-size)))
           (make-term--seq-map-over-head st head-sizes num-terms size)))
    )
   )
 
 ;; Creates a list of terms of a given size walking over all possible functions
 ;; available for the term generation.
 (defun make-term--walkfns (st fns size)
   (declare (xargs :mode :program :guard (listp fns) :verify-guards nil))
   (if (endp fns)
       (mv nil st)
       (let* ((fn (car fns))
              (arity (st-fn-data st fn 'arity)))
             (if (< arity size)
                 ; When (function name + arity) is less than or equal to the target
                 ; term size, we can fit that function in as an instance of the sized
                 ; term.
                 (b* (((mv seqs st) (make-term--seq-permute-over-size st arity (1- size)))
                      (instances (reflow-head-with-rests st fn seqs))
                      ((mv allrest st) (make-term--walkfns st (cdr fns) size)))
                     (mv (append instances allrest) st))
                 ; Otherwise, the arity > target size and there is no way we can fit a
                 ; call instance in the term.
                 (make-term--walkfns st (cdr fns) size)))))
 
 ;; Creates a list of terms of a given "size".
 ;; "size" is measured by the number of items (functions/variables/constants)
 ;; present in the term.
 (defun make-term (st size)
   (declare (xargs :mode :program))
   (b* ((terms (st-get-terms st size))
        ((mv terms st) (if terms
                           (mv terms st)
                           (cond
                            ; Nothing, just bail
                            ((zerop size) (mv nil st))
                            ; Just give back a hole for now. We will fill this
                            ; in with fresh variables in a later pass.
                            ((= size 1) (mv (list *GEN-HOLE*) st))
                            ; Otherwise, fill the sized hole with a function call
                            (t (make-term--walkfns st (st-all-fns st) size)))))
        (st (st-cache-terms st size terms)))
       (mv terms st)))
 ) ; }}}

;;;;; VARIABLE COLLECTION {{{

;; Collects the variables present in a term.
(define collect-vars ((st st-p) (term pseudo-termp))
  :mode :program
  (cond ((listp term)
         (if (endp term)
             nil
             (if (st-fn-exists st (car term))
                 (collect-vars st (cdr term))
                 (cons (car term) (collect-vars st (cdr term))))))
        (t (if (st-fn-exists st term)
               nil
               term)))
  )

; }}}

(def-const *empty-vars-store*
  (acons 'frozen nil
         (acons 'vars nil
                (acons 'sym 65 nil))))

(define frozen-vars-store ((vars listp))
  (put-assoc 'frozen t
             (put-assoc 'vars vars *empty-vars-store*)))

;;;;; TERM REIFICATION {{{

;; Given a term with holes, places variables in those holes.
;; At each hole, the choices are either (1) any previously instantiated
;; variable, or (2) a fresh variable.
(define reify-term ((st st-p) (term pseudo-termp) (vs alistp))
  :mode :program :verify-guards nil
  (cond ((and (listp term) (endp term)) (mv (list nil) vs))
        ((st-fn-exists st term) (mv (list term) vs))
        ((and (listp term)
              (not (eq (car term) *GEN-HOLE*)))
         (b* (((mv heads vs) (reify-term st (car term) vs))
              ((mv tails vs) (reify-term st (cdr term) vs)))
             (mv (reflow-heads-with-rests st heads tails) vs)))
        (t ; (and (listp term) (eq (car term) *GEN-HOLE*))
           (b* ((vs (if (aget 'frozen vs)
                        ; frozen => use present vars
                        vs
                        ; not frozen => add a fresh variable, then any present variable is a choice
                        (b* ((avoid (append (aget 'vars vs) (st-all-fns st)))
                             (symno (aget 'sym vs))
                             (basis (intern (string (code-char symno)) "ACL2"))
                             (fresh (fresh-name basis avoid))
                             (allvars (cons fresh (aget 'vars vs)))
                             (vs (put-assoc 'vars allvars vs))
                             (vs (put-assoc 'sym (1+ symno) vs)))
                            vs)))
                (possible-vars (aget 'vars vs))
                ((mv tails vs) (reify-term st (cdr term) vs)))
               (mv
                (reflow-heads-with-rests st possible-vars tails)
                vs)))
        )
  )

(define reify-term-top ((st st-p) (term pseudo-termp))
  :mode :program :verify-guards nil
  (b* (((mv terms ?) (reify-term st term *empty-vars-store*)))
      terms))

(std::defmapappend reify-term-list (st x)
                   :mode :program
                   :guard (and (st-p st) (pseudo-termp x))
                   (reify-term-top st x))
;}}}

;;;;; RTERM REIFICATION {{{
;; Given a single concrete lterm and a list of holed rterms,
;;   1. collect the variables in the lterm (TODO collect these on-the-fly
;;      during reify-term)
;;   2. reify each rterm with variables in the lterm
;;   3. return a concrete pair of (lterm, rterm) ready to be used for a theorem.

(std::defprojection pair-each (left x)
                    :mode :program
                    (cons left x))

(define reify-holed-rterms--inner ((st st-p) (vs listp) (lterm pseudo-termp) (rterms listp))
  :mode :program
  (if (endp rterms)
      nil
      (b* (((mv reified-rterms ?) (reify-term st (car rterms) vs))
           (lrterms (pair-each lterm (enlist reified-rterms))))
          (append lrterms (reify-holed-rterms--inner st vs lterm (cdr rterms))))))

(define reify-holed-rterms ((st st-p) (lterm pseudo-termp) (rterms listp))
  :mode :program
  (b* ((lvars (collect-vars st lterm))
       (vs (frozen-vars-store lvars)))
      (reify-holed-rterms--inner st vs lterm rterms)))

(std::defmapappend pair-lterms-holed-rterms (st x holed-rterms)
                   :mode :program
                   :guard (and (st-p st) (pseudo-termp x) (listp holed-rterms))
                   (reify-holed-rterms st x holed-rterms))
;}}}

;;;; TERM REPR {{{

;; An lrpair is a pair of terms '(l r) for which a rewrite conjecture will be
;; constructed.
(defun lrpairp (lrpair)
  (and (listp lrpair)
       (= (length lrpair) 2)
       (pseudo-termp (car lrpair))
       (pseudo-termp (cadr lrpair))))

;; An lrconj is a triple '(l r hyps) where l, r are terms and hyps is a list of
;; terms constituting hypotheses.
(defun lrconjp (lrconj)
  (and (listp lrconj)
       (= (length lrconj) 3)
       (pseudo-termp (car lrconj))
       (pseudo-termp (cadr lrconj))
       (pseudo-term-listp (caddr lrconj))))

; }}}

;;;;; HYPOTHESIS COLLECTION {{{

;; Given two lists of variables and substitution values, returns an alist where
;; each element is a pair (var->substitution)
(define make-substs ((vars pseudo-term-listp) (vals pseudo-term-listp))
  :mode :program
  (cond
    ((and (endp vars) (endp vals)) nil)
    ((or (endp vars) (endp vals))
     (er hard 'top-level "vars and vals of different lengths: ~x0 and ~x1~%" vars vals))
    (t (acons (car vars) (car vals) (make-substs (cdr vars) (cdr vals))))))

(define apply-substs ((term pseudo-termp) (substs alistp))
  :mode :program
  (cond
    ((and (listp term) (endp term)) nil)
    ((listp term)
     (b* ((subst-term (or (aget (car term) substs) (car term))))
         (cons subst-term (apply-substs (cdr term) substs))))
    (t (or (aget term substs) term))))

;; Given a pseudo-term for a function call, of form
;;   (FN p1 p2 ...pn)
;; returns "reasonable" hypotheses we can make about the term, namely from the
;; guard of FN. Done by
;;   1. extract the guard of FN
;;   2. extract the formals of FN
;;   3. create the substitutions [formal_i->parameter_i]i\in 1,\dots,n
;;   4. apply the substitution to the guard
(define extract-hyp-from-fn-call ((st st-p) (call pseudo-termp))
  :mode :program
  :guard (st-fn-exists st (car call)) ; make sure we're not getting nonsense from the hyps collector
  ; :returns (hyp pseudo-termp)
  (b* ((fn (car call))
       (guard (st-fn-data st fn 'guard))
       (formals (st-fn-data st fn 'formals))
       (substs (make-substs formals (cdr call)))
       )
      (apply-substs guard substs)))

;; Given a term of form
;;   (FN A$ (FN2 B$ C$))
;; extracts all hypotheses we can make about the term given its present
;; functions and variables.
;; Namely,
;;   - for each function call, extract the function guards with the associated term values
;;
;; Returns a list of terms representing the hypotheses present in the term, or
;; nil if there are none. Hypotheses are ordered from those recovered from
;; innermost terms to those recovered from outermost terms.
(define extract-hyps-from-term ((st st-p) (term pseudo-termp))
  :mode :program
  ; :returns (listp hyps)
  (if (or (not (listp term)) (endp term))
    ; Can't make any hypotheses from atoms.
    nil
    (b* (
         ; This may be a function call, if we are at the start of the list. Check if
         ; the first term is a function, and if so, extract the hypothesis.
         (frontload-hyps (if (st-fn-exists st (car term))
                              (list (extract-hyp-from-fn-call st term))
                              nil))
         ; The first term might itself be a nested function call, so get
         ; hypotheses from those too.
         (front-inner-hyps (extract-hyps-from-term st (car term)))
         (rest-hyps (extract-hyps-from-term st (cdr term))))
        (append (append front-inner-hyps rest-hyps) frontload-hyps))))

;; Given an lrpair '(l r) returns an lrconj '(l r hyps) with the hypotheses
;; absorbed from l and r in hyps.
(define lrterm-hypothesize ((st st-p) (lrpair lrpairp))
  :mode :program
  ; :returns (lrconjp conj)
  (prog2$ (cw "~% pair:~x0~%" lrpair)
   (append lrpair (list (append (extract-hyps-from-term st (car lrpair))
                                (extract-hyps-from-term st (cadr lrpair)))))))

(std::defprojection lrterm2conj-list ((st st-p) (x listp))
                    :mode :program
                    (lrterm-hypothesize st x))

;}}}

;;;;; THEOREM CREATION {{{

;; Folds an lrconj (left right hyps) into a proper theorem
;; (IMPLIES ,hyps (EQUAL ,left ,right))
(define lrconj2thm ((lrconj lrconjp))
  :mode :program
  (prog2$ (cw "~% conj:~x0~%" lrconj)
   `(IMPLIES
     ,(cons 'AND (caddr lrconj))
     (EQUAL ,(car lrconj) ,(cadr lrconj)))))

(std::defprojection lrconj2thm-list (x)
                    :mode :program
                    (lrconj2thm x))

;}}}

;;;;; MAIN DRIVERS

(defun make-term-top (fn-data size)
  (declare (xargs :mode :program))
  (b* (
       ; (1) break up sizes - left >= right
       (left (ceiling size 2))
       (right (- size left))
       (st (st-new fn-data left))
       ; (2) create holed terms
       ((mv lterms-holed st) (make-term st left))
       ((mv rterms-holed st) (if (= left right)
                                 (mv lterms-holed st)
                                 (make-term st right)))
       ; (3) instantiate lterms with concrete vars
       (lterms (reify-term-list st lterms-holed))
       ; (4) for each lterm, instantiate one of each rterm with concrete
       ; variables from the set of variables in the lterm. Now we have pairs
       ; of concrete terms (left, right) to be used in a theorem.
       (lr-pairs (pair-lterms-holed-rterms st lterms rterms-holed))
       ; (5) for each lrpair, generate a lrconj with hypotheses collected from
       ; the l/r terms.
       (lr-conjs (lrterm2conj-list st lr-pairs))
       ; (6) collapse lrconjs into a theorem
       (thms (lrconj2thm-list lr-conjs)))
      thms))

(defmacro fn-dataM (fns)
  `(fn-datas ,fns state))

(defmacro make-termM (fns size)
  `(make-term-top (fn-dataM ,fns) ,size))

; TODO
; HARD ACL2 ERROR in RAW-EV-FNCALL:  We had thought that *1* functions
; were always defined outside the first pass of initialization, but the
; *1* function for AND, which should be ACL2_*1*_COMMON-LISP::AND, is
; not.
; Probably we are not sanitizing the term before passing it to the
; waterfall.
(defun proveit (term state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (b* ((toprove (prog2$ (cw "~%Now attempting proof of ~x0~%" term) term))
       ((mv erp trval state) (acl2::state-global-let*
                              ((acl2::inhibit-output-lst
                                (cond (t #!acl2(set-difference-eq *valid-output-names* '(error))))))
                              (acl2::prove toprove (acl2::make-pspv (acl2::ens state) (w state) state) (acl2::default-hints (w state)) (acl2::ens state) (w state) "thm..." state)
                              ))
       ((mv ? prove-okp state) (mv erp (if erp (cadr trval) t) state))
       )
      ; (prog2$ (cw "~%Attempted proof of ~x0: erp ~x1, trivial ~x2~|" toprove erp trval)
      (mv prove-okp state)
      ; )
      )
  )

(defun runit (terms state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (if (endp terms) (mv nil nil nil state)
      (b* ((term (car terms))
           ((mv proved no-ce has-ce state) (runit (cdr terms) state))
           ; ((mv ? no-ce-p state) (acl2s::test?-fn term nil nil state))
           ((mv prove-okp state) (if t (proveit term state) (mv nil state)))
           (proved1 (if prove-okp (cons term proved) proved))
           (no-ce1 (if nil (cons term no-ce) no-ce))
           (has-ce1 (if nil has-ce (cons term has-ce))))
          (mv proved1 no-ce1 has-ce1 state))))

(defmacro genM (fns size)
  `(b* ((terms (make-term-top (fn-datas ,fns state) ,size))
        ((mv proved no-ce has-ce state) (runit terms state)))
    (prog2$
     (cw "~%Given the theory of ~x0, generated ~x1 terms of size ~x5.~%~%Counterexample checking segmented them:~%plausible:~y2~%~%bad:~y3~%~%Attempting to prove ``plausible''s yields:~%~y4~%" ,fns (len terms) no-ce has-ce proved ,size)
     (mv proved state))))

 (make-termM '(equal rev2 len) 5)
 (genM '(equal rev2 len) 4)
 
 ;; (defmacro make-termM (fns size)
 ;;   `(with-output
 ;;     :stack :push
 ;;     ,:on :all
 ;;     :gag-mode ,(not t)
 ;;     (make-event
 ;;      (make-term (fns-w-arities fns state) size))))
 
 ; NOTES
 ; - we can grab type prescription of a known term with type-set, f.x.
 ;     (type-set '(integerp x) nil nil nil (ens state) (w state) nil nil nil)
 ;   gives
 ;     (135 ((LEMMA (:TYPE-PRESCRIPTION ARITY))))
 ; - can grab function guards with (guard ...)
 ; - can grab formal param names with (formals ...)
 ; - can grab function arity with (arity ...)
 ; - need to find a way to "instantiate" a subtype (look at cgen for this)
 
 ; TODO
 ; - figure out what's going on with cgen with the 3-fn gen (incl. len) vs 2-fn.
 ;   Maybe we can just get rid of cgen?
 ; - prune identical forms (up to renaming of variables)
 ; - introduce type constraints
 ;   - pull out constraints from guards
 ;   - get return types of functions and only instantiate them in holes that
 ;     correspond with the types that are expected in corresponding hole
 ;     parameters.
 ; - Need to convert to logic mode (relatively low priority)
