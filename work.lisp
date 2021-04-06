; vim: foldmethod=marker
(include-book "books/acl2s/cgen/top")
(include-book "books/kestrel/std/system/add-suffix-to-fn-or-const")
(include-book "books/std/util/defprojection")
(include-book "books/std/util/defmapappend")

(ubt! 'fndata-p)
; (acl2s-defaults :set verbosity-level 4)

(defun rev2 (x)
  (declare (xargs :guard (true-listp x) :VERIFY-GUARDS NIL))
  (if (consp x)
      (append (rev2 (cdr x)) (list (car x)))
      nil))

; (test? (equal (rev (rev x)) x))

(defun getvars (form state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (declare (ignorable state))
  (cw  "~|vars: ~x0~|" (all-vars form))
  )

; (defmacro getvarsM (form &rest kwd-val-lst)
;   (let* ((vl-entry (assoc-keyword :verbosity-level kwd-val-lst))
;          (vl (and vl-entry (cadr vl-entry)))
;          (debug (and (natp vl) (cgen::debug-flag vl))))
;         `(with-output
;           :stack :push
;           ,(if debug :on :off) :all
;           :gag-mode ,(not debug)
;           (make-event
;            (getvars ',form state)))))

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
  ; (declare (xargs :guard (fndata-p fn-data) :verify-guards nil))
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
            res
            ))
  )

(defun reflow-heads-with-rests (st heads rests)
  (declare (xargs :mode :program))
  (if (endp heads)
      nil
      (let* ((res (append (reflow-head-with-rests st (car heads) rests) (reflow-heads-with-rests st (cdr heads) rests))))
            res
            )))

(defun enlist (lst)
  (declare (xargs :mode :program))
  (if (endp lst)
      nil
      (cons (list (car lst)) (enlist (cdr lst)))))

(defconst *GEN-HOLE* '_HOLE_)

(defun fresh-name (base avoid)
  (declare (xargs :mode :program))
  (if (member base avoid)
      (fresh-name (add-suffix-to-fn-or-const base '$) avoid)
      base))

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
                   (mv (append insts-for-headsize allrest) st)
                   ))))))
 
 ;; Creates a list of sequences of terms, list(S), where the number of terms in
 ;; S is equal to "num-terms" and the sum of their sizes is equal to "size".
 ;; This is just a permutation over the ways to arrange "num-terms" terms in a
 ;; sequence s.t. their sizes respect the invariant sum "size".
 (defun make-term--seq-permute-over-size (st num-terms size)
   (declare (xargs :mode :program ))
   (cond
    ((zerop num-terms) (mv nil st))
    (t (b* ((num-tail-terms (- num-terms 1))
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
                 (b* (((mv seqs st) (make-term--seq-permute-over-size st arity (- size 1)))
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
 )

(define holed-terms-of-sizes ((st st-p) ns)
  :mode :program
  (if (endp ns)
      (mv nil st)
      (b* (((mv rst st) (holed-terms-of-sizes st (cdr ns)))
           ((mv cur st) (make-term st (car ns))))
          (mv (append cur rst) st))))

; }}}

;;;;; VARIABLE COLLECTION {{{

;; Collects the variables present in a term.
(define collect-vars ((st st-p) (term pseudo-termp))
  :mode :program
  (if (listp term)
      (if (endp term)
          nil
          (append (collect-vars st (car term)) (collect-vars st (cdr term))))
      
      (if (st-fn-exists st term)
          nil
          (list term))))

; }}}

(defconst *empty-vars-store*
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
           ; Either a list where the first term is a hole,
           ; or an atom that is a hole.
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
                ((mv tails vs) (if (listp term) (reify-term st (cdr term) vs) (mv nil vs))))
               (if (listp term)
                   (mv (reflow-heads-with-rests st possible-vars tails) vs)
                   (mv possible-vars vs))))
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

;; Given an lterm and a set of corresponding rterms, produces a list of lrpairs
;; (l, r)\forall r\in rterms\setminus\{l\}
(define pair-each ((lterm pseudo-termp) (rterms pseudo-term-listp))
  :mode :program
  (cond ((endp rterms) nil)
        ((equal lterm (caar rterms)) (pair-each lterm (cdr rterms)))
        (t (cons (cons lterm (car rterms)) (pair-each lterm (cdr rterms))))))

(define reify-holed-rterms--inner ((st st-p) (vs listp) (lterm pseudo-termp) (rterms listp))
  :mode :program
  (if (endp rterms)
      nil
      (b* (((mv reified-rterms ?) (reify-term st (car rterms) vs))
           (lrterms (pair-each lterm (enlist reified-rterms))))
          (append lrterms (reify-holed-rterms--inner st vs lterm (cdr rterms))))))

(define reify-holed-rterms ((st st-p) (lterm pseudo-termp) (rterms listp))
  :mode :program
  (b* ((lvars (remove-duplicates-equal (collect-vars st lterm)))
       (vs (frozen-vars-store lvars)))
      (reify-holed-rterms--inner st vs lterm rterms)))

(std::defmapappend pair-lterms-holed-rterms (st x holed-rterms)
                   :mode :program
                   :guard (and (st-p st) (pseudo-termp x) (listp holed-rterms))
                   (reify-holed-rterms st x holed-rterms))
;}}}

;;;;; TERM REPR {{{

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

(define pack-lrconj (l r hyps) (list l r hyps))
(define unpack-lrconj ((lrconj lrconjp)) :mode :program (mv (car lrconj) (cadr lrconj) (caddr lrconj)))

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
    (b* ((subst-term (or (aget (car term) substs)
                         (apply-substs (car term) substs))))
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

(define normalize-hyps ((hyps pseudo-term-listp))
  :mode :program
  (b* ((hyps (remove-duplicates-equal hyps))
       (hyps (remove-equal ''T  hyps)))
      hyps))

;; Given an lrpair '(l r) returns an lrconj '(l r hyps) with the hypotheses
;; absorbed from l and r in hyps.
(define lrterm-hypothesize ((st st-p) (lrpair lrpairp))
  :mode :program
  ; :returns (lrconjp conj)
  (b* ((hyps (append (extract-hyps-from-term st (car lrpair))
                     (extract-hyps-from-term st (cadr lrpair))))
       (hyps (normalize-hyps hyps)))
      (append lrpair (list hyps))))

(std::defprojection lrterm2conj-list ((st st-p) (x listp))
                    :mode :program
                    (lrterm-hypothesize st x))

;}}}

;;;;; THEOREM CREATION {{{

;; Folds an lrconj (left right hyps) into a proper theorem
;; (IMPLIES ,hyps (EQUAL ,left ,right))
(define thm-of-lrconj ((lrconj lrconjp))
  :mode :program
  (if (caddr lrconj)
      `(IMPLIES
        ,(cons 'AND (caddr lrconj))
        (EQUAL ,(car lrconj) ,(cadr lrconj)))
      `(EQUAL ,(car lrconj) ,(cadr lrconj))
      ))

(std::defprojection thm-of-lrconj-list (x)
                    :mode :program
                    (thm-of-lrconj x))


;; Given a list of LR conjectures, put them in a form a user would want to see,
;; since originally we generated these somewhat haphazardly.
(define pretty-thms-of-lrconj-list (lrconjs state)
  :mode :program
  :stobjs state
  (if (endp lrconjs)
      (mv nil state)
      (b* (((mv rst state) (pretty-thms-of-lrconj-list (cdr lrconjs) state))
           ((mv ? desugared state) (acl2::translate (thm-of-lrconj (car lrconjs)) t nil t "thm..." (w state) state))
           (sugared (acl2::untranslate desugared t (w state))))
          (mv (cons sugared rst) state))))

;}}}

;;;;; THM PROVING {{{

(defun tryprove (term st state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (b* (; Enable all functions in the proof attempt
       (allfns (st-all-fns st))
       (hints (append
               `(("Goal" :in-theory ,(cons 'enable allfns)))
               (acl2::default-hints (w state))))
       ((mv ? hints state) (acl2::translate-hints "Goal" hints "Goal" (w state) state))
       ; ((mv ? hints state) (acl2::translate hints t nil t "hints..." (w state) state))
       ; TODO capture + handle error
       ((mv ? toprove state) (acl2::translate term t nil t "thm..." (w state) state))
       ((mv erp trval state) (acl2::state-global-let*
                              ((acl2::inhibit-output-lst *valid-output-names*)
                               (acl2::print-clause-ids nil)
                               )
                              (acl2::prove toprove (acl2::make-pspv (acl2::ens state) (w state) state) hints (acl2::ens state) (w state) "thm..." state)))
       ((mv ? prove-okp state) (mv erp (if erp (cadr trval) t) state))
       )
      (mv prove-okp state)
      ))

; }}}

;;;;; THM PRUNING {{{

; Returns whether a type hypothesis `hyp` is unsatisfiable. For example,
; "(LISTP (LEN A))" is never satisfiable, regardless of the value of `A`. Given
; a term "(TYPEP X)", we determine what the type set of `X` must be supposing
; "(TYPEP X)" is true. If the type set is empty, the hypothesis is never
; satisfiable.
; (define is-type-hypothesis-unsat ((hyp pseudo-termp) state)
;   :mode :program
;   :stobjs state
;   (b* (((mv ts ?ttree) (acl2::type-set-implied-by-term (cadr hyp) nil hyp (acl2::ens state) (acl2::w state) nil)))
;       (= acl2::*ts-empty* ts)))
;
; ; Heuristic to determine is a term is a type hypothesis
; (define type-hypothesisp ((term pseudo-termp))
;   :mode :program
;   (and (pseudo-termp term)
;        (= 2 (len term))
;        (symbolp (car term))
;        (eql #\P (char (reverse (string (car term))) 0))))
;
; (define is-hypothesis-unsat1 ((hyp pseudo-termp) state isfirst)
;   :mode :program
;   :stobjs state
;   (if (atom hyp)
;     nil
;     (b* ((is-unsat (if isfirst
;                      (and (type-hypothesisp hyp) (is-type-hypothesis-unsat hyp state))
;                      nil)))
;         (or is-unsat
;             ; check current subterm we're at, in case it's nested
;             (is-hypothesis-unsat1 (car hyp) state t)
;             ; check the rest of the term
;             (is-hypothesis-unsat1 (cdr hyp) state nil))
;         )))

; Determines if a variable is unsatisfiable in a hypothesis via its type set.
; A variable is unsatisfiable if its deduced type set is empty.
(define is-var-ty-unsat-in-hypothesis ((var symbolp) (hyp pseudo-termp) state)
  :mode :program :stobjs state
  (b* (((mv ts ?ttree) (acl2::type-set-implied-by-term var nil hyp (acl2::ens state) (acl2::w state) nil)))
      (= acl2::*ts-empty* ts)))

; Determines if any variables in a hypothesis are unsatisfiable by way of their
; type sets being empty.
(define any-vars-ty-unsat-in-hypothesis ((vars symbol-listp) (hypothesis pseudo-termp) state)
  :mode :program :stobjs state
  (and (consp vars)
       (or (is-var-ty-unsat-in-hypothesis (car vars) hypothesis state)
           (any-vars-ty-unsat-in-hypothesis (cdr vars) hypothesis state))))

; Determines whether it can be proved that a hypothesis is unsatisfiable.
; If -A is valid, it must be the case that A is unsatisfiable. That is the
; approach we take here.
(define is-hyp-provable-unsatisfiable ((hypothesis pseudo-termp) st state)
  :mode :program :stobjs state
  (b* (((mv unsatp state) (tryprove `(NOT ,hypothesis) st state)))
      (mv unsatp state)))

(define hypothesis-unsatisfiable ((hypothesis pseudo-termp) (vars symbol-listp) st state)
  :mode :program :stobjs state
  (if (any-vars-ty-unsat-in-hypothesis vars hypothesis state) (mv t state)
      (is-hyp-provable-unsatisfiable hypothesis st state)))

; A heuristic to decide whether this theorem should be pruned from inclusion as
; a desirable lemma to include in the theory. The reasons for this include
;   - Unsatisfiable hypotheses, making the theorem vacuous
;   - TODO: "trivial" conclusion - what does this mean?
(define should-prune-thm ((thm lrconjp) (st st-p) state)
  :mode :program
  :stobjs state
  (b* (((mv l ?r hyps) (unpack-lrconj thm))
       ((mv ? hypothesis state) (acl2::translate (cons 'AND hyps) t nil t "thm..." (w state) state))
       (vars (collect-vars st l))
       ((mv should-prune state)
        (cond
         ((zerop (len hyps)) (mv nil state))
         (t (hypothesis-unsatisfiable hypothesis vars st state)))))
      (mv should-prune state)))

(define prune-thms (thms (st st-p) state)
  :mode :program
  :stobjs state
  (if (endp thms)
      (mv nil state)
      (b* (((mv pruneit state) (should-prune-thm (car thms) st state))
           ((mv keepthms state) (prune-thms (cdr thms) st state)))
          (if pruneit
              (mv keepthms state)
              (mv (cons (car thms) keepthms) state)))))

; Prunes theorems in an attempt to satisfy intuitions about what "nice" theorems
; look like on the front-end.
; For example, the theorem
;   (EQUAL (BINARY-APPEND A (BINARY-APPEND A A) (BINARY-APPEND (BINARY-APPEND A A) A))
; may be useful and "go somewhere", but its front-end sugaring is
;   (EQUAL (APPEND A A A) (APPEND (APPEND A A) A))
; which is not a very nice-appearing theorem, as the LHS is smaller than the
; RHS. Indeed, intuition would suggest this theorem would not be useful. To this
; end, we elide those theorems where the left hand side is not well-pre-ordered
; relative to the right hand side.
;
; References:
;   https://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/index-seo.php/ACL2____TERM-ORDER)
(define posterior-prune-thms (thms state)
  :mode :program :stobjs state
  (if (endp thms)
      nil
      (b* ((keepthms (posterior-prune-thms (cdr thms) state))
           ((mv l r ?hyps) (unpack-lrconj (car thms)))
           (lsugared (acl2::untranslate l t (w state)))
           (rsugared (acl2::untranslate r t (w state)))
           (well-orderedp (term-order lsugared rsugared))
           (pruneit (and well-orderedp)))
          (if pruneit
              keepthms
              (cons (car thms) keepthms)))))

; }}}

;;;;; HYPOTHESIS PRUNING {{{

(mutual-recursion
 (defun tryprove-pruning-hyps (l r incl-hyps rest-hyps st state)
   (declare (xargs :mode :program :stobjs state))
   (if (endp rest-hyps)
       (mv nil nil state)
       (b* (((mv other-provedp best-other state) (tryprove-pruning-hyps l r (append incl-hyps (list (car rest-hyps))) (cdr rest-hyps) st state))
            (cand-hyps (append incl-hyps (cdr rest-hyps)))
            ((mv cand-provedp best-from-cand-hyps state) (tryprove-simplest-conj l r cand-hyps st state)))
           (cond
            ((and cand-provedp other-provedp)
             (mv t (if (< (len best-other) (len best-from-cand-hyps)) best-other best-from-cand-hyps) state))
            (cand-provedp (mv t best-from-cand-hyps state))
            (other-provedp (mv t best-other state))
            (t (mv nil nil state)))
           )
       ))
 
 (defun tryprove-simplest-conj (l r hyps st state)
   (declare (xargs :mode :program :stobjs state))
   (b* (((mv provedp state) (tryprove (thm-of-lrconj (pack-lrconj l r hyps)) st state)))
       (if (not provedp)
           (mv nil nil state)
           ; We were able to prove the conjecture. Can we prove it with less hypotheses?
           (b* (((mv provedwithless-p less-hyps state) (tryprove-pruning-hyps l r nil hyps st state)))
               (if provedwithless-p
                   (mv t less-hyps state) ; yes!
                   (mv t hyps state)) ; no, just use what we started with
               )
           )))
 )

(define tryprove-simplest-conj-top ((lrconj lrconjp) st state)
  :mode :program
  :stobjs state
  (b* (((mv l r hyps) (unpack-lrconj lrconj))
       ((mv provedp besthyps state) (tryprove-simplest-conj l r hyps st state))
       (conj (pack-lrconj l r besthyps)))
      (mv provedp conj state)))

;}}}

;;;;; MAIN DRIVERS

(defun make-rw-conjectures (st left right)
  (declare (xargs :mode :program))
  (b* (
       ; Create holed terms
       ((mv lterms-holed st) (make-term st left))
       ((mv rterms-holed st) (holed-terms-of-sizes st (list-of-n right)))
       ; Instantiate lterms with concrete vars
       (lterms (reify-term-list st lterms-holed))
       ; For each lterm, instantiate one of each rterm with concrete
       ; variables from the set of variables in the lterm. Now we have pairs
       ; of concrete terms (left, right) to be used in a theorem.
       (lr-pairs (pair-lterms-holed-rterms st lterms rterms-holed))
       ; For each lrpair, generate a lrconj with hypotheses collected from
       ; the l/r terms.
       (lr-conjs (lrterm2conj-list st lr-pairs)))
      lr-conjs))

(defmacro fn-dataM (fns)
  `(fn-datas ,fns state))

(defmacro single-termM (fns size)
  `(make-term (fn-dataM ,fns) ,size))

(defmacro make-termM (fns left right)
  `(make-rw-conjectures (st-new (fn-dataM ,fns) ,left) ,left ,right))

(defconst *cgen-opts* (acons 'verbosity-level 0 nil))

(define ce-thms (terms state)
  :stobjs state
  :mode :program
  (if (endp terms) (mv nil state)
      (b* (((mv rst state) (ce-thms (cdr terms) state))
           ((mv cts-found? ? state) (acl2s::test?-fn (thm-of-lrconj (car terms)) nil *cgen-opts* state)))
          (mv (if cts-found? rst (cons (car terms) rst)) state)
          )))

(defun validate-conjs (terms st state cnt total)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (if (endp terms) (mv nil state)
      (b* ((conj (car terms))
           ((mv proved-list state) (validate-conjs (cdr terms) st state (1+ cnt) total))
           ((mv provedp proved-conj state) (tryprove-simplest-conj-top conj st state))
           (proved-list1 (if provedp (cons proved-conj proved-list) proved-list)))
          (prog2$ (if (= 0 (mod (- total cnt) 10))
                      (cw "~s2~x0/~x1..." (- total cnt) total (coerce '(#\return) 'string)) nil)
                  (mv proved-list1 state)))))

(defmacro genM (fns left-size &rest opts)
  `(b* ((show-useful-conjs (aget 'show-useful-conjectures ,opts))
        (st (st-new (fn-datas ,fns state) ,left-size))
        (conjs (make-rw-conjectures st ,left-size ,left-size))
        ((mv useful-conjs state) (prune-thms conjs st state))
        (num-useful (length useful-conjs))
        ((mv plausible-conjs state) (ce-thms useful-conjs state))
        (num-plausible (length plausible-conjs))
        ((mv proved-thms state) (prog2$ (cw "~%Validating ~x0 conjectures...~%" num-plausible)
                                        (validate-conjs plausible-conjs st state 0 num-plausible)))
        (num-proved (len proved-thms))
        (nice-thms (posterior-prune-thms proved-thms state))
        (num-nice (len nice-thms))
        ((mv final-thms-pretty state) (pretty-thms-of-lrconj-list nice-thms state)))
    (prog2$
     (prog2$ (cw "~%====================~%\
Given the theory ~x0,\
we generated ~x1 conjectures of size left=~x2, right<=~x2.\
Of those, we deemed ~x3 useful.\
Of those, we were unable to find counterexamples for ~x4~s5~%"
                 ,fns (length conjs) ,left-size num-useful num-plausible
                 (if show-useful-conjs (fms-to-string ", namely:~%~y0" (list (cons #\0 (thm-of-lrconj-list plausible-conjs)))) "."))
             (if (zerop num-proved)
                 (cw "~%Unfortunately, we failed to prove any of them true.~%")
                 (cw "We were able to prove ~x0. ~x1 of those appear nice, namely:~%~y2~%"
                     num-proved num-nice final-thms-pretty)))
     (mv num-proved state))))

(defmacro translate** (term)
  `(acl2::translate ,term t nil t "thm..." (w state) state))

(defmacro prove** (term)
  `(b* (((mv ? hints state) (acl2::translate-hints "" (acl2::default-hints (w state)) nil (w state) state)))
    (acl2::prove ,term (acl2::make-pspv (acl2::ens state) (w state) state) hints (acl2::ens state) (w state) "thm..." state)
    ))

(defmacro tyinfer** (var term)
  `(type-set-implied-by-term ,var nil ,term (ens state) (w state) nil))

(make-termM '(equal rev2 len) 3 3)
(genM '(reverse len) 3
      acons 'show-useful-conjectures t nil)

;; (defthm my-len-of-rev (IMPLIES (AND (IF (TRUE-LISTP A)
;;                                         (TRUE-LISTP A)
;;                                         (STRINGP A)))
;;                                (EQUAL (LEN (REVERSE A)) (LEN A))))

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
; - How can we better deal with the hypotheses we are introducing?
;   So far:
;   D pull out function guards as hyps
;   What else can we do?
;   - "generate" hypotheses
;     - this seems futile - where would we generate them from
;   - perhaps, pull out failed subgoals as new, additional hypotheses for the
;     conjecture
; - Hypothesis pruning
;   D when a theorem is proven, attempt to remove hypotheses so long as we have
;     that the theorem continues to hold
; - Theorem pruning
;   D Remove theorems whose hypotheses are unsatisfiable via their types
;   - Remove theorems whose hypotheses are unsatisfiable in general - via
;     SMTlink?
; TODO backburner
; * figure out what's going on with cgen with the 3-fn gen (incl. len) vs 2-fn.
;   Maybe we can just get rid of cgen?
;   - Resolution: not using cgen at all for now
; * Need to convert to logic mode (relatively low priority)
