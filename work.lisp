(include-book "books/acl2s/cgen/top")
(include-book "books/kestrel/std/system/add-suffix-to-fn-or-const")

(ubt! 'fns-w-arities)
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

(defun fns-w-arities (fns state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (endp fns)
      nil
      (acons (car fns) (arity (car fns) (w state)) (fns-w-arities (cdr fns) state))))

;; Returns a list of numbers [1..=n]
(defun list-of-n (n)
  (declare (xargs :mode :program))
  (if (= n 1) (list 1) (cons n (list-of-n (- n 1)))))

(defun st-new (fns-w-arities nmax-vars)
  (b* ((fns (acons 'fns fns-w-arities nil))
       (cached-terms (acons 'cached-terms nil nil))
       (max-vars (acons 'max-vars nmax-vars nil)))
      (append fns cached-terms max-vars)))

(defun st-p (st)
  (declare (xargs :guard t))
  (and (symbol-alistp st)
       (assoc 'fns st)
       (assoc 'cached-terms st)
       (assoc 'max-vars st)))

(defun st-get (st key)
  (declare (xargs :mode :program :guard (st-p st) :verify-guards nil))
  (cdr (assoc key st))
  )

(defun st-all-fns (st)
  (declare (xargs :mode :program :guard (st-p st) :verify-guards nil))
  (strip-cars (cdr (assoc 'fns st))))

(defun st-fn-exists (st fn)
  (declare (xargs :mode :program :guard (st-p st) :verify-guards nil))
  (if (assoc fn (cdr (assoc 'fns st))) t nil))

(defun st-fn-arity (st fn)
  (declare (xargs :mode :program :guard (st-p st) :verify-guards nil))
  (cdr (assoc fn (cdr (assoc 'fns st)))))

(defun st-get-terms (st size)
  (declare (xargs :mode :program :guard (st-p st) :verify-guards nil))
  (cdr (assoc size (cdr (assoc 'cached-terms st)))))

(defun st-cache-terms (st size terms)
  (declare (xargs :mode :program :guard (st-p st) :verify-guards nil))
  (b* ((oldt (cdr (assoc 'cached-terms st)))
       (newt (put-assoc size terms oldt)))
      (put-assoc 'cached-terms newt st)))

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

(def-const *base-var-names*
  '(X Y Z A B C D G L K M N))

(defun fresh-name ( base avoid)
  (declare (xargs :mode :program))
  (if (member base avoid)
      (fresh-name (add-suffix-to-fn-or-const base '$) avoid)
      base))

(defun n-fresh-names (howmany avoid basis)
  (declare (xargs :mode :program))
  (if (zerop howmany)
      nil
      (cons (fresh-name (car basis) avoid) (n-fresh-names (1- howmany) avoid (cdr basis)))))

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
              (arity (st-fn-arity st fn)))
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
                             ; Create fresh variable names to fit in 1-size holes
                             ((= size 1) (mv
                                          (n-fresh-names
                                           (st-get st 'max-vars)
                                           (st-all-fns st)
                                           *base-var-names*)
                                          st))
                             ; Otherwise, fill the sized hole with a function call
                             (t (make-term--walkfns st (st-all-fns st) size)))))
        (st (st-cache-terms st size terms)))
       (mv terms st)))
 )

(defun make-term-top (fns-w-arities size)
  (declare (xargs :mode :program))
  (b* ((left (round size 2))
       (right (- size left))
       (st (st-new fns-w-arities left))
       ((mv lterms st) (make-term st left))
       ((mv rterms st) (if (= left right) (mv lterms st) (make-term st right)))
       (rewrites (reflow-heads-with-rests st lterms rterms)))
      (reflow-head-with-rests st 'EQUAL rewrites)))

(defmacro fns-w-aritiesM (fns)
  `(fns-w-arities ,fns state))

(defmacro make-termM (fns size)
  `(make-term-top (fns-w-aritiesM ,fns) ,size))

(defun proveit (term state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (b* ((toprove term)
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
  `(b* ((terms (make-term-top (fns-w-arities ,fns state) ,size))
        ((mv proved no-ce has-ce state) (runit terms state)))
    (prog2$
     (cw "~%Given the theory of ~x0, generated ~x1 terms of size ~x5.~%~%Counterexample checking segmented them:~%plausible:~y2~%~%bad:~y3~%~%Attempting to prove ``plausible''s yields:~%~y4~%" ,fns (len terms) no-ce has-ce proved ,size)
     (mv proved state))))

 (make-termM '(equal rev2 len) 4)
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
