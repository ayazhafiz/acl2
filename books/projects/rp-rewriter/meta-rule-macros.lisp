; RP-REWRITER

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Mertcan Temel         <mert@utexas.edu>

(in-package "RP")

(include-book "rp-rewriter")
(include-book "extract-formula")
(include-book "eval-functions")
(include-book "cl-correct")
(include-book "tools/templates" :dir :system)
(include-book "std/strings/decimal" :dir :system)

;(include-book "def-formula-checks")

;; (table-alist 'rp-rw-meta-rules (w state)) has meta rules with formal checks
;; that merge as books are added.

;; (cdr (assoc-equal 'formal-checks-fn-list (table-alist 'rp-rw (w state))))
;; this only has the name of meta checks functions that cannot be merged by
;; sepearet books and is updated succesfully when a new clause processor is
;; generated.



;; (defun create-rp-clause-proc (cl-name-prefix appended-meta-rules)
;;   (list
;;    `(defun ,(sa cl-name-prefix "RP-CLAUSE-PROCESSOR") (cl hints rp-state state)
;;       (declare
;;        (xargs :stobjs (rp-state state)
;;               :guard t
;;               :guard-hints (("goal"
;;                              :in-theory (e/d (rp-meta-valid-syntax-listp)
;;                                              (rp-meta-valid-syntaxp-sk))))
;;               :verify-guards nil))
;;       (if (rp-cl-hints-p hints)
;;           (rp-clause-processor-aux
;;            cl hints
;;            ,appended-meta-rules
;;            rp-state
;;            state)
;;         (mv nil (list cl) rp-state state)))

;;    `(defthm ,(sa 'correctness-of-rp-clause-processor cl-name-prefix)
;;       (implies
;;        (and
;;         (pseudo-term-listp cl)
;;         (alistp a)
;;         (rp-evl-meta-extract-global-facts :state state)
;;         (rp-evl (acl2::conjoin-clauses
;;                  (acl2::clauses-result
;;                   (,(sa cl-name-prefix "RP-CLAUSE-PROCESSOR") cl hint rp-state state)))
;;                 a))
;;        (rp-evl (acl2::disjoin cl) a))
;;       :otf-flg t
;;       :hints (("Goal"
;;                :in-theory (e/d (correctness-of-rp-clause-processor-aux
;;                                 valid-rp-meta-rule-listp
;;                                 rp-meta-valid-syntax-listp)
;;                                (rp-clause-processor-aux
;;                                 valid-rp-meta-rulep
;;                                 rp-meta-valid-syntaxp-sk
;;                                 acl2::conjoin-clauses
;;                                 acl2::clauses-result))))
;;       :rule-classes :clause-processor)))

(defun make-appended-meta-rules (rp-rw-meta-rules-with-fc)
  (if (atom rp-rw-meta-rules-with-fc)
      nil
    `(append (and (,(caar rp-rw-meta-rules-with-fc) state)
                  ',(cdar rp-rw-meta-rules-with-fc))
             ,(make-appended-meta-rules (cdr rp-rw-meta-rules-with-fc)))))

(progn
  (defun make-appended-meta-rules2-aux1 (rp-rw-meta-rules-with-fc)
    (if (atom rp-rw-meta-rules-with-fc)
        nil
      (cons `',(cdar rp-rw-meta-rules-with-fc)
            (make-appended-meta-rules2-aux1 (cdr rp-rw-meta-rules-with-fc)))))

  (defun make-appended-meta-rules2-aux2 (rp-rw-meta-rules-with-fc)
    (if (atom rp-rw-meta-rules-with-fc)
        nil
      (cons `(,(caar rp-rw-meta-rules-with-fc) state)
            (make-appended-meta-rules2-aux2 (cdr rp-rw-meta-rules-with-fc)))))

  (defun make-appended-meta-rules2 (rp-rw-meta-rules-with-fc)
    `(if (and . ,(make-appended-meta-rules2-aux2 rp-rw-meta-rules-with-fc))
         (append . ,(make-appended-meta-rules2-aux1 rp-rw-meta-rules-with-fc))
       nil)))

(defun append-entries (alist)
  (if (atom alist)
      nil
    (append (cdar alist)
            (append-entries (cdr alist)))))

;; (defmacro update-rp-clause-proc (cl-name-prefix)
;;   `(make-event
;;     (b* ((all-rp-rw-meta-rules (table-alist 'rp-rw-meta-rules (w state)))
;;          (appended-meta-rules (make-appended-meta-rules2
;;                                all-rp-rw-meta-rules))
;;          (meta-rules-list (append-entries all-rp-rw-meta-rules))
;;          (cl-name-prefix ',cl-name-prefix))
;;       `(encapsulate
;;          nil
;;          (local
;;           (in-theory (disable (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND)
;;                               (:e tau-system)
;;                               (:TYPE-PRESCRIPTION RP-CLAUSE-PROCESSOR-AUX)
;;                               (:TYPE-PRESCRIPTION BINARY-APPEND)
;;                               (:DEFINITION PSEUDO-TERM-LISTP)
;;                               (:TYPE-PRESCRIPTION RP-CLAUSE-PROCESSOR-AUX)
;;                               (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP)
;;                               (:TYPE-PRESCRIPTION ALISTP))))
;;          (table rp-rw 'cl-name-prefix ',cl-name-prefix)
;;          (table rp-rw 'meta-rules ',appended-meta-rules)
;;          (table rp-rw 'meta-rules-list ',meta-rules-list)
;;          (table rp-rw 'formal-checks-fn-list ',(strip-cars all-rp-rw-meta-rules))
;;          ,@(create-rp-clause-proc cl-name-prefix appended-meta-rules)))))

(xdoc::defxdoc
 attach-meta-fncs
 :parents (rp-rewriter/meta-rules)
 :short "Creates and attaches a new meta-rule caller function to register added meta rules."
 :long "<p>
After calling @(see add-meta-rules) or when different books with meta rules are
 included, users need to call attach-meta-fncs. This creates a
 new meta function caller function and attaches it to rp::rp-rw-meta-rule. </p>
<code>(rp::attach unique-prefix)</code>
<p> unique-prefix should be a unique name that will be a prefix to the name
 of the new  meta-rule caller function. </p>
")

(defun add-meta-rules-fn-aux (formula-checks-fn new-meta-rules  hints)
  (declare (xargs :guard (weak-rp-meta-rule-recs-p new-meta-rules)))
  (if (atom new-meta-rules)
      nil
    (cons
     `(local
       (in-theory (disable ,(rp-meta-fnc (car new-meta-rules)))))
     (cons
      (b* ((cur (car new-meta-rules))
           (dont-rw (rp-meta-dont-rw cur))
           (syntax (rp-meta-syntax-verified cur))
           (trig-fnc (rp-meta-trig-fnc cur))
           (fnc (rp-meta-fnc cur))
           (outside-in (rp-meta-outside-in cur))
           (rune `(:meta ,fnc . ,trig-fnc)))
        `(progn
           (table rp-rules ',rune
                  ',(cond
                     ((equal outside-in ':both) `(:both . t))
                     (outside-in `(:outside-in . t))
                     (t `(:inside-out . t))))
           (defthm ,(sa fnc 'for trig-fnc 'valid)
             (and (implies (and (,formula-checks-fn state)
                                (rp-evl-meta-extract-global-facts)
                                (rp-termp term)
                                (valid-sc term a))
                           (and (equal (rp-evlt
                                        ,(if dont-rw `(mv-nth 0 (,fnc term)) `(,fnc
                                                                               term))
                                        a)
                                       (rp-evlt term a))
                                (valid-sc ,(if dont-rw `(mv-nth 0 (,fnc term)) `(,fnc
                                                                                 term))
                                          a
                                          )))
                  ,@(append (and dont-rw
                                 `((dont-rw-syntaxp (mv-nth 1 (,fnc term)))))
                            (and syntax
                                 `((implies (rp-termp term)
                                            (rp-termp ,(if dont-rw `(mv-nth 0 (,fnc term)) `(,fnc
                                                                                             term))))))))
             :hints ,hints)))
      (add-meta-rules-fn-aux formula-checks-fn (cdr new-meta-rules)  hints)))))

(defun add-meta-rules-fn (formula-checks-fn new-meta-rules cl-name-prefix
                                            hints)
  (declare (ignorable hints cl-name-prefix))
  `(make-event
    (b* ((?talist (table-alist 'rp-rw (w state)))
         (?added-meta-rules (cdr (assoc-equal 'meta-rules talist)))
         (?added-meta-rules-list (cdr (assoc-equal 'meta-rules-list talist)))
         (?added-meta-formal-checks-fn-list (cdr (assoc-equal 'formal-checks-fn-list talist)))
         (formula-checks-fn ',formula-checks-fn)
         ;;(?cl-name-prefix ',cl-name-prefix)
         (?new-meta-rules ',new-meta-rules))

      `(encapsulate
         nil

         (in-theory (disable ,formula-checks-fn
                             (:type-prescription ,formula-checks-fn)))

;(value-triple (cw  "Disabled for

         (table rp-rw-meta-rules
                ',formula-checks-fn
                ',new-meta-rules)

         (progn ,@(add-meta-rules-fn-aux formula-checks-fn new-meta-rules ',hints))

         ;; ,@(if ',cl-name-prefix
         ;;       `(;(update-rp-clause-proc ,cl-name-prefix)
         ;;         #|(table rp-rw 'cl-name-prefix ',cl-name-prefix)

         ;;         (table rp-rw 'meta-rules `(append
         ;;         (and (,',formal-checks-fn state)
         ;;         ',',new-meta-rules)
         ;;         ,',added-meta-rules))

         ;;         (table rp-rw 'meta-rules-list (append
         ;;         ',new-meta-rules
         ;;         ',added-meta-rules-list))

         ;;         (table rp-rw 'formal-checks-fn-list (cons
         ;;         ',formal-checks-fn
         ;;         ',added-meta-formal-checks-fn-list))

         ;;         ,@(create-rp-clause-proc cl-name-prefix `(append
         ;;         (and (,formal-checks-fn state)
         ;;         ',new-meta-rules)
         ;;         ,added-meta-rules))||#)
         ;;     nil)

         ))))

(defmacro add-meta-rules (formula-checks-fn new-meta-rules
                                            &key hints cl-name-prefix)
  `(make-event
    (add-meta-rules-fn ',formula-checks-fn ,new-meta-rules ',cl-name-prefix ',hints)))

(xdoc::defxdoc
 add-meta-rules
 :parents (rp-rewriter/meta-rules)
 :short "A macro to add created meta rules to RP-Rewriter"
 :long "<p>
<code> (add-meta-rules formal-checks-fn new-meta-rules) </code>

OR

<code> (add-meta-rules formal-checks-fn new-meta-rules cl-name-prefix) </code>

submits an event that saves previously proved meta-rules in rp-rewriter's
rule-set for meta rules.
</p>

<p> formal-checks-fn: it is the name of the formula-checks function created
with def-formula-checks </p>

<p> new-meta-rules: a list of constructs created with defrec struct
rp-meta-rule-rec. It can have one or more meta-rules that are proved with the
same formula-checks function.  For example: <code>
(list
  (make rp-meta-rule-rec
        :fnc 'rp-equal-meta
        :trig-fnc 'equal
        :dont-rw t
        :valid-syntax t))
</code>
</p>

<p>cl-name-prefix: An optional argument. When non-nil, the macro also calls
@(see rp::attach-meta-fncs) to create a new clause processor function for
RP-Rewriter. </p>
"
 )


(defun create-rp-rw-meta-rule-fn-aux (meta-rules)
 (if (atom meta-rules)
     `((t (mv term nil )))
   (b* ((m (car meta-rules))
        (fnc (rp-meta-fnc m))
        (?trig-fnc (rp-meta-trig-fnc m))
        (dont-rw (rp-meta-dont-rw m))
        (syntax (rp-meta-syntax-verified m)))
     (cons
      `((eq ',fnc meta-fnc-name)
        ,(if dont-rw
             `(b* (((mv res-term dont-rw)
                    (,fnc term))
                   . ,(if syntax
                          nil
                        `((res-term
                           (if (rp-termp res-term)
                               res-term
                             (progn$ (cw "Meta-function ~p0 returned a term that does not satisfy rp::rp-termp" ',fnc)
                                     term))))))
                (mv res-term dont-rw ))
           `(b* ((res-term
                  (,fnc term))
                 . ,(if syntax
                        nil
                      `((res-term
                         (if (rp-termp res-term)
                             res-term
                           (progn$ (cw "Meta-function ~p0 returned a term that does not satisfy rp::rp-termp" ',fnc)
                                   term))))))
              (mv res-term nil ))))
      (create-rp-rw-meta-rule-fn-aux (cdr meta-rules))))))


(defun get-meta-rule-validity-lemma (meta-rules)
  (declare (xargs :guard (weak-rp-meta-rule-recs-p meta-rules))) 
  (if (atom meta-rules)
      nil
    (cons (sa (rp-meta-fnc (car meta-rules)) 'for
              (rp-meta-trig-fnc (car meta-rules))
              'valid)
          (get-meta-rule-validity-lemma (cdr meta-rules)))))

(defun create-rp-rw-meta-rule-fn (prefix world)
  (b* ((fnc-name (sa prefix 'rp-rw-meta-rule))
       (formula-checks-fnc-name (sa prefix 'rp-formula-checks))
       (meta-rules (get-meta-rules (table-alist 'rp-rw-meta-rules world)))
       (formula-checks-fns (strip-cars (table-alist 'rp-rw-meta-rules world)))
       (meta-rule-validity-lemmas (get-meta-rule-validity-lemma meta-rules))
       (formula-checks-fn-body
        (cons 'and (pairlis$ formula-checks-fns (pairlis$ (repeat (len formula-checks-fns) 'state) nil)))))
    `(encapsulate
       nil
       
       (defun ,formula-checks-fnc-name (state)
         (declare (xargs :stobjs (state)))
         ,formula-checks-fn-body)
       
       (defun ,fnc-name (term meta-fnc-name )
         (declare (xargs :guard (rp-termp term)))
         (declare (ignorable term meta-fnc-name))
         (cond
          ,@(create-rp-rw-meta-rule-fn-aux meta-rules)))

       (local
        (in-theory (theory 'minimal-theory)))
       
       (defattach
         (rp-formula-checks ,formula-checks-fnc-name)
         (rp-rw-meta-rule ,fnc-name)
         :hints (("Goal"
                  :in-theory (e/d (,formula-checks-fnc-name
                                   ,fnc-name
                                   ,@meta-rule-validity-lemmas
                                   (:e dont-rw-syntaxp))
                                  ())))
         ))))




(defun attach-meta-fncs-fn (prefix state)
  (declare (xargs :stobjs (state)
                  :verify-guards nil))
  (b* ((world (w state))
       (rp-rw-meta-rules-with-fc (table-alist 'rp-rw-meta-rules world))
       (meta-rules (get-meta-rules rp-rw-meta-rules-with-fc))
       ;(simple-meta-rules-list (create-simple-meta-rules-alist meta-rules))
       #|(appended-meta-rules (make-appended-meta-rules2
       all-rp-rw-meta-rules))||#
       ;;(meta-rules-list (append-entries rp-rw-meta-rules-with-fc))
       )
    `(progn
       #|(table rp-rw 'meta-rules ',appended-meta-rules)||#
       (table rp-rw 'meta-rules-list ',meta-rules)
       ;(table rp-rw 'simple-meta-rules-alist ',simple-meta-rules-list)
       (table rp-rw 'formal-checks-fn-list ',(strip-cars rp-rw-meta-rules-with-fc))
       ,(create-rp-rw-meta-rule-fn prefix world))))
       
       
(defmacro attach-meta-fncs (prefix)
  `(make-event
    (attach-meta-fncs-fn ',prefix state)))

(defun is-rp-clause-processor-up-to-date (world)
  (declare (xargs :guard (and (PLIST-WORLDP world))
                  :guard-hints (("Goal"
                                 :in-theory (e/d (hons-assoc-equal
                                                  acl2::plist-worldp-with-formals)
                                                 ())))))
  (b* ((rp-rw-meta-rules-with-fc (table-alist 'rp-rw-meta-rules world))
       (added-meta-formal-checks-fn-list (cdr (hons-assoc-equal
                                               'formal-checks-fn-list
                                               (table-alist 'rp-rw world)))))
    (equal (len rp-rw-meta-rules-with-fc)
           (len added-meta-formal-checks-fn-list))))

(xdoc::defxdoc
 is-rp-clause-processor-up-to-date
 :parents (rp-rewriter/meta-rules)
 :short "Checks if all the added meta-rules are 'registered'"
 :long "<p>
After calling @(see add-meta-rules) or when different books with meta rules are
 included, users need to call @(see rp::attach-meta-fncs). This function
 checks if it is necessary. </p>
<code>(is-rp-clause-processor-up-to-date world)</code>
")


(define check-if-clause-processor-up-to-date (world)
  (declare (xargs :guard (and (PLIST-WORLDP world))
                  :guard-hints (("Goal"
                                 :in-theory (e/d (assoc-equal
                                                  ACL2::PLIST-WORLDP-WITH-FORMALS) ())))))
  (if (is-rp-clause-processor-up-to-date world)
      nil
    (hard-error 'defthmrp
                "The clause processor function is NOT up-to-date with respect
  to added meta rules. Run (update-rp-clause-proc cl-name-suffix) to create the
  updated clause processor. cl-name-suffix should be a unique nickname for the
  updated clause processor function. ~%"
                nil)))

(progn
  (defthm valid-rp-meta-rule-listp-opener-cons
    (equal (valid-rp-meta-rule-listp (cons rule1 rest) state)
           (and (valid-rp-meta-rulep rule1 state)
                (valid-rp-meta-rule-listp rest state)))
    :hints (("goal"
             :in-theory (e/d (valid-rp-meta-rule-listp)
                             (valid-rp-meta-rulep)))))

  (defthm valid-rp-meta-rule-listp-opener-nil
    (equal (valid-rp-meta-rule-listp nil state)
           t)
    :hints (("goal"
             :in-theory (e/d (valid-rp-meta-rule-listp)
                             (valid-rp-meta-rulep)))))

  (defthm rp-meta-valid-syntax-listp-opener-cons
    (equal (rp-meta-valid-syntax-listp (cons first rest) state)
           (and (rp-meta-valid-syntaxp-sk first state)
                (rp-meta-valid-syntax-listp rest
                                            state)))
    :hints (("goal"
             :in-theory (e/d (rp-meta-valid-syntax-listp)
                             (rp-meta-valid-syntaxp-sk)))))

  (defthm rp-meta-valid-syntax-listp-opener-nil
    (equal (rp-meta-valid-syntax-listp nil state)
           t)
    :hints (("goal"
             :in-theory (e/d (rp-meta-valid-syntax-listp)
                             (rp-meta-valid-syntaxp-sk))))))

(progn


  ;; (defun update-simple-meta-rules-alist-fn
  ;;   (disabled-rules meta-rule-list)
  ;;   (if (atom meta-rule-list)
  ;;       nil
  ;;     (b* ((fnc (rp-meta-fnc (car meta-rule-list)))
  ;;          (trig-fn (rp-meta-trig-fnc (car meta-rule-list)))
  ;;          (entry (hons-assoc-equal fnc disabled-rules))
  ;;          (rest (update-simple-meta-rules-alist-fn disabled-rules (cdr meta-rule-list))) 
  ;;          ((when (or (not entry)
  ;;                     (not (cdr entry)))) 
  ;;           (acons trig-fn fnc rest)))
  ;;       rest)))
           

  ;; (defmacro update-simple-meta-rules-alist ()
  ;;   `(make-event
  ;;     (b* ((rp-rw-meta-rules-with-fc (table-alist 'rp-rw-meta-rules world))
  ;;          (meta-rules (get-meta-rules rp-rw-meta-rules-with-fc))
  ;;          ((table disabled-rp-meta-rules t)
     

  (defwarrant RP-META-FNC)
  (defwarrant RP-META-TRIG-FNC)
  
  (define disable-meta-rules-fnc (meta-rules-list args)
    :verify-guards nil
    (if (atom args)
        nil
      (cons `(disable-rules
              ',(loop$ for x in meta-rules-list
                      when (equal (car args)
                                  (rp-meta-fnc x))
                      collect
                      `(:meta ,(rp-meta-fnc x) . ,(rp-meta-trig-fnc x))))
            (disable-meta-rules-fnc meta-rules-list (cdr args)))))

  (define enable-meta-rules-fnc (meta-rules-list args)
    :verify-guards nil
    (if (atom args)
        nil
      (cons `(enable-rules
              ',(loop$ for x in meta-rules-list
                      when (equal (car args)
                                  (rp-meta-fnc x))
                      collect
                      `(:meta ,(rp-meta-fnc x) . ,(rp-meta-trig-fnc x))))
            (enable-meta-rules-fnc meta-rules-list (cdr args)))))

  
  

  (defmacro disable-all-meta-rules ()
    `(make-event
      (b* ((meta-rules-list (cdr (assoc-equal 'meta-rules-list (table-alist 'rp-rw (w state)))))
           (meta-fncs (loop$ for x in meta-rules-list collect (rp-meta-fnc x))))
        `(disable-meta-rules ,@meta-fncs))))

  (defmacro enable-all-meta-rules ()
    `(make-event
      (b* ((meta-rules-list (cdr (assoc-equal 'meta-rules-list (table-alist 'rp-rw (w state)))))
           (meta-fncs (loop$ for x in meta-rules-list collect (rp-meta-fnc x))))
        `(enable-meta-rules ,@meta-fncs))))
  
  (defmacro disable-meta-rules (&rest args)
    (if (not args)
        `(value-triple :none)
      `(make-event
        (b* ((meta-rules-list (cdr (assoc-equal 'meta-rules-list (table-alist 'rp-rw (w state))))))
          `(progn
             ,@(disable-meta-rules-fnc meta-rules-list ',args))))))
      
  (defmacro enable-meta-rules (&rest args)
    (if (not args)
        `(value-triple :none)
      `(make-event
        (b* ((meta-rules-list (cdr (assoc-equal 'meta-rules-list (table-alist 'rp-rw (w state))))))
          `(progn
             ,@(enable-meta-rules-fnc meta-rules-list ',args))))))

  (defmacro bump-all-enabled-meta-rules ()
    `(make-event
      `(progn
        (bump-rp-rules ,@(reverse (get-enabled-meta-rules-from-table nil state)))
        (bump-rp-rules ,@(reverse (get-enabled-meta-rules-from-table t state)))))))

(defthm iff-of-rp-evlt-lst
  (iff (rp-evlt-lst subterms a)
       (consp subterms))
  :hints (("goal"
           :induct (len subterms)
           :do-not-induct t
           :in-theory (e/d () ()))))


(defthmd rp-evl-of-ex-from-rp-reverse-for-atom
  (implies (syntaxp (atom x))
           (equal (rp-evl x a)
                  (rp-evl (ex-from-rp x) a)))
   :hints (("Goal"
           :do-not-induct t
           :induct (ex-from-rp x)
           :in-theory (e/d (is-rp) ()))))

(defthmd rp-evlt-of-ex-from-rp-reverse-for-atom
  (implies (syntaxp (atom x))
           (equal (rp-evlt x a)
                  (rp-evlt (ex-from-rp x) a)))
  :hints (("Goal"
           :do-not-induct t
           :induct (ex-from-rp x)
           :in-theory (e/d (is-rp) ()))))


(acl2::def-ruleset
 regular-eval-lemmas
 nil)

(acl2::def-ruleset
 regular-eval-lemmas-with-ex-from-rp
 nil)


(defun create-regular-eval-lemma-fn (fn argc formula-checks)
  `(progn
     (defthmd ,(sa 'regular-rp-evl-of fn 'when formula-checks)
       (implies (and (rp-evl-meta-extract-global-facts :state state)
                     (,formula-checks state)
                     (case-match x ((',fn . ,(repeat argc '&)) t)))
                (and (equal (rp-evl x a)
                            (,fn . ,(loop$ for i from 1 to argc
                                           collect `(rp-evl (nth ,i x) a))))
                     (equal (rp-evlt x a)
                            (,fn . ,(loop$ for i from 1 to argc
                                           collect `(rp-evlt (nth ,i x)
                                                             a)))))))
     (acl2::add-to-ruleset regular-eval-lemmas '(,(sa 'regular-rp-evl-of fn 'when formula-checks)))
     (defthmd ,(sa 'regular-rp-evl-of fn 'when formula-checks 'with-ex-from-rp)
       (implies (and (rp-evl-meta-extract-global-facts :state state)
                     (,formula-checks state)
                     (let* ((x (ex-from-rp x))) (case-match x ((',fn . ,(repeat argc '&)) t))))
                (and (equal
                      (rp-evl x a)
                      (,fn . ,(loop$ for i from 1 to argc
                                     collect `(rp-evl (nth ,i (ex-from-rp  x)) a))))
                     (equal
                      (rp-evlt x a)
                      (,fn . ,(loop$ for i from 1 to argc
                                     collect `(rp-evlt (nth ,i (ex-from-rp x)) a))))))
       :hints (("Goal"
                :use ((:instance
                       ,(sa 'regular-rp-evl-of fn 'when formula-checks)
                       (x (ex-from-rp x))))
                :in-theory '(
                             rp-evlt-of-ex-from-rp-reverse-for-atom
                             rp-evl-of-ex-from-rp-reverse-for-atom ))))
     (acl2::add-to-ruleset regular-eval-lemmas
                           '(,(sa 'regular-rp-evl-of fn 'when formula-checks 'with-ex-from-rp)))
     (acl2::add-to-ruleset regular-eval-lemmas-with-ex-from-rp
                           '(,(sa 'regular-rp-evl-of fn 'when formula-checks 'with-ex-from-rp)))))


(defmacro create-regular-eval-lemma (fn argc formula-checks)
  `(make-event
    (create-regular-eval-lemma-fn ',fn ',argc ',formula-checks)))



(xdoc::defxdoc
 rp-rewriter/meta-rules
 :parents (rp-rewriter)
 :short "The steps necessary to add meta rules to RP-Rewriter"
 :long "<p>Below are the steps users need to follow, and information they may
 use:</p>

<p>
1. Create your  meta function.
<code>
@('(define <meta-fnc> (term)
     :returns (mv term dont-rw) OR (term)
     ...)')
</code>
Your meta function can return either two values:term and @(see rp::dont-rw); or
only term. For best performance, it is recommended that you return dont-rw
structure as well. If you do not want the returned term to be rewritten at all,
you can return 't' for dont-rw.
</p>

<p>
2. Create formula-checks function.
<code>
@('(def-formula-checks <formula-check-name>
       (<list-of-function-names>))')
</code>
This event submits a function with signature @('(<formula-check-name> state)'). When
you add this function to your correctness theorem for this meta function, the
evaluator of RP-Rewriter will recognize the functions you list.
</p>

<p>
3. Prove that evaluation of the function returns an equivalent term under the
evaluator.
<code>
@('(defthm rp-evlt-of-meta-fnc
    (implies (and (valid-sc term a) ;;optional
                  (rp-termp term) ;;optional
                  (rp-evl-meta-extract-global-facts)
                  (<formula-check-name> state))
             (equal (rp-evlt (<meta-fnc> term) a)
                    (rp-evlt term a))))')
</code>

This is the correctness theorem of the meta rule. Optionally, you may have
(valid-sc term a), which states that the side-conditions in RP-Rewriter are
correct; and (rp-termp term), which states that some of the syntactic
invariances hold and the term is syntactically compatible with RP-Rewriter. See
discussions for @(see valid-sc) and @(see rp-termp).
</p>

<p>
If the meta function returns dont-rw, then you need to prove the same lemma for
@('(mv-nth 0 (<meta-fnc> term))').
</p>

<p>
4. Prove that meta-function retains the correctness of side-conditions.
<code>
 @('(defthm valid-sc-of-meta-fnc
    (implies (and (valid-sc term a)
                  (rp-termp term) ;;optional
                  (rp-evl-meta-extract-global-facts) ;;optional
                  (<formula-check-name> state)) ;;optional
             (valid-sc (<meta-fnc> term) a)))')
</code>

Meta functions can introduce or change side-conditions by manipulating 'rp'
instances. Therefore users need to prove that the invariance about side
conditions are maintained.
</p>

<p>
If the meta function returns dont-rw, then you need to prove the same lemma for
@('(mv-nth 0 (<meta-fnc> term))').
</p>

<p>
5. Optionally, prove that the meta function returns a valid syntax.
<code>
@('(defthm rp-termp-of-meta-fnc
    (implies (rp-termp term)
             (rp-termp (<meta-fnc> term))))')
</code>

Even though it is optional, it is recommended that you prove such a lemma for
your meta function. It prevents syntactic check on every term returned from
meta function.
</p>
<p>
If the meta function returns dont-rw, then you need to prove the same lemma for
@('(mv-nth 0 (<meta-fnc> term))').
</p>

<p>
6. If your function returns @(see rp::dont-rw), then you also need to prove
that it is syntactically correct. Otherwise skip this step.
<code>
@('(defthm dont-rw-syntaxp-of-meta-fnc
   (dont-rw-syntaxp (mv-nth 1 (<meta-fnc> term))))')
</code>
</p>

<p>
7. Save the meta rule in the rule-set of RP-Rewriter for meta rules.
<code>
@('
(add-meta-rules <formula-check-name>
                (list (make rp-meta-rule-rec
                            :fnc <meta-fnc>
                            :trig-fnc <trig-fnc>
                            :dont-rw <t-if-returns-dont-rw>
                            :outside-in <t-if-the-meta-rule-should-apply-from-outside-in>
                            :valid-syntax <t-if-rp-termp-of-meta-fnc-is-proved>)))')
</code>

</p>

<p>
8. Attach these newly created meta functions.
<code>
@('(rp::attach-meta-fncs <a-unique-name-for-updated-clause-processor>)')
</code>
If you are going to include this book later when other meta rules for
RP-Rewriter is present, you may want to call this function when all the meta
rules are included.
</p>


<p>
You may look at examples of RP-Rewriter meta rules under
/books/projects/RP-Rewriter/meta/*
</p>

<p>
Some books under /books/projects/RP-Rewriter/proofs/* might be useful when
proving when proving meta rules correct, especially aux-function-lemmas and
eval-functions-lemmas.
</p>

")

(xdoc::defxdoc
 dont-rw
 :parents (rp-rewriter/meta-rules)
 :short "A special data structure that RP-Rewriter meta rules may return to
 control rewriting of returned terms."
 :long "<p>When a term us returned from a meta rule, it appears as completely
 new to the rewriter and by default, it will be parsed completely and be
 rewritten for a second time. This can cause performance issues with big
 terms. To solve this problem, we use a special structure called dont-rw that
 meta functions may generate and return to control which subterms should be
 rewritten and which should not.</p>

<p>
The dont-rw structure has the same cons skeleton as the term itself such that
it is traversed (car'ed and cdr'ed) the same way as the term. Whenever dont-rw
structure becomes an atom and non-nil, the rewriting of corresponding term
stops. For example, assume that a meta rule returns the following term and we
would like to avoid rewriting all the instances of g, then the following
dont-rw structure would enable that.</p>

<code>
 (f1 (f2 (g a b) c)
     (f3 d (g x y)))
 </code>
 <code>
 (nil (nil t t)
      (nil t t))
</code>")
