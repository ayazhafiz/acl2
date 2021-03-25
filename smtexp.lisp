(include-book "books/projects/smtlink/top")
(value-triple (tshell-ensure))
(add-default-hints '((SMT::SMT-computed-hint clause)))

(ubt! 'poly-ineq-example-a)

;(defthm poly-ineq-example-a
;  (implies (and (rationalp x) (rationalp y)
;                (<= (+ (* 4/5 x x) (* y y)) 1)
;                (<= (- (* x x) (* y y)) 1))
;           (<= y (- (* 3 (- x 17/8) (- x 17/8)) 3)))
;  :hints (("Goal"
;           :clause-processor
;           (smt::Smtlink clause nil))))
;
;(defthm p2
;  (implies (and (rationalp l))
;           (equal (+ l l) l))
;  :hints (("Goal"
;           :clause-processor
;           (smt::Smtlink clause nil))))

(fty::deflist my-integer-list
              :elt-type integerp
              :true-listp t)

;(defthm arb
;  (and (listp b) (natp (append b a)))
;  :hints (("Goal" :smtlink nil)))

;(defthm arb-2
;  (implies (and (integer-listp l)) (>= (len l) 0))
;  :hints (("Goal" :smtlink (:fty (acl2::integer-list)))))

;(defthm arb-2
;  (and (integer-listp l) (natp l))
;  :hints (("Goal" :smtlink (:fty (acl2::integer-list)))))

(defthm arb
  (implies (integerp n) (and (< 5 n) (> 5 n)))
  :hints (("Goal" :smtlink nil)))

;(defthm arb
;    (implies
;      (and (my-integer-list-p a))
;      (equal (rev (rev a)) a))
;    :hints (("Goal" :smtlink (:fty (my-integer-list)))))

;(defthm
;  fty-deflist-theorem
;  (implies
;   (and
;    (integer-listp l))
;   (>=
;    (+
;     (car l)
;     (car (cdr l)))
;    0))
;  :hints (("Goal" :smtlink (:fty (acl2::integer-list))))
;  :rule-classes nil)

;(defthm poly-of-expt-example
;  (implies (and (rationalp x) (rationalp y) (rationalp z) (integerp m)
;                (integerp n) (< 0 z) (< z 1) (< 0 m) (< m n))
;           (<= (* 2 (expt z n) x y) (* (expt z m) (+ (* x x) (* y y)))))
;  :hints(("Goal"
;          :clause-processor
;          (smt::Smtlink clause '((:let ((expt_z_m (expt z m) rationalp)
;                                        (expt_z_n (expt z n) rationalp)))
;                                 (:hypothesize ((< expt_z_n expt_z_m)
;                                                (< 0 expt_z_m)
;                                                (< 0 expt_z_n)))
;                                 )
;                        ))))
