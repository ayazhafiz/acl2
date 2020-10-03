; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "schemalg-template-generators")

(include-book "kestrel/event-macros/proof-preparation" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains generic proofs for
; the termination, guard, and refinement theorems generated by SCHEMALG.
; The proofs are generic because they are based on template functions.
; The SCHEMALG implementation generates proofs consistently with this file.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate generic outputs of the transformation,
; corresponding to the generic inputs generated by GEN-INPUTS,
; for different values of n and m and
; different positions npos and mpos within 1,...,n and 1,...m
; (both npos and mpos are 0-based);
; the instantiations are passed explicitly
; so their structure is more clear than if they were calculated.

; generate list of variables Z1, ..., Zm:
(defun gen-z1...zm (m)
  (cond ((zp m) nil)
        (t (append (gen-z1...zm (1- m)) (list (packn (list 'z m)))))))

(defmacro gen-outputs (n npos m mpos &key equal-algo-l2r-inst algo-correct-inst)
  (let* ((x1...xn (gen-x1...xn n))
         (z1...zm (gen-z1...zm m))
         (a1...am (gen-a1...am m x1...xn))
         (x1... (take npos x1...xn))
         (...xn (nthcdr npos x1...xn))
         (z1... (take mpos z1...zm))
         (...zm (nthcdr mpos z1...zm))
         (a1... (take mpos a1...am))
         (...am (nthcdr mpos a1...am)))
    `(encapsulate ()
       (evmac-prepare-proofs)
       (gen-funvar :name ?g :arity ,(1+ m))
       (gen-funvar :name ?h :arity ,(+ 2 m))
       (gen-algo
        :z1... ,z1...
        :...zm ,@(list ...zm)
        :hints (("Goal" :in-theory nil))
        :guard-hints (("Goal" :in-theory nil)))
       (gen-spec-0
        :x1... ,x1...
        :...xn ,@(list ...xn)
        :a1... ,a1...
        :...am ,@(list ...am)
        :guard-hints (("Goal" :in-theory nil)))
       (gen-spec-1
        :x1... ,x1...
        :...xn ,@(list ...xn)
        :a1... ,a1...
        :...am ,@(list ...am)
        :guard-hints (("Goal" :in-theory nil)))
       (gen-equal-algo
        :z1... ,z1...
        :...zm ,@(list ...zm))
       (gen-algo-correct
        :x1... ,x1...
        :...xn ,@(list ...xn)
        :a1... ,a1...
        :...am ,@(list ...am)
        :hints (("Goal"
                 :in-theory '(algo[?g][?h] atom)
                 :induct (algo[?g][?h] ,@z1... x ,@...zm))
                '(:use (spec-0[?g]-necc
                        (:instance spec-1[?h]-necc
                         (y (algo[?g][?h] ,@a1... (cdr x) ,@...am)))))))
       (gen-new
        :guard-hints (("Goal" :in-theory nil)))
       (gen-old-if-new
        :hints (("Goal"
                 :in-theory '(old new)
                 :use ((:instance ?f-to-algo[?g][?h] ,@equal-algo-l2r-inst)
                       (:instance algo-correct ,@algo-correct-inst))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Proof templates for n = m = 0.

(must-succeed*
 (gen-inputs 0 0 0 0)
 (gen-outputs 0 0 0 0
              :equal-algo-l2r-inst ((x (old-witness)))
              :algo-correct-inst ((x (old-witness)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Proof templates for n = m = 1.

; (invariant to mpos)

(must-succeed*
 (gen-inputs 1 0 1 0)
 (gen-outputs 1 0 1 0
              :equal-algo-l2r-inst ((x (mv-nth 0 (old-witness)))
                                    (z1 (a1 (mv-nth 1 (old-witness)))))
              :algo-correct-inst ((x (mv-nth 0 (old-witness)))
                                  (x1 (mv-nth 1 (old-witness))))))

(must-succeed*
 (gen-inputs 1 1 1 0)
 (gen-outputs 1 1 1 0
              :equal-algo-l2r-inst ((x (mv-nth 1 (old-witness)))
                                    (z1 (a1 (mv-nth 0 (old-witness)))))
              :algo-correct-inst ((x1 (mv-nth 0 (old-witness)))
                                  (x (mv-nth 1 (old-witness))))))

(must-succeed*
 (gen-inputs 1 0 1 1)
 (gen-outputs 1 0 1 1
              :equal-algo-l2r-inst ((x (mv-nth 0 (old-witness)))
                                    (z1 (a1 (mv-nth 1 (old-witness)))))
              :algo-correct-inst ((x (mv-nth 0 (old-witness)))
                                  (x1 (mv-nth 1 (old-witness))))))

(must-succeed*
 (gen-inputs 1 1 1 1)
 (gen-outputs 1 1 1 1
              :equal-algo-l2r-inst ((x (mv-nth 1 (old-witness)))
                                    (z1 (a1 (mv-nth 0 (old-witness)))))
              :algo-correct-inst ((x1 (mv-nth 0 (old-witness)))
                                  (x (mv-nth 1 (old-witness))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Proof templates for n = 1 and m = 1.

; (invariant to mpos)

(must-succeed*
 (gen-inputs 2 0 1 0)
 (gen-outputs 2 0 1 0
              :equal-algo-l2r-inst ((x (mv-nth 0 (old-witness)))
                                    (z1 (a1 (mv-nth 1 (old-witness))
                                            (mv-nth 2 (old-witness)))))
              :algo-correct-inst ((x (mv-nth 0 (old-witness)))
                                  (x1 (mv-nth 1 (old-witness)))
                                  (x2 (mv-nth 2 (old-witness))))))

(must-succeed*
 (gen-inputs 2 1 1 0)
 (gen-outputs 2 1 1 0
              :equal-algo-l2r-inst ((x (mv-nth 1 (old-witness)))
                                    (z1 (a1 (mv-nth 0 (old-witness))
                                            (mv-nth 2 (old-witness)))))
              :algo-correct-inst ((x1 (mv-nth 0 (old-witness)))
                                  (x (mv-nth 1 (old-witness)))
                                  (x2 (mv-nth 2 (old-witness))))))

(must-succeed*
 (gen-inputs 2 2 1 0)
 (gen-outputs 2 2 1 0
              :equal-algo-l2r-inst ((x (mv-nth 2 (old-witness)))
                                    (z1 (a1 (mv-nth 0 (old-witness))
                                            (mv-nth 1 (old-witness)))))
              :algo-correct-inst ((x1 (mv-nth 0 (old-witness)))
                                  (x2 (mv-nth 1 (old-witness)))
                                  (x (mv-nth 2 (old-witness))))))

(must-succeed*
 (gen-inputs 2 0 1 1)
 (gen-outputs 2 0 1 1
              :equal-algo-l2r-inst ((x (mv-nth 0 (old-witness)))
                                    (z1 (a1 (mv-nth 1 (old-witness))
                                            (mv-nth 2 (old-witness)))))
              :algo-correct-inst ((x (mv-nth 0 (old-witness)))
                                  (x1 (mv-nth 1 (old-witness)))
                                  (x2 (mv-nth 2 (old-witness))))))

(must-succeed*
 (gen-inputs 2 1 1 1)
 (gen-outputs 2 1 1 1
              :equal-algo-l2r-inst ((x (mv-nth 1 (old-witness)))
                                    (z1 (a1 (mv-nth 0 (old-witness))
                                            (mv-nth 2 (old-witness)))))
              :algo-correct-inst ((x1 (mv-nth 0 (old-witness)))
                                  (x (mv-nth 1 (old-witness)))
                                  (x2 (mv-nth 2 (old-witness))))))

(must-succeed*
 (gen-inputs 2 2 1 1)
 (gen-outputs 2 2 1 1
              :equal-algo-l2r-inst ((x (mv-nth 2 (old-witness)))
                                    (z1 (a1 (mv-nth 0 (old-witness))
                                            (mv-nth 1 (old-witness)))))
              :algo-correct-inst ((x1 (mv-nth 0 (old-witness)))
                                  (x2 (mv-nth 1 (old-witness)))
                                  (x (mv-nth 2 (old-witness))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Proof templates for n = 1 and m = 2.

; (invariant to mpos)

(must-succeed*
 (gen-inputs 1 0 2 0)
 (gen-outputs 1 0 2 0
              :equal-algo-l2r-inst ((x (mv-nth 0 (old-witness)))
                                    (z1 (a1 (mv-nth 1 (old-witness))))
                                    (z2 (a2 (mv-nth 1 (old-witness)))))
              :algo-correct-inst ((x (mv-nth 0 (old-witness)))
                                  (x1 (mv-nth 1 (old-witness))))))

(must-succeed*
 (gen-inputs 1 1 2 0)
 (gen-outputs 1 1 2 0
              :equal-algo-l2r-inst ((x (mv-nth 1 (old-witness)))
                                    (z1 (a1 (mv-nth 0 (old-witness))))
                                    (z2 (a2 (mv-nth 0 (old-witness)))))
              :algo-correct-inst ((x1 (mv-nth 0 (old-witness)))
                                  (x (mv-nth 1 (old-witness))))))

(must-succeed*
 (gen-inputs 1 0 2 1)
 (gen-outputs 1 0 2 1
              :equal-algo-l2r-inst ((x (mv-nth 0 (old-witness)))
                                    (z1 (a1 (mv-nth 1 (old-witness))))
                                    (z2 (a2 (mv-nth 1 (old-witness)))))
              :algo-correct-inst ((x (mv-nth 0 (old-witness)))
                                  (x1 (mv-nth 1 (old-witness))))))

(must-succeed*
 (gen-inputs 1 1 2 1)
 (gen-outputs 1 1 2 1
              :equal-algo-l2r-inst ((x (mv-nth 1 (old-witness)))
                                    (z1 (a1 (mv-nth 0 (old-witness))))
                                    (z2 (a2 (mv-nth 0 (old-witness)))))
              :algo-correct-inst ((x1 (mv-nth 0 (old-witness)))
                                  (x (mv-nth 1 (old-witness))))))

(must-succeed*
 (gen-inputs 1 0 2 2)
 (gen-outputs 1 0 2 2
              :equal-algo-l2r-inst ((x (mv-nth 0 (old-witness)))
                                    (z1 (a1 (mv-nth 1 (old-witness))))
                                    (z2 (a2 (mv-nth 1 (old-witness)))))
              :algo-correct-inst ((x (mv-nth 0 (old-witness)))
                                  (x1 (mv-nth 1 (old-witness))))))

(must-succeed*
 (gen-inputs 1 1 2 2)
 (gen-outputs 1 1 2 2
              :equal-algo-l2r-inst ((x (mv-nth 1 (old-witness)))
                                    (z1 (a1 (mv-nth 0 (old-witness))))
                                    (z2 (a2 (mv-nth 0 (old-witness)))))
              :algo-correct-inst ((x1 (mv-nth 0 (old-witness)))
                                  (x (mv-nth 1 (old-witness))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Proof templates for n = m = 2.

; (invariant to mpos)

(must-succeed*
 (gen-inputs 2 0 2 0)
 (gen-outputs 2 0 2 0
              :equal-algo-l2r-inst ((x (mv-nth 0 (old-witness)))
                                    (z1 (a1 (mv-nth 1 (old-witness))
                                            (mv-nth 2 (old-witness))))
                                    (z2 (a2 (mv-nth 1 (old-witness))
                                            (mv-nth 2 (old-witness)))))
              :algo-correct-inst ((x (mv-nth 0 (old-witness)))
                                  (x1 (mv-nth 1 (old-witness)))
                                  (x2 (mv-nth 2 (old-witness))))))

(must-succeed*
 (gen-inputs 2 1 2 0)
 (gen-outputs 2 1 2 0
              :equal-algo-l2r-inst ((x (mv-nth 1 (old-witness)))
                                    (z1 (a1 (mv-nth 0 (old-witness))
                                            (mv-nth 2 (old-witness))))
                                    (z2 (a2 (mv-nth 0 (old-witness))
                                            (mv-nth 2 (old-witness)))))
              :algo-correct-inst ((x1 (mv-nth 0 (old-witness)))
                                  (x (mv-nth 1 (old-witness)))
                                  (x2 (mv-nth 2 (old-witness))))))

(must-succeed*
 (gen-inputs 2 2 2 0)
 (gen-outputs 2 2 2 0
              :equal-algo-l2r-inst ((x (mv-nth 2 (old-witness)))
                                    (z1 (a1 (mv-nth 0 (old-witness))
                                            (mv-nth 1 (old-witness))))
                                    (z2 (a2 (mv-nth 0 (old-witness))
                                            (mv-nth 1 (old-witness)))))
              :algo-correct-inst ((x1 (mv-nth 0 (old-witness)))
                                  (x2 (mv-nth 1 (old-witness)))
                                  (x (mv-nth 2 (old-witness))))))

(must-succeed*
 (gen-inputs 2 0 2 1)
 (gen-outputs 2 0 2 1
              :equal-algo-l2r-inst ((x (mv-nth 0 (old-witness)))
                                    (z1 (a1 (mv-nth 1 (old-witness))
                                            (mv-nth 2 (old-witness))))
                                    (z2 (a2 (mv-nth 1 (old-witness))
                                            (mv-nth 2 (old-witness)))))
              :algo-correct-inst ((x (mv-nth 0 (old-witness)))
                                  (x1 (mv-nth 1 (old-witness)))
                                  (x2 (mv-nth 2 (old-witness))))))

(must-succeed*
 (gen-inputs 2 1 2 1)
 (gen-outputs 2 1 2 1
              :equal-algo-l2r-inst ((x (mv-nth 1 (old-witness)))
                                    (z1 (a1 (mv-nth 0 (old-witness))
                                            (mv-nth 2 (old-witness))))
                                    (z2 (a2 (mv-nth 0 (old-witness))
                                            (mv-nth 2 (old-witness)))))
              :algo-correct-inst ((x1 (mv-nth 0 (old-witness)))
                                  (x (mv-nth 1 (old-witness)))
                                  (x2 (mv-nth 2 (old-witness))))))

(must-succeed*
 (gen-inputs 2 2 2 1)
 (gen-outputs 2 2 2 1
              :equal-algo-l2r-inst ((x (mv-nth 2 (old-witness)))
                                    (z1 (a1 (mv-nth 0 (old-witness))
                                            (mv-nth 1 (old-witness))))
                                    (z2 (a2 (mv-nth 0 (old-witness))
                                            (mv-nth 1 (old-witness)))))
              :algo-correct-inst ((x1 (mv-nth 0 (old-witness)))
                                  (x2 (mv-nth 1 (old-witness)))
                                  (x (mv-nth 2 (old-witness))))))

(must-succeed*
 (gen-inputs 2 0 2 2)
 (gen-outputs 2 0 2 2
              :equal-algo-l2r-inst ((x (mv-nth 0 (old-witness)))
                                    (z1 (a1 (mv-nth 1 (old-witness))
                                            (mv-nth 2 (old-witness))))
                                    (z2 (a2 (mv-nth 1 (old-witness))
                                            (mv-nth 2 (old-witness)))))
              :algo-correct-inst ((x (mv-nth 0 (old-witness)))
                                  (x1 (mv-nth 1 (old-witness)))
                                  (x2 (mv-nth 2 (old-witness))))))

(must-succeed*
 (gen-inputs 2 1 2 2)
 (gen-outputs 2 1 2 2
              :equal-algo-l2r-inst ((x (mv-nth 1 (old-witness)))
                                    (z1 (a1 (mv-nth 0 (old-witness))
                                            (mv-nth 2 (old-witness))))
                                    (z2 (a2 (mv-nth 0 (old-witness))
                                            (mv-nth 2 (old-witness)))))
              :algo-correct-inst ((x1 (mv-nth 0 (old-witness)))
                                  (x (mv-nth 1 (old-witness)))
                                  (x2 (mv-nth 2 (old-witness))))))

(must-succeed*
 (gen-inputs 2 2 2 2)
 (gen-outputs 2 2 2 2
              :equal-algo-l2r-inst ((x (mv-nth 2 (old-witness)))
                                    (z1 (a1 (mv-nth 0 (old-witness))
                                            (mv-nth 1 (old-witness))))
                                    (z2 (a2 (mv-nth 0 (old-witness))
                                            (mv-nth 1 (old-witness)))))
              :algo-correct-inst ((x1 (mv-nth 0 (old-witness)))
                                  (x2 (mv-nth 1 (old-witness)))
                                  (x (mv-nth 2 (old-witness))))))
