; A variant of update-nth that does some fixing
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: In-progress

(local (include-book "kestrel/lists-light/take" :dir :system))

;guaranteed to return a result of length len (actually (nfix len))
(defund update-nth2 (len key val lst)
  (declare (xargs :guard (and (natp len)
                              (natp key)
                              (true-listp lst)
                              )))
  ;;the min (instead of just key) prevents very expensive computations when key is huge
  (take len (update-nth (min (nfix key)
                             (nfix len))
                        val lst)))

(defthm len-of-update-nth2
  (implies (natp len)
           (equal (len (update-nth2 len key val lst))
                  len))
  :hints (("Goal" :in-theory (enable update-nth2))))

(defthm consp-of-update-nth2
  (equal (consp (update-nth2 len key val lst))
         (posp len))
  :hints (("Goal" :in-theory (enable update-nth2))))

(defthm nth-of-update-nth2
  (implies (and (< m len) ;work-hard?
                (natp len)
                (natp m)
                (natp n))
           (equal (nth m (update-nth2 len n val l))
                  (if (equal (nfix m) (nfix n))
                      val
                    (nth m l))))
  :hints
  (("Goal" :in-theory (e/d (update-nth2)
                           ()))))

(defthm nth-update-nth2-safe
  (implies (and (syntaxp (and (quotep m)
                              (quotep n)))
                (< m len)
                (natp len)
                (natp m)
                (natp n)
                )
           (equal (nth m (update-nth2 len n val l))
                  (if (equal (nfix m) (nfix n))
                      val
                    (nth m l))))
  :hints (("Goal" :in-theory (e/d (update-nth2) (;update-nth-becomes-update-nth2
                                                 )))))

(defthm update-nth2-of-0-arg1
  (equal (update-nth2 0 key val lst)
         nil)
  :hints (("Goal" :in-theory (enable update-nth2))))

(defthm update-nth2-too-high
  (implies (and (<= len key) ;weird case
                (integerp len)
                (integerp key))
           (equal (update-nth2 len key val lst)
                  (take len lst)))
  :hints (("Goal" :in-theory (e/d (update-nth2)
                                  ()))))

;only needed by axe?
(defthm true-listp-of-update-nth2
  (true-listp (update-nth2 len key val lst)))

(defthm update-nth2-not-nil1
  (implies (not (zp a))
           (equal (equal (update-nth2 a b c d) nil)
                  nil))
  :hints (("Goal" :in-theory (enable update-nth2))))

(defthm update-nth2-not-nil2
  (implies (not (zp a))
           (equal (equal nil (update-nth2 a b c d))
                  nil))
  :hints (("Goal" :in-theory (enable update-nth2))))

(defthm nth-of-update-nth2-too-high
  (implies (and (<= m n)
                (natp m)
                (posp n))
           (equal (nth n (update-nth2 m index val data))
                  nil))
  :hints (("Goal" :in-theory (e/d (update-nth2) (take-of-update-nth)))))
