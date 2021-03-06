(UBYTE3-LISTP)
(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(STD::DEFLIST-LOCAL-ELEMENTP-OF-NIL-THM)
(UBYTE3-LISTP-OF-CONS)
(UBYTE3-LISTP-OF-CDR-WHEN-UBYTE3-LISTP)
(UBYTE3-LISTP-WHEN-NOT-CONSP)
(UBYTE3P-OF-CAR-WHEN-UBYTE3-LISTP)
(TRUE-LISTP-WHEN-UBYTE3-LISTP)
(UBYTE3-LISTP-OF-LIST-FIX)
(UBYTE3-LISTP-OF-SFIX)
(UBYTE3-LISTP-OF-INSERT)
(UBYTE3-LISTP-OF-DELETE)
(UBYTE3-LISTP-OF-MERGESORT)
(UBYTE3-LISTP-OF-UNION)
(UBYTE3-LISTP-OF-INTERSECT-1)
(UBYTE3-LISTP-OF-INTERSECT-2)
(UBYTE3-LISTP-OF-DIFFERENCE)
(UBYTE3-LISTP-OF-DUPLICATED-MEMBERS)
(UBYTE3-LISTP-OF-REV)
(UBYTE3-LISTP-OF-APPEND)
(UBYTE3-LISTP-OF-RCONS)
(UBYTE3P-WHEN-MEMBER-EQUAL-OF-UBYTE3-LISTP)
(UBYTE3-LISTP-WHEN-SUBSETP-EQUAL)
(UBYTE3-LISTP-OF-SET-DIFFERENCE-EQUAL)
(UBYTE3-LISTP-OF-INTERSECTION-EQUAL-1)
(UBYTE3-LISTP-OF-INTERSECTION-EQUAL-2)
(UBYTE3-LISTP-OF-UNION-EQUAL)
(UBYTE3-LISTP-OF-TAKE)
(UBYTE3-LISTP-OF-REPEAT)
(UBYTE3P-OF-NTH-WHEN-UBYTE3-LISTP)
(UBYTE3-LISTP-OF-UPDATE-NTH)
(UBYTE3-LISTP-OF-BUTLAST)
(UBYTE3-LISTP-OF-NTHCDR)
(UBYTE3-LISTP-OF-LAST)
(UBYTE3-LISTP-OF-REMOVE)
(UBYTE3-LISTP-OF-REVAPPEND)
(UBYTE3-LIST-FIX$INLINE)
(UBYTE3-LISTP-OF-UBYTE3-LIST-FIX
     (30 1 (:REWRITE UBYTE3-FIX-WHEN-UBYTE3P))
     (22 2
         (:REWRITE UBYTE3P-OF-CAR-WHEN-UBYTE3-LISTP))
     (18 10
         (:REWRITE UBYTE3-LISTP-WHEN-SUBSETP-EQUAL))
     (15 1 (:DEFINITION UBYTE3-LISTP))
     (12 6
         (:REWRITE UBYTE3P-WHEN-MEMBER-EQUAL-OF-UBYTE3-LISTP))
     (9 5
        (:REWRITE UBYTE3-LISTP-WHEN-NOT-CONSP))
     (8 8 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (4 4 (:TYPE-PRESCRIPTION UBYTE3P))
     (4 4 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (2 2
        (:REWRITE FTY::OPEN-MEMBER-EQUAL-ON-LIST-OF-TAGS))
     (2 1
        (:REWRITE UBYTE3-LISTP-OF-CDR-WHEN-UBYTE3-LISTP)))
(UBYTE3-LIST-FIX-WHEN-UBYTE3-LISTP
     (32 4
         (:REWRITE UBYTE3-LISTP-OF-CDR-WHEN-UBYTE3-LISTP))
     (28 24
         (:REWRITE UBYTE3-LISTP-WHEN-SUBSETP-EQUAL))
     (13 3
         (:REWRITE UBYTE3P-OF-CAR-WHEN-UBYTE3-LISTP))
     (9 6
        (:REWRITE UBYTE3P-WHEN-MEMBER-EQUAL-OF-UBYTE3-LISTP))
     (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (2 2 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (1 1
        (:REWRITE FTY::OPEN-MEMBER-EQUAL-ON-LIST-OF-TAGS)))
(UBYTE3-LIST-FIX$INLINE
     (8 8
        (:REWRITE UBYTE3-LISTP-WHEN-SUBSETP-EQUAL))
     (6 1
        (:REWRITE UBYTE3P-OF-CAR-WHEN-UBYTE3-LISTP))
     (6 1
        (:REWRITE UBYTE3-LISTP-OF-CDR-WHEN-UBYTE3-LISTP))
     (4 4
        (:REWRITE UBYTE3-LISTP-WHEN-NOT-CONSP))
     (2 2
        (:REWRITE UBYTE3P-WHEN-MEMBER-EQUAL-OF-UBYTE3-LISTP)))
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
     (2 2
        (:REWRITE UBYTE3-LISTP-WHEN-SUBSETP-EQUAL))
     (1 1
        (:REWRITE UBYTE3-LISTP-WHEN-NOT-CONSP)))
(UBYTE3-LIST-EQUIV$INLINE)
(UBYTE3-LIST-EQUIV-IS-AN-EQUIVALENCE)
(UBYTE3-LIST-EQUIV-IMPLIES-EQUAL-UBYTE3-LIST-FIX-1)
(UBYTE3-LIST-FIX-UNDER-UBYTE3-LIST-EQUIV)
(EQUAL-OF-UBYTE3-LIST-FIX-1-FORWARD-TO-UBYTE3-LIST-EQUIV)
(EQUAL-OF-UBYTE3-LIST-FIX-2-FORWARD-TO-UBYTE3-LIST-EQUIV)
(UBYTE3-LIST-EQUIV-OF-UBYTE3-LIST-FIX-1-FORWARD)
(UBYTE3-LIST-EQUIV-OF-UBYTE3-LIST-FIX-2-FORWARD)
(CAR-OF-UBYTE3-LIST-FIX-X-UNDER-UBYTE3-EQUIV
     (33 3 (:REWRITE UBYTE3-FIX-WHEN-UBYTE3P))
     (18 3
         (:REWRITE UBYTE3P-OF-CAR-WHEN-UBYTE3-LISTP))
     (18 2
         (:REWRITE UBYTE3-LIST-FIX-WHEN-UBYTE3-LISTP))
     (12 12 (:TYPE-PRESCRIPTION UBYTE3-LISTP))
     (12 12
         (:REWRITE UBYTE3-LISTP-WHEN-SUBSETP-EQUAL))
     (6 6 (:TYPE-PRESCRIPTION UBYTE3P))
     (6 6
        (:REWRITE UBYTE3P-WHEN-MEMBER-EQUAL-OF-UBYTE3-LISTP))
     (6 6
        (:REWRITE UBYTE3-LISTP-WHEN-NOT-CONSP))
     (6 1
        (:REWRITE UBYTE3-LISTP-OF-CDR-WHEN-UBYTE3-LISTP))
     (3 3
        (:TYPE-PRESCRIPTION UBYTE3-LIST-FIX$INLINE)))
(CAR-OF-UBYTE3-LIST-FIX-X-NORMALIZE-CONST-UNDER-UBYTE3-EQUIV)
(CAR-UBYTE3-LIST-EQUIV-CONGRUENCE-ON-X-UNDER-UBYTE3-EQUIV)
(CDR-OF-UBYTE3-LIST-FIX-X-UNDER-UBYTE3-LIST-EQUIV
     (41 3
         (:REWRITE UBYTE3-LISTP-OF-CDR-WHEN-UBYTE3-LISTP))
     (22 2 (:REWRITE UBYTE3-FIX-WHEN-UBYTE3P))
     (20 20
         (:REWRITE UBYTE3-LISTP-WHEN-SUBSETP-EQUAL))
     (12 2
         (:REWRITE UBYTE3P-OF-CAR-WHEN-UBYTE3-LISTP))
     (4 4 (:TYPE-PRESCRIPTION UBYTE3P))
     (4 4
        (:REWRITE UBYTE3P-WHEN-MEMBER-EQUAL-OF-UBYTE3-LISTP)))
(CDR-OF-UBYTE3-LIST-FIX-X-NORMALIZE-CONST-UNDER-UBYTE3-LIST-EQUIV)
(CDR-UBYTE3-LIST-EQUIV-CONGRUENCE-ON-X-UNDER-UBYTE3-LIST-EQUIV)
(CONS-OF-UBYTE3-FIX-X-UNDER-UBYTE3-LIST-EQUIV
  (34 4
      (:REWRITE UBYTE3-LIST-FIX-WHEN-UBYTE3-LISTP))
  (17 2 (:REWRITE UBYTE3-LISTP-OF-CONS))
  (10 10
      (:REWRITE UBYTE3-LISTP-WHEN-SUBSETP-EQUAL))
  (8 8
     (:REWRITE UBYTE3P-WHEN-MEMBER-EQUAL-OF-UBYTE3-LISTP))
  (6 6 (:TYPE-PRESCRIPTION UBYTE3-LISTP))
  (5 5
     (:REWRITE UBYTE3-LISTP-WHEN-NOT-CONSP))
  (2 2
     (:REWRITE
          CDR-OF-UBYTE3-LIST-FIX-X-NORMALIZE-CONST-UNDER-UBYTE3-LIST-EQUIV)))
(CONS-OF-UBYTE3-FIX-X-NORMALIZE-CONST-UNDER-UBYTE3-LIST-EQUIV)
(CONS-UBYTE3-EQUIV-CONGRUENCE-ON-X-UNDER-UBYTE3-LIST-EQUIV)
(CONS-OF-UBYTE3-LIST-FIX-Y-UNDER-UBYTE3-LIST-EQUIV
  (20 2 (:REWRITE UBYTE3-LISTP-OF-CONS))
  (8 8 (:TYPE-PRESCRIPTION UBYTE3P))
  (8 8
     (:REWRITE UBYTE3P-WHEN-MEMBER-EQUAL-OF-UBYTE3-LISTP))
  (8 8
     (:REWRITE UBYTE3-LISTP-WHEN-SUBSETP-EQUAL))
  (6 2 (:REWRITE UBYTE3-FIX-WHEN-UBYTE3P))
  (5 4
     (:REWRITE UBYTE3-LISTP-WHEN-NOT-CONSP))
  (2 2
     (:REWRITE CONS-OF-UBYTE3-FIX-X-NORMALIZE-CONST-UNDER-UBYTE3-LIST-EQUIV))
  (2 2
     (:REWRITE
          CDR-OF-UBYTE3-LIST-FIX-X-NORMALIZE-CONST-UNDER-UBYTE3-LIST-EQUIV)))
(CONS-OF-UBYTE3-LIST-FIX-Y-NORMALIZE-CONST-UNDER-UBYTE3-LIST-EQUIV)
(CONS-UBYTE3-LIST-EQUIV-CONGRUENCE-ON-Y-UNDER-UBYTE3-LIST-EQUIV)
(CONSP-OF-UBYTE3-LIST-FIX
  (18 2
      (:REWRITE UBYTE3-LIST-FIX-WHEN-UBYTE3-LISTP))
  (11 1 (:REWRITE UBYTE3-FIX-WHEN-UBYTE3P))
  (8 8 (:TYPE-PRESCRIPTION UBYTE3-LISTP))
  (8 8
     (:REWRITE UBYTE3-LISTP-WHEN-SUBSETP-EQUAL))
  (6 1
     (:REWRITE UBYTE3P-OF-CAR-WHEN-UBYTE3-LISTP))
  (6 1
     (:REWRITE UBYTE3-LISTP-OF-CDR-WHEN-UBYTE3-LISTP))
  (4 4
     (:REWRITE UBYTE3-LISTP-WHEN-NOT-CONSP))
  (2 2 (:TYPE-PRESCRIPTION UBYTE3P))
  (2 2
     (:REWRITE UBYTE3P-WHEN-MEMBER-EQUAL-OF-UBYTE3-LISTP))
  (1 1
     (:REWRITE
          CDR-OF-UBYTE3-LIST-FIX-X-NORMALIZE-CONST-UNDER-UBYTE3-LIST-EQUIV)))
(UBYTE3-LIST-FIX-UNDER-IFF
  (18 2
      (:REWRITE UBYTE3-LIST-FIX-WHEN-UBYTE3-LISTP))
  (11 1 (:REWRITE UBYTE3-FIX-WHEN-UBYTE3P))
  (8 8 (:TYPE-PRESCRIPTION UBYTE3-LISTP))
  (8 8
     (:REWRITE UBYTE3-LISTP-WHEN-SUBSETP-EQUAL))
  (6 1
     (:REWRITE UBYTE3P-OF-CAR-WHEN-UBYTE3-LISTP))
  (6 1
     (:REWRITE UBYTE3-LISTP-OF-CDR-WHEN-UBYTE3-LISTP))
  (4 4
     (:REWRITE UBYTE3-LISTP-WHEN-NOT-CONSP))
  (2 2 (:TYPE-PRESCRIPTION UBYTE3P))
  (2 2
     (:REWRITE UBYTE3P-WHEN-MEMBER-EQUAL-OF-UBYTE3-LISTP))
  (1 1
     (:REWRITE
          CDR-OF-UBYTE3-LIST-FIX-X-NORMALIZE-CONST-UNDER-UBYTE3-LIST-EQUIV)))
(UBYTE3-LIST-FIX-OF-CONS
  (21 3
      (:REWRITE UBYTE3-LIST-FIX-WHEN-UBYTE3-LISTP))
  (9 1 (:REWRITE UBYTE3-LISTP-OF-CONS))
  (6 6
     (:REWRITE UBYTE3-LISTP-WHEN-SUBSETP-EQUAL))
  (6 2 (:REWRITE UBYTE3-FIX-WHEN-UBYTE3P))
  (4 4 (:TYPE-PRESCRIPTION UBYTE3P))
  (4 4 (:TYPE-PRESCRIPTION UBYTE3-LISTP))
  (4 4
     (:REWRITE UBYTE3P-WHEN-MEMBER-EQUAL-OF-UBYTE3-LISTP))
  (3 3
     (:REWRITE UBYTE3-LISTP-WHEN-NOT-CONSP))
  (1 1
     (:REWRITE
          CONS-OF-UBYTE3-LIST-FIX-Y-NORMALIZE-CONST-UNDER-UBYTE3-LIST-EQUIV))
  (1 1
     (:REWRITE CONS-OF-UBYTE3-FIX-X-NORMALIZE-CONST-UNDER-UBYTE3-LIST-EQUIV))
  (1 1
     (:REWRITE
          CDR-OF-UBYTE3-LIST-FIX-X-NORMALIZE-CONST-UNDER-UBYTE3-LIST-EQUIV)))
(LEN-OF-UBYTE3-LIST-FIX
   (35 4
       (:REWRITE UBYTE3-LIST-FIX-WHEN-UBYTE3-LISTP))
   (14 14
       (:REWRITE UBYTE3-LISTP-WHEN-SUBSETP-EQUAL))
   (13 13 (:TYPE-PRESCRIPTION UBYTE3-LISTP))
   (12 2
       (:REWRITE UBYTE3-LISTP-OF-CDR-WHEN-UBYTE3-LISTP))
   (11 1 (:REWRITE UBYTE3-FIX-WHEN-UBYTE3P))
   (7 7
      (:REWRITE UBYTE3-LISTP-WHEN-NOT-CONSP))
   (6 1
      (:REWRITE UBYTE3P-OF-CAR-WHEN-UBYTE3-LISTP))
   (2 2 (:TYPE-PRESCRIPTION UBYTE3P))
   (2 2
      (:REWRITE UBYTE3P-WHEN-MEMBER-EQUAL-OF-UBYTE3-LISTP))
   (2 2
      (:REWRITE
           CDR-OF-UBYTE3-LIST-FIX-X-NORMALIZE-CONST-UNDER-UBYTE3-LIST-EQUIV))
   (1 1 (:REWRITE FTY::EQUAL-OF-LEN)))
(UBYTE3-LIST-FIX-OF-APPEND
  (114 10
       (:REWRITE UBYTE3-LIST-FIX-WHEN-UBYTE3-LISTP))
  (58 2 (:REWRITE UBYTE3-LISTP-OF-APPEND))
  (40 36
      (:REWRITE UBYTE3-LISTP-WHEN-SUBSETP-EQUAL))
  (29 29 (:TYPE-PRESCRIPTION UBYTE3-LISTP))
  (24 2 (:REWRITE UBYTE3-LISTP-OF-LIST-FIX))
  (22 16
      (:REWRITE UBYTE3-LISTP-WHEN-NOT-CONSP))
  (14 4
      (:REWRITE UBYTE3-LISTP-OF-CDR-WHEN-UBYTE3-LISTP))
  (12 12 (:TYPE-PRESCRIPTION TRUE-LIST-FIX))
  (12 2 (:REWRITE UBYTE3-FIX-WHEN-UBYTE3P))
  (6 1
     (:REWRITE UBYTE3P-OF-CAR-WHEN-UBYTE3-LISTP))
  (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
  (2 2 (:TYPE-PRESCRIPTION UBYTE3P))
  (2 2
     (:REWRITE UBYTE3P-WHEN-MEMBER-EQUAL-OF-UBYTE3-LISTP))
  (2 2
     (:REWRITE
          CDR-OF-UBYTE3-LIST-FIX-X-NORMALIZE-CONST-UNDER-UBYTE3-LIST-EQUIV))
  (1 1
     (:REWRITE
          CONS-OF-UBYTE3-LIST-FIX-Y-NORMALIZE-CONST-UNDER-UBYTE3-LIST-EQUIV))
  (1 1
     (:REWRITE CONS-OF-UBYTE3-FIX-X-NORMALIZE-CONST-UNDER-UBYTE3-LIST-EQUIV))
  (1 1
     (:REWRITE CAR-OF-UBYTE3-LIST-FIX-X-NORMALIZE-CONST-UNDER-UBYTE3-EQUIV)))
(UBYTE3-LIST-FIX-OF-REPEAT
 (20 2
     (:REWRITE UBYTE3-LIST-FIX-WHEN-UBYTE3-LISTP))
 (16 4 (:REWRITE UBYTE3-FIX-WHEN-UBYTE3P))
 (12 2 (:REWRITE UBYTE3-LISTP-OF-REPEAT))
 (10 10 (:TYPE-PRESCRIPTION UBYTE3P))
 (10 10
     (:REWRITE UBYTE3P-WHEN-MEMBER-EQUAL-OF-UBYTE3-LISTP))
 (2 2 (:TYPE-PRESCRIPTION UBYTE3-LISTP))
 (1 1
    (:REWRITE
         CONS-OF-UBYTE3-LIST-FIX-Y-NORMALIZE-CONST-UNDER-UBYTE3-LIST-EQUIV))
 (1 1
    (:REWRITE CONS-OF-UBYTE3-FIX-X-NORMALIZE-CONST-UNDER-UBYTE3-LIST-EQUIV)))
(UBYTE3-LISTP-FORWARD-UNSIGNED-BYTE-LISTP)
(UBYTE3-LISTP-REWRITE-UNSIGNED-BYTE-LISTP)
(UNSIGNED-BYTE-LISTP-REWRITE-UBYTE3-LISTP)
(TRUE-LISTP-WHEN-UBYTE3-LISTP-REWRITE (2 2 (:DEFINITION TRUE-LISTP)))
(UBYTE3-LIST-FIX-OF-TAKE)
(UBYTE3-LIST-FIX-OF-RCONS)
