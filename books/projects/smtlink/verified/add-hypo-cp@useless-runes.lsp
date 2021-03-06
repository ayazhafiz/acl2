(APPLY-FOR-DEFEVALUATOR)
(SMT::EV-ADD-HYPO)
(EVAL-LIST-KWOTE-LST)
(TRUE-LIST-FIX-EV-LST)
(EV-COMMUTES-CAR)
(EV-LST-COMMUTES-CDR)
(SMT::EV-ADD-HYPO-CONSTRAINT-0)
(SMT::EV-ADD-HYPO-CONSTRAINT-1)
(SMT::EV-ADD-HYPO-CONSTRAINT-2)
(SMT::EV-ADD-HYPO-CONSTRAINT-3)
(SMT::EV-ADD-HYPO-CONSTRAINT-4)
(SMT::EV-ADD-HYPO-CONSTRAINT-5)
(SMT::EV-ADD-HYPO-CONSTRAINT-6)
(SMT::EV-ADD-HYPO-CONSTRAINT-7)
(SMT::EV-ADD-HYPO-CONSTRAINT-8)
(SMT::EV-ADD-HYPO-CONSTRAINT-9)
(SMT::EV-ADD-HYPO-CONSTRAINT-10)
(SMT::EV-ADD-HYPO-DISJOIN-CONS)
(SMT::EV-ADD-HYPO-DISJOIN-WHEN-CONSP)
(SMT::EV-ADD-HYPO-DISJOIN-ATOM (1 1
                                  (:REWRITE SMT::EV-ADD-HYPO-CONSTRAINT-9)))
(SMT::EV-ADD-HYPO-DISJOIN-APPEND
     (23 23
         (:REWRITE SMT::EV-ADD-HYPO-CONSTRAINT-9))
     (23 23
         (:REWRITE SMT::EV-ADD-HYPO-CONSTRAINT-2)))
(SMT::EV-ADD-HYPO-CONJOIN-CONS)
(SMT::EV-ADD-HYPO-CONJOIN-WHEN-CONSP)
(SMT::EV-ADD-HYPO-CONJOIN-ATOM (1 1
                                  (:REWRITE SMT::EV-ADD-HYPO-CONSTRAINT-9)))
(SMT::EV-ADD-HYPO-CONJOIN-APPEND
     (23 23
         (:REWRITE SMT::EV-ADD-HYPO-CONSTRAINT-9))
     (23 23
         (:REWRITE SMT::EV-ADD-HYPO-CONSTRAINT-2)))
(SMT::EV-ADD-HYPO-CONJOIN-CLAUSES-CONS
     (100 50 (:DEFINITION DISJOIN))
     (50 50 (:DEFINITION DISJOIN2))
     (7 7
        (:REWRITE SMT::EV-ADD-HYPO-DISJOIN-ATOM))
     (5 5
        (:REWRITE SMT::EV-ADD-HYPO-CONJOIN-ATOM)))
(SMT::EV-ADD-HYPO-CONJOIN-CLAUSES-WHEN-CONSP
     (24 24
         (:REWRITE SMT::EV-ADD-HYPO-CONSTRAINT-9))
     (24 24
         (:REWRITE SMT::EV-ADD-HYPO-CONSTRAINT-2))
     (18 9 (:DEFINITION DISJOIN))
     (9 9
        (:REWRITE SMT::EV-ADD-HYPO-DISJOIN-ATOM))
     (9 9 (:DEFINITION DISJOIN2)))
(SMT::EV-ADD-HYPO-CONJOIN-CLAUSES-ATOM
     (1 1
        (:REWRITE SMT::EV-ADD-HYPO-CONSTRAINT-9)))
(SMT::EV-ADD-HYPO-CONJOIN-CLAUSES-APPEND
     (65 65
         (:REWRITE SMT::EV-ADD-HYPO-CONSTRAINT-9))
     (65 65
         (:REWRITE SMT::EV-ADD-HYPO-CONSTRAINT-2))
     (24 12 (:DEFINITION DISJOIN))
     (12 12
         (:REWRITE SMT::EV-ADD-HYPO-DISJOIN-ATOM))
     (12 12 (:DEFINITION DISJOIN2)))
(SMT::ADD-HYPO-SUBGOALS
 (300 6
      (:REWRITE LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (246 6 (:REWRITE SUBLISTP-WHEN-PREFIXP))
 (207 6 (:DEFINITION SYMBOL-LISTP))
 (180 12
      (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
 (153 114 (:REWRITE DEFAULT-CDR))
 (93 18
     (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (85 44 (:REWRITE DEFAULT-+-2))
 (84 6
     (:REWRITE TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP))
 (81 9 (:DEFINITION TRUE-LISTP))
 (72 3 (:DEFINITION TRUE-LIST-LISTP))
 (64 64 (:REWRITE DEFAULT-CAR))
 (60 9
     (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (60 6 (:REWRITE LEN-WHEN-PREFIXP))
 (44 44 (:REWRITE DEFAULT-+-1))
 (42 42
     (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (42 42
     (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (42 42 (:LINEAR LEN-WHEN-PREFIXP))
 (39 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FUNC-ALISTP))
 (33 6
     (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (30 30 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (30 15 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (30 12
     (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
 (27 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FTY-TYPES-P))
 (27 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FTY-INFO-ALIST-P))
 (27 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FTY-FIELD-ALIST-P))
 (26 13 (:REWRITE DEFAULT-<-1))
 (24 24 (:TYPE-PRESCRIPTION PREFIXP))
 (24 6 (:REWRITE SUBLISTP-WHEN-ATOM-RIGHT))
 (21 21
     (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (21 3
     (:REWRITE SMT::FUNC-ALISTP-OF-CDR-WHEN-FUNC-ALISTP))
 (20 13 (:REWRITE DEFAULT-<-2))
 (18 18
     (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (18 3
     (:REWRITE SMT::HINT-PAIR-LISTP-OF-CDR-WHEN-HINT-PAIR-LISTP))
 (17 17
     (:REWRITE SMT::HINT-PAIR-LISTP-WHEN-NOT-CONSP))
 (15 15 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (15 15 (:REWRITE SET::IN-SET))
 (15 15
     (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV))
 (15 3
     (:REWRITE SMT::FTY-TYPES-P-OF-CDR-WHEN-FTY-TYPES-P))
 (15 3
     (:REWRITE SMT::FTY-INFO-ALIST-P-OF-CDR-WHEN-FTY-INFO-ALIST-P))
 (15 3
     (:REWRITE SMT::FTY-FIELD-ALIST-P-OF-CDR-WHEN-FTY-FIELD-ALIST-P))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (12 12 (:TYPE-PRESCRIPTION SUBLISTP))
 (12 12
     (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
 (12 12 (:REWRITE PREFIXP-TRANSITIVE . 2))
 (12 12 (:REWRITE PREFIXP-TRANSITIVE . 1))
 (12 12
     (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
 (12 12
     (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
 (12 12
     (:REWRITE SMT::FUNC-ALISTP-WHEN-SUBSETP-EQUAL))
 (6 6
    (:REWRITE TRUE-LIST-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (6 6 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
 (6 6 (:REWRITE SUBLISTP-COMPLETE))
 (6 6
    (:REWRITE SMT::FUNC-ALISTP-WHEN-NOT-CONSP))
 (6 6
    (:REWRITE SMT::FTY-TYPES-P-WHEN-NOT-CONSP))
 (6 6
    (:REWRITE SMT::FTY-INFO-ALIST-P-WHEN-NOT-CONSP))
 (6 6
    (:REWRITE SMT::FTY-FIELD-ALIST-P-WHEN-NOT-CONSP))
 (6 3
    (:REWRITE TRUE-LIST-LISTP-OF-CDR-WHEN-TRUE-LIST-LISTP))
 (3 3
    (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (3 3 (:REWRITE SUBSETP-TRANS2))
 (3 3 (:REWRITE SUBSETP-TRANS))
 (3
  3
  (:REWRITE
   SMT::CDR-OF-HINT-PAIR-LIST-FIX-X-NORMALIZE-CONST-UNDER-HINT-PAIR-LIST-EQUIV))
 (1 1
    (:REWRITE
         SMT::HINT-PAIR->HINTS$INLINE-OF-HINT-PAIR-FIX-X-NORMALIZE-CONST)))
(SMT::PSEUDO-TERM-LIST-LISTP-OF-ADD-HYPO-SUBGOALS.LIST-OF-H-THM
 (749 5
      (:REWRITE SMT::EQUAL-FIXED-AND-X-OF-PSEUDO-TERMP))
 (216 6 (:DEFINITION SYMBOL-LISTP))
 (99 9 (:DEFINITION TRUE-LISTP))
 (93 90 (:REWRITE DEFAULT-CAR))
 (93 18
     (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (88 82 (:REWRITE DEFAULT-CDR))
 (84 6
     (:REWRITE TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP))
 (72 3 (:DEFINITION TRUE-LIST-LISTP))
 (60 9
     (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (54 54 (:TYPE-PRESCRIPTION LEN))
 (54 9 (:DEFINITION LENGTH))
 (51 51 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (45 9 (:DEFINITION LEN))
 (39 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FUNC-ALISTP))
 (36 36 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (33 6
     (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (30 30 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (30 30
     (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (30 30
     (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (30 30 (:LINEAR LEN-WHEN-PREFIXP))
 (30 15 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (27 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FTY-TYPES-P))
 (27 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FTY-INFO-ALIST-P))
 (27 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FTY-FIELD-ALIST-P))
 (25 25
     (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (21 21 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
 (21 3
     (:REWRITE SMT::FUNC-ALISTP-OF-CDR-WHEN-FUNC-ALISTP))
 (18 18
     (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (18 18
     (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (18 9 (:REWRITE DEFAULT-+-2))
 (18 3
     (:REWRITE SMT::HINT-PAIR-LIST-FIX-WHEN-HINT-PAIR-LISTP))
 (15 15 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (15 15 (:REWRITE SET::IN-SET))
 (15 15
     (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV))
 (15 15
     (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (15 3
     (:REWRITE SMT::FTY-TYPES-P-OF-CDR-WHEN-FTY-TYPES-P))
 (15 3
     (:REWRITE SMT::FTY-INFO-ALIST-P-OF-CDR-WHEN-FTY-INFO-ALIST-P))
 (15 3
     (:REWRITE SMT::FTY-FIELD-ALIST-P-OF-CDR-WHEN-FTY-FIELD-ALIST-P))
 (12 12
     (:TYPE-PRESCRIPTION SMT::FUNC-ALISTP))
 (12 12
     (:TYPE-PRESCRIPTION SMT::FTY-TYPES-P))
 (12 12
     (:TYPE-PRESCRIPTION SMT::FTY-INFO-ALIST-P))
 (12 12
     (:TYPE-PRESCRIPTION SMT::FTY-FIELD-ALIST-P))
 (12 12
     (:REWRITE SMT::FUNC-ALISTP-WHEN-SUBSETP-EQUAL))
 (9 9 (:REWRITE DEFAULT-+-1))
 (6 6
    (:REWRITE TRUE-LIST-LISTP-WHEN-NOT-CONSP))
 (6 6
    (:REWRITE SMT::HINT-PAIR-LISTP-WHEN-SUBSETP-EQUAL))
 (6 6
    (:REWRITE SMT::FUNC-ALISTP-WHEN-NOT-CONSP))
 (6 6
    (:REWRITE SMT::FTY-TYPES-P-WHEN-NOT-CONSP))
 (6 6
    (:REWRITE SMT::FTY-INFO-ALIST-P-WHEN-NOT-CONSP))
 (6 6
    (:REWRITE SMT::FTY-FIELD-ALIST-P-WHEN-NOT-CONSP))
 (6 3
    (:REWRITE TRUE-LIST-LISTP-OF-CDR-WHEN-TRUE-LIST-LISTP))
 (5 5
    (:TYPE-PRESCRIPTION SMT::HINT-PAIR-LISTP))
 (4
  4
  (:REWRITE SMT::HINT-PAIR->HINTS$INLINE-OF-HINT-PAIR-FIX-X-NORMALIZE-CONST))
 (4
  4
  (:REWRITE
     SMT::CAR-OF-HINT-PAIR-LIST-FIX-X-NORMALIZE-CONST-UNDER-HINT-PAIR-EQUIV))
 (4 3
    (:REWRITE SMT::HINT-PAIR-LISTP-WHEN-NOT-CONSP))
 (2
   2
   (:REWRITE SMT::HINT-PAIR->THM$INLINE-OF-HINT-PAIR-FIX-X-NORMALIZE-CONST)))
(SMT::PSEUDO-TERM-LISTP-OF-ADD-HYPO-SUBGOALS.LIST-OF-NOT-HS
 (747 3
      (:REWRITE SMT::EQUAL-FIXED-AND-X-OF-PSEUDO-TERMP))
 (216 6 (:DEFINITION SYMBOL-LISTP))
 (99 9 (:DEFINITION TRUE-LISTP))
 (93 18
     (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (84 6
     (:REWRITE TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP))
 (80 77 (:REWRITE DEFAULT-CAR))
 (75 69 (:REWRITE DEFAULT-CDR))
 (72 3 (:DEFINITION TRUE-LIST-LISTP))
 (60 9
     (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (54 54 (:TYPE-PRESCRIPTION LEN))
 (54 9 (:DEFINITION LENGTH))
 (51 51 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (45 9 (:DEFINITION LEN))
 (39 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FUNC-ALISTP))
 (36 36 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (33 6
     (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (30 30 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (30 30
     (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (30 30
     (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (30 30 (:LINEAR LEN-WHEN-PREFIXP))
 (30 15 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (27 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FTY-TYPES-P))
 (27 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FTY-INFO-ALIST-P))
 (27 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FTY-FIELD-ALIST-P))
 (22 22
     (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (21 21 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
 (21 3
     (:REWRITE SMT::FUNC-ALISTP-OF-CDR-WHEN-FUNC-ALISTP))
 (18 18
     (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (18 9 (:REWRITE DEFAULT-+-2))
 (18 3
     (:REWRITE SMT::HINT-PAIR-LIST-FIX-WHEN-HINT-PAIR-LISTP))
 (16 16
     (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (15 15 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (15 15 (:REWRITE SET::IN-SET))
 (15 15
     (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV))
 (15 15
     (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (15 3
     (:REWRITE SMT::FTY-TYPES-P-OF-CDR-WHEN-FTY-TYPES-P))
 (15 3
     (:REWRITE SMT::FTY-INFO-ALIST-P-OF-CDR-WHEN-FTY-INFO-ALIST-P))
 (15 3
     (:REWRITE SMT::FTY-FIELD-ALIST-P-OF-CDR-WHEN-FTY-FIELD-ALIST-P))
 (12 12
     (:TYPE-PRESCRIPTION SMT::FUNC-ALISTP))
 (12 12
     (:TYPE-PRESCRIPTION SMT::FTY-TYPES-P))
 (12 12
     (:TYPE-PRESCRIPTION SMT::FTY-INFO-ALIST-P))
 (12 12
     (:TYPE-PRESCRIPTION SMT::FTY-FIELD-ALIST-P))
 (12 12
     (:REWRITE SMT::FUNC-ALISTP-WHEN-SUBSETP-EQUAL))
 (9 9 (:REWRITE DEFAULT-+-1))
 (6 6
    (:REWRITE TRUE-LIST-LISTP-WHEN-NOT-CONSP))
 (6 6
    (:REWRITE SMT::HINT-PAIR-LISTP-WHEN-SUBSETP-EQUAL))
 (6 6
    (:REWRITE SMT::FUNC-ALISTP-WHEN-NOT-CONSP))
 (6 6
    (:REWRITE SMT::FTY-TYPES-P-WHEN-NOT-CONSP))
 (6 6
    (:REWRITE SMT::FTY-INFO-ALIST-P-WHEN-NOT-CONSP))
 (6 6
    (:REWRITE SMT::FTY-FIELD-ALIST-P-WHEN-NOT-CONSP))
 (6 3
    (:REWRITE TRUE-LIST-LISTP-OF-CDR-WHEN-TRUE-LIST-LISTP))
 (5 5
    (:TYPE-PRESCRIPTION SMT::HINT-PAIR-LISTP))
 (4 3
    (:REWRITE SMT::HINT-PAIR-LISTP-WHEN-NOT-CONSP))
 (3 3
    (:REWRITE SMT::HINT-PAIR->THM$INLINE-OF-HINT-PAIR-FIX-X-NORMALIZE-CONST))
 (2
  2
  (:REWRITE
     SMT::CAR-OF-HINT-PAIR-LIST-FIX-X-NORMALIZE-CONST-UNDER-HINT-PAIR-EQUIV))
 (1 1
    (:REWRITE
         SMT::HINT-PAIR->HINTS$INLINE-OF-HINT-PAIR-FIX-X-NORMALIZE-CONST)))
(SMT::ADD-HYPO-SUBGOALS-CORRECTNESS
 (546 3 (:DEFINITION PSEUDO-TERMP))
 (207 6 (:DEFINITION SYMBOL-LISTP))
 (131 131 (:REWRITE DEFAULT-CAR))
 (96 96 (:REWRITE DEFAULT-CDR))
 (93 18
     (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (84 6
     (:REWRITE TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP))
 (81 9 (:DEFINITION TRUE-LISTP))
 (72 3 (:DEFINITION TRUE-LIST-LISTP))
 (60 9
     (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (54 42
     (:REWRITE SMT::EV-ADD-HYPO-CONSTRAINT-9))
 (54 9 (:DEFINITION LENGTH))
 (50 38
     (:REWRITE SMT::EV-ADD-HYPO-CONSTRAINT-3))
 (45 9 (:DEFINITION LEN))
 (39 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FUNC-ALISTP))
 (33 6
     (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (32 8
     (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (30 30 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (30 15 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (29 29
     (:REWRITE SMT::EV-ADD-HYPO-CONSTRAINT-1))
 (27 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FTY-TYPES-P))
 (27 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FTY-INFO-ALIST-P))
 (27 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FTY-FIELD-ALIST-P))
 (23 23
     (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV))
 (21 21 (:TYPE-PRESCRIPTION LEN))
 (21 3
     (:REWRITE SMT::FUNC-ALISTP-OF-CDR-WHEN-FUNC-ALISTP))
 (20
    20
    (:REWRITE SMT::HINT-PAIR->THM$INLINE-OF-HINT-PAIR-FIX-X-NORMALIZE-CONST))
 (20
  20
  (:REWRITE SMT::HINT-PAIR->HINTS$INLINE-OF-HINT-PAIR-FIX-X-NORMALIZE-CONST))
 (18 18
     (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (18 18
     (:REWRITE SMT::EV-ADD-HYPO-DISJOIN-ATOM))
 (18 9 (:REWRITE DEFAULT-+-2))
 (16 16
     (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (15 15 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (15 15 (:REWRITE SET::IN-SET))
 (15 3
     (:REWRITE SMT::FTY-TYPES-P-OF-CDR-WHEN-FTY-TYPES-P))
 (15 3
     (:REWRITE SMT::FTY-INFO-ALIST-P-OF-CDR-WHEN-FTY-INFO-ALIST-P))
 (15 3
     (:REWRITE SMT::FTY-FIELD-ALIST-P-OF-CDR-WHEN-FTY-FIELD-ALIST-P))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (12 12
     (:REWRITE SMT::FUNC-ALISTP-WHEN-SUBSETP-EQUAL))
 (10 10
     (:REWRITE SMT::EV-ADD-HYPO-CONJOIN-CLAUSES-ATOM))
 (9 9 (:REWRITE DEFAULT-+-1))
 (8 8
    (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (6 6
    (:REWRITE TRUE-LIST-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (6 6
    (:REWRITE SMT::FUNC-ALISTP-WHEN-NOT-CONSP))
 (6 6
    (:REWRITE SMT::FTY-TYPES-P-WHEN-NOT-CONSP))
 (6 6
    (:REWRITE SMT::FTY-INFO-ALIST-P-WHEN-NOT-CONSP))
 (6 6
    (:REWRITE SMT::FTY-FIELD-ALIST-P-WHEN-NOT-CONSP))
 (6 3
    (:REWRITE TRUE-LIST-LISTP-OF-CDR-WHEN-TRUE-LIST-LISTP))
 (3 3
    (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (3 3
    (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP)))
(SMT::CROCK0
 (322 1 (:DEFINITION PSEUDO-TERMP))
 (112 4 (:DEFINITION SYMBOL-LISTP))
 (104 6
      (:REWRITE TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP))
 (97 3 (:DEFINITION TRUE-LIST-LISTP))
 (60 6 (:DEFINITION TRUE-LISTP))
 (59 57 (:REWRITE DEFAULT-CAR))
 (58 48 (:REWRITE DEFAULT-CDR))
 (57 12
     (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (56 7
     (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (32 32
     (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (22 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FUNC-ALISTP))
 (19 5
     (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (18 18 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (18 18
     (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (18 9 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (18 3 (:DEFINITION LENGTH))
 (16 16 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (16 4 (:REWRITE CAR-OF-APPEND))
 (16 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FTY-TYPES-P))
 (16 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FTY-INFO-ALIST-P))
 (16 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FTY-FIELD-ALIST-P))
 (15 3 (:DEFINITION LEN))
 (10 10
     (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (10 10
     (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV))
 (9 9 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (9 9 (:REWRITE SET::IN-SET))
 (9 1
    (:REWRITE SMT::FUNC-ALISTP-OF-CDR-WHEN-FUNC-ALISTP))
 (8 4
    (:REWRITE TRUE-LIST-LISTP-OF-CDR-WHEN-TRUE-LIST-LISTP))
 (7 7 (:TYPE-PRESCRIPTION LEN))
 (7 1
    (:REWRITE SMT::FTY-TYPES-P-OF-CDR-WHEN-FTY-TYPES-P))
 (7 1
    (:REWRITE SMT::FTY-INFO-ALIST-P-OF-CDR-WHEN-FTY-INFO-ALIST-P))
 (7 1
    (:REWRITE SMT::FTY-FIELD-ALIST-P-OF-CDR-WHEN-FTY-FIELD-ALIST-P))
 (6 6
    (:REWRITE TRUE-LIST-LISTP-WHEN-NOT-CONSP))
 (6 6
    (:REWRITE SMT::FUNC-ALISTP-WHEN-SUBSETP-EQUAL))
 (6 3 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE CDR-OF-APPEND-WHEN-CONSP))
 (3 3
    (:REWRITE SMT::FUNC-ALISTP-WHEN-NOT-CONSP))
 (3 3
    (:REWRITE SMT::FTY-TYPES-P-WHEN-NOT-CONSP))
 (3 3
    (:REWRITE SMT::FTY-INFO-ALIST-P-WHEN-NOT-CONSP))
 (3 3
    (:REWRITE SMT::FTY-FIELD-ALIST-P-WHEN-NOT-CONSP))
 (3 3 (:REWRITE DEFAULT-+-1)))
(SMT::CROCK1
 (322 1 (:DEFINITION PSEUDO-TERMP))
 (112 4 (:DEFINITION SYMBOL-LISTP))
 (104 6
      (:REWRITE TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP))
 (97 3 (:DEFINITION TRUE-LIST-LISTP))
 (60 6 (:DEFINITION TRUE-LISTP))
 (57 12
     (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (56 7
     (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (53 43 (:REWRITE DEFAULT-CDR))
 (50 48 (:REWRITE DEFAULT-CAR))
 (23 23
     (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (22 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FUNC-ALISTP))
 (19 5
     (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (18 18 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (18 9 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (18 3 (:DEFINITION LENGTH))
 (16 16 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (16 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FTY-TYPES-P))
 (16 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FTY-INFO-ALIST-P))
 (16 3
     (:REWRITE SMT::SYMBOLP-OF-CAAR-WHEN-FTY-FIELD-ALIST-P))
 (15 3 (:DEFINITION LEN))
 (14 14
     (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (10 10
     (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (10 10
     (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV))
 (9 9 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (9 9 (:REWRITE SET::IN-SET))
 (9 1
    (:REWRITE SMT::FUNC-ALISTP-OF-CDR-WHEN-FUNC-ALISTP))
 (8 4
    (:REWRITE TRUE-LIST-LISTP-OF-CDR-WHEN-TRUE-LIST-LISTP))
 (8 4 (:REWRITE CAR-OF-APPEND))
 (7 7 (:TYPE-PRESCRIPTION LEN))
 (7 7 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (7 1
    (:REWRITE SMT::FTY-TYPES-P-OF-CDR-WHEN-FTY-TYPES-P))
 (7 1
    (:REWRITE SMT::FTY-INFO-ALIST-P-OF-CDR-WHEN-FTY-INFO-ALIST-P))
 (7 1
    (:REWRITE SMT::FTY-FIELD-ALIST-P-OF-CDR-WHEN-FTY-FIELD-ALIST-P))
 (6 6
    (:REWRITE TRUE-LIST-LISTP-WHEN-NOT-CONSP))
 (6 6
    (:REWRITE SMT::FUNC-ALISTP-WHEN-SUBSETP-EQUAL))
 (6 3 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE CDR-OF-APPEND-WHEN-CONSP))
 (3 3
    (:REWRITE SMT::FUNC-ALISTP-WHEN-NOT-CONSP))
 (3 3
    (:REWRITE SMT::FTY-TYPES-P-WHEN-NOT-CONSP))
 (3 3
    (:REWRITE SMT::FTY-INFO-ALIST-P-WHEN-NOT-CONSP))
 (3 3
    (:REWRITE SMT::FTY-FIELD-ALIST-P-WHEN-NOT-CONSP))
 (3 3 (:REWRITE DEFAULT-+-1)))
(SMT::ADD-HYPO-CP)
(SMT::PSEUDO-TERM-LIST-LISTP-OF-ADD-HYPO-CP
 (24 6
     (:REWRITE SMT::SMTLINK-HINT-P-WHEN-MAYBE-SMTLINK-HINT-P))
 (18 16 (:REWRITE DEFAULT-CDR))
 (17 15 (:REWRITE DEFAULT-CAR))
 (15 3
     (:REWRITE SMT::MAYBE-SMTLINK-HINT-P-WHEN-SMTLINK-HINT-P))
 (14 14
     (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (11 11
     (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (9 9
    (:TYPE-PRESCRIPTION SMT::MAYBE-SMTLINK-HINT-P))
 (8 2 (:DEFINITION BINARY-APPEND))
 (4 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (3
  3
  (:REWRITE
   SMT::SMTLINK-HINT->HYPOTHESES$INLINE-OF-SMTLINK-HINT-FIX-X-NORMALIZE-CONST)))
(SMT::CORRECTNESS-OF-ADD-HYPOS
 (32 8
     (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (24 6
     (:REWRITE SMT::SMTLINK-HINT-P-WHEN-MAYBE-SMTLINK-HINT-P))
 (20 20 (:REWRITE DEFAULT-CAR))
 (19 16
     (:REWRITE SMT::EV-ADD-HYPO-CONSTRAINT-3))
 (18 16
     (:REWRITE SMT::EV-ADD-HYPO-CONSTRAINT-9))
 (18 16
     (:REWRITE SMT::EV-ADD-HYPO-CONSTRAINT-8))
 (16 16
     (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (15 3
     (:REWRITE SMT::MAYBE-SMTLINK-HINT-P-WHEN-SMTLINK-HINT-P))
 (14 14
     (:REWRITE SMT::EV-ADD-HYPO-CONSTRAINT-1))
 (14 14 (:REWRITE DEFAULT-CDR))
 (14 12
     (:REWRITE SMT::EV-ADD-HYPO-DISJOIN-ATOM))
 (12 3 (:DEFINITION BINARY-APPEND))
 (10 10
     (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (9 9
    (:TYPE-PRESCRIPTION SMT::MAYBE-SMTLINK-HINT-P))
 (8 8
    (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (7
  7
  (:REWRITE
   SMT::SMTLINK-HINT->HYPOTHESES$INLINE-OF-SMTLINK-HINT-FIX-X-NORMALIZE-CONST))
 (6 6 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (5 5 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (5 5
    (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV))
 (4 4
    (:REWRITE SMT::EV-ADD-HYPO-CONJOIN-CLAUSES-ATOM))
 (1 1
    (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (1 1 (:TYPE-PRESCRIPTION BINARY-APPEND)))
