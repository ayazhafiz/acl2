(RP::RP-RW-META-RULE-MAIN-VALID-EVAL
     (834 3 (:DEFINITION RP::RP-TERMP))
     (641 599 (:REWRITE DEFAULT-CDR))
     (597 3 (:DEFINITION RP::FALIST-CONSISTENT))
     (575 5 (:DEFINITION RP::EVAL-AND-ALL))
     (568 484 (:REWRITE DEFAULT-CAR))
     (562 14 (:DEFINITION RP::RP-TRANS))
     (557 52 (:DEFINITION RP::INCLUDE-FNC))
     (462 3
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (421 29
          (:REWRITE RP::NOT-INCLUDE-RP-MEANS-VALID-SC))
     (298 69 (:REWRITE O-P-O-INFP-CAR))
     (252 14 (:DEFINITION RP::TRANS-LIST))
     (188 14
          (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
     (180 180
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (172 75 (:DEFINITION QUOTEP))
     (148 148
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (126 126
          (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
     (120 10
          (:REWRITE RP::NOT-INCLUDE-RP-MEANS-VALID-SC-LST))
     (112 14 (:DEFINITION RP::IS-FALIST))
     (106 11 (:REWRITE RP::NOT-INCLUDE-RP))
     (103 63 (:REWRITE O-P-DEF-O-FINP-1))
     (93 3 (:DEFINITION RP::VALID-SC-SUBTERMS))
     (90 10
         (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (60 4 (:DEFINITION RP::EX-FROM-RP))
     (58 58
         (:TYPE-PRESCRIPTION RP::RP-STAT-ADD-TO-RULES-USED))
     (56 56 (:REWRITE RP::CONSP-RP-TRANS-LST))
     (48 12 (:REWRITE RP::IS-IF-RP-TERMP))
     (44 16 (:REWRITE RP::RP-EVL-OF-VARIABLE))
     (41 20
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (40 40 (:TYPE-PRESCRIPTION O-FINP))
     (39 3 (:DEFINITION RP::RP-TERM-LISTP))
     (37 37
         (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (36 36 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (36 6
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (33 3 (:REWRITE RP::NOT-INCLUDE-EX-FROM-RP))
     (24 6
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (24 6 (:REWRITE RP::RP-TERMP-CADR))
     (24 6 (:REWRITE RP::RP-TERMP-CADDR))
     (20 20
         (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP))
     (20 20
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (16 16 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (16 16 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (16 16 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (16 16 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (16 16
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (16 16 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (16 16 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (16 16 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (16 16
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (16 16 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (16 16 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (16 16 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (16 16 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (16 16 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
     (16 16 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (16 16 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (16 16 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (16 16 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (16 16 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (16 16 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (16 16 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (16 16 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (16 16
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (16 16 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (16 12 (:REWRITE RP::VALID-SC-CADR))
     (15 3 (:REWRITE RP::VALID-SC-OF-EX-FROM-RP))
     (12 8 (:REWRITE RP::VALID-SC-CADDR))
     (12 3
         (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (9 9 (:TYPE-PRESCRIPTION QUOTEP))
     (8 4 (:REWRITE RP::VALID-SC-CADDDR))
     (3 3
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (3 3
        (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-RP-STATEP))
     (3 3
        (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-ALISTP))
     (3 3
        (:REWRITE RP::CAR-OF-EX-FROM-RP-IS-NOT-RP)))
(RP::RP-RW-META-RULE-MAIN-VALID-RP-TERMP
     (770 5
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (524 524 (:REWRITE DEFAULT-CDR))
     (371 371 (:REWRITE DEFAULT-CAR))
     (210 60 (:REWRITE O-P-O-INFP-CAR))
     (78 20 (:REWRITE RP::IS-IF-RP-TERMP))
     (50 50 (:REWRITE O-P-DEF-O-FINP-1))
     (36 9 (:REWRITE RP::RP-TERMP-CADR))
     (30 5 (:REWRITE RP::NOT-INCLUDE-RP))
     (25 25 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (20 5 (:DEFINITION RP::INCLUDE-FNC))
     (19 19
         (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (16 4
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (9 9
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (5 5 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (4 4
        (:TYPE-PRESCRIPTION RP::IS-IF$INLINE)))
(RP::RP-RW-META-RULE-MAIN-VALID-DONT-RW-SYNTAXP)
(RP::RP-RW-META-RULE-MAIN-VALID-RP-STATE-PRESERVEDP
     (18 18 (:REWRITE DEFAULT-CDR))
     (9 9 (:REWRITE DEFAULT-CAR))
     (3 3
        (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-RP-STATEP))
     (3 3
        (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-ALISTP)))
(RP::VALID-RP-STATE-SYNTAXP-IMPLIES-RP-STATEP)
(RP::VALID-RP-STATE-SYNTAXP-RP-RW-META-RULE-MAIN
     (18 18 (:REWRITE DEFAULT-CDR))
     (9 9 (:REWRITE DEFAULT-CAR)))
(RP::VALID-RP-STATEP-RP-RW-META-RULE-MAIN
     (4 1
        (:REWRITE RP::VALID-RP-STATE-SYNTAXP-IMPLIES-RP-STATEP))
     (2 2
        (:TYPE-PRESCRIPTION RP::VALID-RP-STATE-SYNTAXP))
     (1 1 (:REWRITE RP::VALID-RP-STATEP-NECC))
     (1 1
        (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-VALID-RP-STATE-SYNTAXP))
     (1 1
        (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-RP-STATEP))
     (1 1
        (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-ALISTP)))
