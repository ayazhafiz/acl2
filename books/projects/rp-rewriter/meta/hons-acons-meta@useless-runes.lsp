(RP::UNQUOTE-FALIST-KEYS (75 36 (:REWRITE DEFAULT-+-2))
                         (47 36 (:REWRITE DEFAULT-+-1))
                         (39 33 (:REWRITE DEFAULT-CDR))
                         (32 32 (:REWRITE DEFAULT-CAR))
                         (30 2 (:DEFINITION LENGTH))
                         (30 1 (:REWRITE O<=-O-FINP-DEF))
                         (22 2 (:DEFINITION LEN))
                         (16 4 (:DEFINITION INTEGER-ABS))
                         (12 3 (:REWRITE O-P-O-INFP-CAR))
                         (7 5 (:REWRITE DEFAULT-<-2))
                         (6 6
                            (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                         (6 5 (:REWRITE DEFAULT-<-1))
                         (6 4 (:REWRITE STR::CONSP-OF-EXPLODE))
                         (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
                         (4 4
                            (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
                         (4 2
                            (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                         (4 1 (:REWRITE AC-<))
                         (3 3 (:REWRITE O-P-DEF-O-FINP-1))
                         (3 3
                            (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
                         (2 2 (:TYPE-PRESCRIPTION LEN))
                         (2 2
                            (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                         (2 2 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                         (2 2 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                         (2 2 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                         (2 2
                            (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                         (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                         (2 2
                            (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                         (2 2 (:REWRITE DEFAULT-REALPART))
                         (2 2 (:REWRITE DEFAULT-NUMERATOR))
                         (2 2 (:REWRITE DEFAULT-IMAGPART))
                         (2 2 (:REWRITE DEFAULT-DENOMINATOR))
                         (2 2
                            (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
                         (2 2
                            (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
                         (2 1 (:REWRITE O-INFP-O-FINP-O<=))
                         (1 1
                            (:TYPE-PRESCRIPTION RP::UNQUOTE-FALIST-KEYS))
                         (1 1
                            (:REWRITE |a < b & b < c  =>  a < c|)))
(RP::QUOTE-FALIST-VALS (75 36 (:REWRITE DEFAULT-+-2))
                       (47 36 (:REWRITE DEFAULT-+-1))
                       (32 26 (:REWRITE DEFAULT-CDR))
                       (30 2 (:DEFINITION LENGTH))
                       (30 1 (:REWRITE O<=-O-FINP-DEF))
                       (22 2 (:DEFINITION LEN))
                       (19 19 (:REWRITE DEFAULT-CAR))
                       (16 4 (:DEFINITION INTEGER-ABS))
                       (8 2 (:REWRITE O-P-O-INFP-CAR))
                       (7 5 (:REWRITE DEFAULT-<-2))
                       (6 6
                          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                       (6 5 (:REWRITE DEFAULT-<-1))
                       (6 4 (:REWRITE STR::CONSP-OF-EXPLODE))
                       (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
                       (4 4
                          (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
                       (4 2
                          (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                       (4 1 (:REWRITE AC-<))
                       (3 3
                          (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
                       (2 2 (:TYPE-PRESCRIPTION LEN))
                       (2 2
                          (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                       (2 2 (:REWRITE O-P-DEF-O-FINP-1))
                       (2 2 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                       (2 2 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                       (2 2 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                       (2 2
                          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                       (2 2
                          (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                       (2 2 (:REWRITE DEFAULT-REALPART))
                       (2 2 (:REWRITE DEFAULT-NUMERATOR))
                       (2 2 (:REWRITE DEFAULT-IMAGPART))
                       (2 2 (:REWRITE DEFAULT-DENOMINATOR))
                       (2 2
                          (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
                       (2 2
                          (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
                       (2 1 (:REWRITE O-INFP-O-FINP-O<=))
                       (1 1
                          (:TYPE-PRESCRIPTION RP::QUOTE-FALIST-VALS))
                       (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
                       (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::HONS-ACONS-META (343 21 (:REWRITE RP::IS-IF-RP-TERMP))
                     (208 204 (:REWRITE DEFAULT-CDR))
                     (155 155 (:REWRITE DEFAULT-CAR))
                     (118 19
                          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
                     (53 19
                         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                     (52 13 (:REWRITE O-P-O-INFP-CAR))
                     (35 1 (:DEFINITION RP::FALIST-CONSISTENT))
                     (30 12 (:REWRITE RP::RP-TERMP-CADR))
                     (24 1 (:DEFINITION RP::EX-FROM-RP))
                     (18 6 (:DEFINITION APPLY$-BADGEP))
                     (15 3
                         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
                     (15 3
                         (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
                     (15 1 (:REWRITE RP::NOT-INCLUDE-RP))
                     (13 13 (:REWRITE O-P-DEF-O-FINP-1))
                     (13 13 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                     (12 6 (:DEFINITION WEAK-APPLY$-BADGE-P))
                     (12 1 (:DEFINITION RP::INCLUDE-FNC))
                     (10 2
                         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                     (8 2 (:REWRITE RP::RP-TERMP-CADDR))
                     (6 6 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                     (4 4 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
                     (3 3 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
                     (2 2
                        (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
                     (2 2
                        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP)))
(RP::HONS-ACONS-META-FORMULA-CHECKS)
(RP::META-EXTRACT-FORMULA-HONS-ACONS-WHEN-HONS-ACONS-META-FORMULA-CHECKS)
(RP::RP-EVL-OF-HONS-ACONS-WHEN-HONS-ACONS-META-FORMULA-CHECKS
     (188 188 (:REWRITE DEFAULT-CAR))
     (50 44 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (50 44 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (50 44 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (50 44 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (50 44 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (50 44 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (50 44 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (50 44 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (50 44 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (50 44 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (50 44 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (50 44 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (50 44
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (50 44 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (48 42 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (48 42
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (48 42 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (48 42 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (48 42 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (47 41 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (47 41 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (22 22 (:REWRITE DEFAULT-CDR))
     (8 8
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (8 8
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (7 7
        (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF)))
(RP::LEMMA4 (1536 411 (:REWRITE O-P-O-INFP-CAR))
            (490 148 (:REWRITE RP::IS-IF-RP-TERMP))
            (445 83
                 (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
            (391 367 (:REWRITE O-P-DEF-O-FINP-1))
            (358 179 (:DEFINITION QUOTEP))
            (278 74 (:REWRITE RP::RP-TERMP-CADDR))
            (221 23
                 (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
            (217 217 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
            (212 212
                 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
            (188 74 (:REWRITE RP::RP-TERMP-CADR))
            (116 23
                 (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
            (83 83
                (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
            (52 4
                (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
            (44 4 (:DEFINITION APPLY$-BADGEP))
            (32 4 (:DEFINITION WEAK-APPLY$-BADGE-P))
            (24 24 (:TYPE-PRESCRIPTION O-FINP))
            (23 23 (:TYPE-PRESCRIPTION QUOTEP))
            (4 4 (:TYPE-PRESCRIPTION APPLY$-BADGEP)))
(RP::LEMMA5 (755 2 (:DEFINITION RP::RP-TERMP))
            (465 8 (:REWRITE RP::IS-IF-RP-TERMP))
            (408 8 (:DEFINITION RP::EX-FROM-RP))
            (346 10 (:DEFINITION RP::IS-RP$INLINE))
            (306 306 (:REWRITE DEFAULT-CDR))
            (234 2 (:DEFINITION RP::FALIST-CONSISTENT))
            (206 206 (:REWRITE DEFAULT-CAR))
            (154 1
                 (:DEFINITION RP::FALIST-CONSISTENT-AUX))
            (130 34 (:REWRITE O-P-O-INFP-CAR))
            (94 9 (:REWRITE RP::NOT-INCLUDE-RP))
            (68 9 (:DEFINITION RP::INCLUDE-FNC))
            (64 64 (:TYPE-PRESCRIPTION O-P))
            (64 13
                (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
            (32 32 (:REWRITE O-P-DEF-O-FINP-1))
            (26 26 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
            (25 25 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
            (20 1 (:DEFINITION RP::RP-TERM-LISTP))
            (17 3
                (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
            (16 16
                (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
            (13 13
                (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
            (10 2
                (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
            (8 8 (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
            (8 3
               (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
            (8 2 (:REWRITE RP::RP-TERMP-CADR))
            (8 2
               (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
            (6 2 (:DEFINITION APPLY$-BADGEP))
            (4 4 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
            (4 2 (:DEFINITION WEAK-APPLY$-BADGE-P))
            (2 2 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
            (1 1
               (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::LEMMA6 (38 38 (:REWRITE DEFAULT-CDR))
            (24 24 (:REWRITE DEFAULT-CAR))
            (20 5 (:REWRITE O-P-O-INFP-CAR))
            (8 8 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
            (5 5 (:REWRITE O-P-DEF-O-FINP-1)))
(RP::LEMMA2 (313 1 (:DEFINITION RP::RP-TERMP))
            (199 1 (:DEFINITION RP::FALIST-CONSISTENT))
            (184 184 (:REWRITE DEFAULT-CDR))
            (154 1
                 (:DEFINITION RP::FALIST-CONSISTENT-AUX))
            (153 3 (:DEFINITION RP::EX-FROM-RP))
            (144 4 (:DEFINITION RP::IS-RP$INLINE))
            (116 116 (:REWRITE DEFAULT-CAR))
            (74 20 (:REWRITE O-P-O-INFP-CAR))
            (39 4 (:REWRITE RP::NOT-INCLUDE-RP))
            (36 36 (:TYPE-PRESCRIPTION O-P))
            (29 6
                (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
            (28 4 (:DEFINITION RP::INCLUDE-FNC))
            (18 18 (:REWRITE O-P-DEF-O-FINP-1))
            (16 4 (:REWRITE RP::IS-IF-RP-TERMP))
            (13 13 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
            (10 10 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
            (10 5 (:DEFINITION QUOTEP))
            (8 8 (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
            (8 2 (:REWRITE RP::RP-TERMP-CADR))
            (8 2 (:REWRITE RP::RP-TERMP-CADDR))
            (7 1
               (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
            (6 6
               (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
            (6 6
               (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
            (4 1
               (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
            (1 1 (:TYPE-PRESCRIPTION QUOTEP))
            (1 1
               (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::LEMMA7 (248 247 (:REWRITE DEFAULT-CDR))
            (239 238 (:REWRITE DEFAULT-CAR))
            (104 35 (:REWRITE O-P-O-INFP-CAR))
            (23 23 (:REWRITE O-P-DEF-O-FINP-1))
            (4 4 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::RP-TERMP-HONS-ACONS-META
     (2773 2772 (:REWRITE DEFAULT-CDR))
     (1974 1973 (:REWRITE DEFAULT-CAR))
     (1817 49 (:DEFINITION RP::IS-RP$INLINE))
     (1711 29 (:DEFINITION RP::EX-FROM-RP))
     (1682 47
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (1242 327 (:REWRITE O-P-O-INFP-CAR))
     (1028 209 (:REWRITE RP::IS-IF-RP-TERMP))
     (655 91 (:REWRITE RP::RP-TERMP-CADR))
     (483 37 (:REWRITE RP::NOT-INCLUDE-RP))
     (467 80
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (428 47
          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (380 37 (:DEFINITION RP::INCLUDE-FNC))
     (305 305 (:REWRITE O-P-DEF-O-FINP-1))
     (304 85 (:REWRITE RP::RP-TERMP-CADDR))
     (234 84 (:DEFINITION QUOTEP))
     (180 60 (:DEFINITION APPLY$-BADGEP))
     (180 36
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (176 176 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (120 60 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (120 24
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (105 33 (:REWRITE RP::RP-TERMP-CADDDR))
     (95 95 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (80 80
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (60 60 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (58 58
         (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (52 2 (:DEFINITION RP::QUOTE-FALIST-VALS))
     (47 47 (:TYPE-PRESCRIPTION QUOTEP))
     (35 35
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (22 2 (:DEFINITION ALISTP))
     (3 3 (:TYPE-PRESCRIPTION BOOLEANP)))
(RP::LEMMA9-2)
(RP::LEMMA2 (125 107 (:REWRITE DEFAULT-CDR))
            (108 6 (:DEFINITION RP::TRANS-LIST))
            (98 62 (:REWRITE DEFAULT-CAR))
            (54 54
                (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
            (48 6
                (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
            (36 9 (:REWRITE O-P-O-INFP-CAR))
            (36 3 (:DEFINITION RP::INCLUDE-FNC))
            (24 24 (:REWRITE RP::CONSP-RP-TRANS-LST))
            (15 7 (:REWRITE RP::RP-EVL-OF-VARIABLE))
            (9 9 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
            (9 9 (:REWRITE O-P-DEF-O-FINP-1))
            (7 7 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
            (7 7
               (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
            (7 7
               (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
            (7 7
               (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
            (7 7
               (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
            (7 7
               (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
            (7 7
               (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
            (7 7
               (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-RP-CALL))
            (7 7
               (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
            (7 7
               (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
            (7 7
               (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-QUOTE))
            (7 7
               (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-LAMBDA))
            (7 7
               (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
            (7 7
               (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
            (7 7
               (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-IF-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
            (7 7
               (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
            (7 7
               (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
            (7 7
               (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
            (7 7
               (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
            (7 7
               (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
            (7 7
               (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
            (7 7
               (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
            (7 7
               (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
            (7 7
               (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
            (7 7 (:REWRITE RP::RP-EVL-OF-<-CALL))
            (6 6
               (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
            (6 6 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
            (4 4
               (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
            (4 4
               (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::RP-EVL-OF-HONS-ACONS-META
     (969 891 (:REWRITE DEFAULT-CAR))
     (893 722 (:REWRITE DEFAULT-CDR))
     (483 33 (:REWRITE RP::NOT-INCLUDE-RP))
     (436 39 (:DEFINITION RP::INCLUDE-FNC))
     (378 105 (:REWRITE O-P-O-INFP-CAR))
     (234 13 (:DEFINITION RP::TRANS-LIST))
     (117 117
          (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
     (117 117
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (91 91 (:REWRITE O-P-DEF-O-FINP-1))
     (78 78
         (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (74 10
         (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
     (60 2 (:DEFINITION RP::QUOTE-FALIST-VALS))
     (52 52 (:REWRITE RP::CONSP-RP-TRANS-LST))
     (48 30 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (48 30 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (48 30 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (48 30 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (48 30 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (48 30 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (48 30 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (48 30 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (48 30 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (48 30 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (48 30 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (48 30 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (48 30
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (48 30 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (41 13 (:REWRITE RP::LEMMA2))
     (34 14 (:REWRITE RP::RP-EVL-OF-VARIABLE))
     (30 24 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (30 24 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (30 24
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (30 24 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (30 24 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (30 24 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (30 24 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (22 2 (:DEFINITION ALISTP))
     (21 21 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (18 3
         (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (11 11
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (10 10
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (10 10
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (3 3 (:TYPE-PRESCRIPTION QUOTEP)))
(RP::LEMMA2 (56 6 (:DEFINITION RP::INCLUDE-FNC))
            (53 5
                (:REWRITE RP::NOT-INCLUDE-RP-MEANS-VALID-SC))
            (49 4
                (:REWRITE RP::NOT-INCLUDE-RP-MEANS-VALID-SC-LST))
            (37 4
                (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
            (37 1 (:DEFINITION RP::VALID-SC-SUBTERMS))
            (33 33 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
            (30 30
                (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
            (25 25 (:REWRITE DEFAULT-CAR))
            (22 22 (:REWRITE DEFAULT-CDR))
            (22 2 (:REWRITE RP::NOT-INCLUDE-RP))
            (12 6 (:DEFINITION QUOTEP))
            (8 2 (:REWRITE O-P-O-INFP-CAR))
            (5 1 (:REWRITE RP::VALID-SC-CADR))
            (4 4 (:TYPE-PRESCRIPTION O-P))
            (2 2 (:REWRITE O-P-DEF-O-FINP-1)))
(RP::VALID-SC-HONS-META
     (8119 141 (:DEFINITION RP::EX-FROM-RP))
     (6623 6569 (:REWRITE DEFAULT-CDR))
     (4878 4770 (:REWRITE DEFAULT-CAR))
     (4564 167 (:REWRITE RP::NOT-INCLUDE-RP))
     (3360 849 (:REWRITE O-P-O-INFP-CAR))
     (3316 5
           (:REWRITE RP::CAR-OF-EX-FROM-RP-IS-NOT-RP))
     (3277 35 (:DEFINITION RP::RP-TERMP))
     (2904 18 (:DEFINITION RP::RP-TERM-LISTP))
     (1664 124 (:REWRITE RP::IS-IF-RP-TERMP))
     (1567 50 (:REWRITE RP::RP-TERMP-CADDR))
     (1242 6 (:DEFINITION RP::FALIST-CONSISTENT))
     (1150 10 (:DEFINITION RP::EVAL-AND-ALL))
     (966 6
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (875 51 (:REWRITE RP::VALID-SC-CADR))
     (837 837 (:REWRITE O-P-DEF-O-FINP-1))
     (795 177
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (738 18 (:DEFINITION RP::RP-TRANS))
     (640 64
          (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (576 72 (:DEFINITION APPLY$-BADGEP))
     (449 43 (:REWRITE RP::VALID-SC-CADDR))
     (358 358 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (324 18 (:DEFINITION RP::TRANS-LIST))
     (290 18
          (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
     (282 43
          (:REWRITE RP::NOT-INCLUDE-EX-FROM-RP))
     (270 9 (:DEFINITION RP::QUOTE-FALIST-VALS))
     (210 42
          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (192 16 (:DEFINITION NATP))
     (177 177
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (162 162
          (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
     (160 72 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (144 144 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (139 62 (:REWRITE RP::RP-TERMP-CADR))
     (132 20 (:REWRITE RP::VALID-SC-CADDDR))
     (124 19
          (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (96 24
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (84 42
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (72 72 (:REWRITE RP::CONSP-RP-TRANS-LST))
     (61 61 (:TYPE-PRESCRIPTION QUOTEP))
     (56 24
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (54 54
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (54 18 (:REWRITE RP::RP-EVL-OF-VARIABLE))
     (48 48
         (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (48 24
         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (43 6 (:REWRITE RP::VALID-SC-OF-EX-FROM-RP))
     (40 40
         (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP))
     (24 24
         (:TYPE-PRESCRIPTION RP::VALID-SC-SUBTERMS))
     (24 24
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (24 12 (:REWRITE RP::RP-TERMP-CADDDR))
     (22 2 (:DEFINITION ALISTP))
     (18 18 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (18 18 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (18 18 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (18 18 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (18 18
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (18 18 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (18 18 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (18 18 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (18 18
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (18 18 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (18 18 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (18 18 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (18 18 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (18 18 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
     (18 18 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (18 18 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (18 18 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (18 18 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (18 18 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (18 18 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (18 18 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (18 18 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (18 18
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (18 18 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (10 10
         (:TYPE-PRESCRIPTION RP::EVAL-AND-ALL))
     (8 8 (:REWRITE DEFAULT-<-2))
     (8 8 (:REWRITE DEFAULT-<-1))
     (6 6 (:TYPE-PRESCRIPTION BOOLEANP)))
(RP::DONT-RW-SYNTAXP-HONS-ACONS-META)
(RP::HONS-ACONS-META_FOR_HONS-ACONS_VALID
     (556 2 (:DEFINITION RP::RP-TERMP))
     (398 2 (:DEFINITION RP::FALIST-CONSISTENT))
     (391 1 (:DEFINITION RP::VALID-SC))
     (308 2
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (301 286 (:REWRITE DEFAULT-CDR))
     (245 215 (:REWRITE DEFAULT-CAR))
     (195 5 (:DEFINITION RP::RP-TRANS))
     (139 14 (:DEFINITION RP::INCLUDE-FNC))
     (122 31 (:REWRITE O-P-O-INFP-CAR))
     (115 1 (:DEFINITION RP::EVAL-AND-ALL))
     (101 7
          (:REWRITE RP::NOT-INCLUDE-RP-MEANS-VALID-SC))
     (90 5 (:DEFINITION RP::TRANS-LIST))
     (54 54 (:TYPE-PRESCRIPTION O-P))
     (50 22 (:DEFINITION QUOTEP))
     (46 4
         (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
     (45 45
         (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
     (41 41 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (40 5 (:DEFINITION RP::IS-FALIST))
     (37 27 (:REWRITE O-P-DEF-O-FINP-1))
     (34 4 (:REWRITE RP::NOT-INCLUDE-RP))
     (32 8 (:REWRITE RP::IS-IF-RP-TERMP))
     (29 29
         (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (22 8
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (20 20 (:REWRITE RP::CONSP-RP-TRANS-LST))
     (16 16 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (16 4 (:REWRITE RP::RP-TERMP-CADR))
     (16 4 (:REWRITE RP::RP-TERMP-CADDR))
     (15 1 (:REWRITE RP::VALID-SC-EX-FROM-RP))
     (15 1 (:DEFINITION RP::EX-FROM-RP))
     (14 2
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (13 13
         (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (13 5 (:REWRITE RP::RP-EVL-OF-VARIABLE))
     (12 1
         (:REWRITE RP::NOT-INCLUDE-RP-MEANS-VALID-SC-LST))
     (11 1 (:REWRITE RP::NOT-INCLUDE-EX-FROM-RP))
     (10 10 (:TYPE-PRESCRIPTION O-FINP))
     (9 1
        (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (8 8
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (8 2
        (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (5 5 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (5 5
        (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (5 5
        (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (5 5
        (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (5 5
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (5 5
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (5 5
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (5 5
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (5 5
        (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (5 5
        (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (5 5
        (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (5 5
        (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (5 5
        (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (5 5
        (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (5 5
        (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (5 5
        (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (5 5
        (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (5 5
        (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (5 5
        (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (5 5
        (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (5 5
        (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (5 5
        (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (5 5
        (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (5 5
        (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (5 5 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (5 1 (:REWRITE RP::VALID-SC-OF-EX-FROM-RP))
     (4 4
        (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP))
     (4 3 (:REWRITE RP::VALID-SC-CADR))
     (4 1
        (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (3 3 (:TYPE-PRESCRIPTION QUOTEP))
     (3 2 (:REWRITE RP::VALID-SC-CADDR))
     (2 2
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (2 1 (:REWRITE RP::VALID-SC-CADDDR))
     (1 1 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (1 1 (:TYPE-PRESCRIPTION RP::EVAL-AND-ALL))
     (1 1
        (:REWRITE RP::CAR-OF-EX-FROM-RP-IS-NOT-RP)))
