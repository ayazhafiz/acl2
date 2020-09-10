(RP::FLAG-INCLUDE-FNC (269 130 (:REWRITE DEFAULT-+-2))
                      (196 14 (:DEFINITION LENGTH))
                      (181 130 (:REWRITE DEFAULT-+-1))
                      (154 14 (:DEFINITION LEN))
                      (112 28 (:REWRITE COMMUTATIVITY-OF-+))
                      (112 28 (:DEFINITION INTEGER-ABS))
                      (80 38 (:REWRITE DEFAULT-CDR))
                      (43 34 (:REWRITE DEFAULT-<-2))
                      (42 42
                          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                      (42 28 (:REWRITE STR::CONSP-OF-EXPLODE))
                      (40 34 (:REWRITE DEFAULT-<-1))
                      (37 37 (:REWRITE FOLD-CONSTS-IN-+))
                      (28 28 (:REWRITE DEFAULT-UNARY-MINUS))
                      (28 28 (:REWRITE DEFAULT-CAR))
                      (28 14
                          (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                      (14 14 (:TYPE-PRESCRIPTION LEN))
                      (14 14
                          (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                      (14 14 (:REWRITE DEFAULT-REALPART))
                      (14 14 (:REWRITE DEFAULT-NUMERATOR))
                      (14 14 (:REWRITE DEFAULT-IMAGPART))
                      (14 14 (:REWRITE DEFAULT-DENOMINATOR))
                      (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(FLAG::FLAG-EQUIV-LEMMA)
(RP::FLAG-INCLUDE-FNC-EQUIVALENCES)
(RP::FLAG-RP-TERMP (598 288 (:REWRITE DEFAULT-+-2))
                   (406 29 (:DEFINITION LENGTH))
                   (392 288 (:REWRITE DEFAULT-+-1))
                   (319 29 (:DEFINITION LEN))
                   (232 58 (:DEFINITION INTEGER-ABS))
                   (120 1
                        (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                   (90 71 (:REWRITE DEFAULT-<-2))
                   (87 87
                       (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                   (87 58 (:REWRITE STR::CONSP-OF-EXPLODE))
                   (82 71 (:REWRITE DEFAULT-<-1))
                   (58 58 (:REWRITE DEFAULT-UNARY-MINUS))
                   (58 29
                       (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
                   (29 29 (:TYPE-PRESCRIPTION LEN))
                   (29 29
                       (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                   (29 29 (:REWRITE DEFAULT-REALPART))
                   (29 29 (:REWRITE DEFAULT-NUMERATOR))
                   (29 29 (:REWRITE DEFAULT-IMAGPART))
                   (29 29 (:REWRITE DEFAULT-DENOMINATOR))
                   (5 5 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(FLAG::FLAG-EQUIV-LEMMA)
(RP::FLAG-RP-TERMP-EQUIVALENCES)
(RP::FLAG-BETA-SEARCH-REDUCE
     (136 2 (:DEFINITION PSEUDO-TERMP))
     (62 10 (:DEFINITION LEN))
     (62 6 (:DEFINITION LENGTH))
     (34 28 (:REWRITE DEFAULT-CDR))
     (33 33 (:REWRITE DEFAULT-CAR))
     (25 15 (:REWRITE DEFAULT-+-2))
     (16 16 (:REWRITE DEFAULT-<-2))
     (16 16 (:REWRITE DEFAULT-<-1))
     (16 2 (:TYPE-PRESCRIPTION RETURN-LAST))
     (15 15 (:REWRITE DEFAULT-+-1))
     (8 4 (:DEFINITION TRUE-LISTP))
     (8 2 (:DEFINITION SYMBOL-LISTP))
     (6 6
        (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (6 4 (:REWRITE STR::CONSP-OF-EXPLODE))
     (4 4 (:REWRITE ZP-OPEN))
     (4 4 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (4 4 (:REWRITE FN-CHECK-DEF-FORMALS))
     (4 2
        (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (2 2
        (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
     (2 2 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
     (2 2
        (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
     (2 2
        (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (2 2
        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (2 2 (:LINEAR LEN-WHEN-PREFIXP)))
(FLAG::FLAG-EQUIV-LEMMA)
(RP::FLAG-BETA-SEARCH-REDUCE-EQUIVALENCES)
(RP::FLAG-LAMBDA-EXP-FREE-P
     (264 128 (:REWRITE DEFAULT-+-2))
     (196 14 (:DEFINITION LENGTH))
     (178 128 (:REWRITE DEFAULT-+-1))
     (154 14 (:DEFINITION LEN))
     (112 28 (:REWRITE COMMUTATIVITY-OF-+))
     (112 28 (:DEFINITION INTEGER-ABS))
     (79 37 (:REWRITE DEFAULT-CDR))
     (43 34 (:REWRITE DEFAULT-<-2))
     (42 42
         (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (42 28 (:REWRITE STR::CONSP-OF-EXPLODE))
     (40 34 (:REWRITE DEFAULT-<-1))
     (36 36 (:REWRITE FOLD-CONSTS-IN-+))
     (28 28 (:REWRITE DEFAULT-UNARY-MINUS))
     (28 14
         (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (27 27 (:REWRITE DEFAULT-CAR))
     (14 14 (:TYPE-PRESCRIPTION LEN))
     (14 14
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (14 14 (:REWRITE DEFAULT-REALPART))
     (14 14 (:REWRITE DEFAULT-NUMERATOR))
     (14 14 (:REWRITE DEFAULT-IMAGPART))
     (14 14 (:REWRITE DEFAULT-DENOMINATOR))
     (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(FLAG::FLAG-EQUIV-LEMMA)
(RP::FLAG-LAMBDA-EXP-FREE-P-EQUIVALENCES)
(RP::FLAG-GET-LAMBDA-FREE-VARS
     (795 363 (:REWRITE DEFAULT-+-2))
     (507 363 (:REWRITE DEFAULT-+-1))
     (504 36 (:DEFINITION LENGTH))
     (396 36 (:DEFINITION LEN))
     (288 72 (:DEFINITION INTEGER-ABS))
     (119 89 (:REWRITE DEFAULT-<-2))
     (108 108
          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (108 72 (:REWRITE STR::CONSP-OF-EXPLODE))
     (103 89 (:REWRITE DEFAULT-<-1))
     (72 72 (:REWRITE DEFAULT-UNARY-MINUS))
     (72 36
         (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (36 36 (:TYPE-PRESCRIPTION LEN))
     (36 36
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (36 36 (:REWRITE DEFAULT-REALPART))
     (36 36 (:REWRITE DEFAULT-NUMERATOR))
     (36 36 (:REWRITE DEFAULT-IMAGPART))
     (36 36 (:REWRITE DEFAULT-DENOMINATOR))
     (6 6 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(FLAG::FLAG-EQUIV-LEMMA)
(RP::FLAG-GET-LAMBDA-FREE-VARS-EQUIVALENCES)
(RP::IS-LAMBDA-IMPLIES)
(RP::IS-LAMBDA-STRICT-IMPLIES)
(RP::GET-LAMBDA-FREE-VARS-IMPLIES
     (253 253 (:REWRITE DEFAULT-CAR))
     (244 244 (:REWRITE DEFAULT-CDR))
     (108 12 (:DEFINITION RP::REMOVE-VARS))
     (84 4
         (:DEFINITION RP::GET-LAMBDA-FREE-VARS-LST))
     (72 8 (:DEFINITION RP::UNION-EQUAL2))
     (60 20 (:DEFINITION RP::IS-MEMBER))
     (20 20 (:TYPE-PRESCRIPTION RP::IS-MEMBER))
     (5 5 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::RP-TERMP-IMPLIES (662 662 (:REWRITE DEFAULT-CDR))
                      (501 501 (:REWRITE DEFAULT-CAR))
                      (32 32 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::LAMBDA-EXP-FREE-P-IMPLIES (4 4 (:REWRITE DEFAULT-CAR))
                               (4 1
                                  (:DEFINITION RP::LAMBDA-EXP-FREE-LISTP))
                               (3 3 (:REWRITE DEFAULT-CDR)))
(RP::LAMBDA-EXP-FREE-LISTP-IMPLIES (5 5 (:REWRITE DEFAULT-CAR))
                                   (5 1 (:DEFINITION RP::LAMBDA-EXP-FREE-P))
                                   (4 4 (:REWRITE DEFAULT-CDR))
                                   (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::RP-TERMP-DUMB-NEGATE-LIT2
     (806 5 (:DEFINITION RP::FALIST-CONSISTENT))
     (607 5
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (588 588 (:REWRITE DEFAULT-CDR))
     (510 510 (:REWRITE DEFAULT-CAR))
     (336 37
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (26 26 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (13 13
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::FLAG-LEMMA-FOR-RP-TERMP-IMPLIES-PSEUDO-TERMP
     (1512 1503 (:REWRITE DEFAULT-CDR))
     (1006 1006 (:REWRITE DEFAULT-CAR))
     (93 9 (:DEFINITION LENGTH))
     (84 84 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (78 12 (:DEFINITION LEN))
     (27 27 (:TYPE-PRESCRIPTION LEN))
     (24 12 (:REWRITE DEFAULT-+-2))
     (20 20
         (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (20 20
         (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (12 12 (:REWRITE DEFAULT-+-1))
     (12 3 (:DEFINITION SYMBOL-LISTP))
     (9 9
        (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (9 6 (:REWRITE STR::CONSP-OF-EXPLODE))
     (6 6 (:REWRITE FN-CHECK-DEF-FORMALS))
     (6 3
        (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (3 3 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
     (3 3
        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP)))
(RP::RP-TERMP-IMPLIES-PSEUDO-TERMP)
(RP::RP-TERM-LIST-IMPLIES-PSEUDO-TERM-LISTP)
(RP::STRIP-CDRS-PSEUDO-TERMLISTP2
     (960 8
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (849 845 (:REWRITE DEFAULT-CDR))
     (610 606 (:REWRITE DEFAULT-CAR))
     (40 40 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::RP-TERMP-BINDINGS-LEMMA1
     (552 3 (:DEFINITION RP::RP-TERMP))
     (483 3 (:DEFINITION RP::FALIST-CONSISTENT))
     (360 3
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (338 334 (:REWRITE DEFAULT-CDR))
     (265 261 (:REWRITE DEFAULT-CAR))
     (36 9
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (15 15 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (3 3 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (3 3
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::RP-TERM-LISTP-IS-TRUE-LISTP)
(RP::IS-SYNP-IMPLIES (10 10 (:REWRITE DEFAULT-CDR))
                     (1 1 (:REWRITE DEFAULT-CAR)))
(RP::PSEUDO-TERMLISTP-EXTRACT-FROM-RP
     (2663 2663 (:REWRITE DEFAULT-CAR))
     (229 229 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::RP-TERMP-EXTRACT-FROM-RP (180 180 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::EXTRACT-FROM-SYNP-TO-EX-FROM-RP
     (20 20 (:REWRITE DEFAULT-CDR))
     (11 11
         (:TYPE-PRESCRIPTION RP::EXTRACT-FROM-SYNP))
     (11 11
         (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (2 2 (:REWRITE DEFAULT-CAR)))
(RP::PSEUDO-TERMP-EXTRACT-FROM-SYNP
     (418 2 (:DEFINITION RP::RP-TERMP))
     (322 2 (:DEFINITION RP::FALIST-CONSISTENT))
     (242 242 (:REWRITE DEFAULT-CDR))
     (240 2
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (155 155 (:REWRITE DEFAULT-CAR))
     (52 2 (:DEFINITION RP::IS-RP$INLINE))
     (14 14 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (8 2
        (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (2 2
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::ATOM-RP-TERMP-IS-SYMBOLP)
(RP::RP-TERMP-CONTEXT-FROM-RP (3336 3334 (:REWRITE DEFAULT-CDR))
                              (2440 2438 (:REWRITE DEFAULT-CAR))
                              (434 14 (:DEFINITION RP::EX-FROM-RP))
                              (225 225 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                              (20 20
                                  (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP)))
(RP::PUT-TERM-IN-CONS-IS-PSEUDO-TERMP (20 20 (:REWRITE DEFAULT-CDR))
                                      (19 19 (:REWRITE DEFAULT-CAR)))
(RP::EXTRACT-FROM-RP-WITH-CONTEXT-TO-NO-CONTEXT
     (448 448 (:REWRITE DEFAULT-CDR))
     (263 263 (:REWRITE DEFAULT-CAR))
     (36 36 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (8 8
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::EXTRACT-FROM-RP-WITH-CONTEXT-CONTEXT
     (575 575 (:REWRITE DEFAULT-CDR))
     (333 333 (:REWRITE DEFAULT-CAR))
     (279 9 (:DEFINITION RP::EX-FROM-RP))
     (182 182
          (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP))
     (50 50 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (15 15
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::CONS-CONSP-CONTEXT-FROM-RP (243 242 (:REWRITE DEFAULT-CDR))
                                (229 227 (:REWRITE DEFAULT-CAR))
                                (49 49 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                                (31 1 (:DEFINITION RP::EX-FROM-RP))
                                (9 9
                                   (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP))
                                (3 3
                                   (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::SYMBOLP-EX-FROM-RP (215 1 (:DEFINITION RP::RP-TERMP))
                        (161 1 (:DEFINITION RP::FALIST-CONSISTENT))
                        (150 150 (:REWRITE DEFAULT-CDR))
                        (120 1
                             (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                        (95 95 (:REWRITE DEFAULT-CAR))
                        (81 3 (:DEFINITION RP::IS-RP$INLINE))
                        (62 2 (:DEFINITION RP::EX-FROM-RP))
                        (11 11 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                        (4 1
                           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                        (1 1
                           (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::EX-FROM-RP-X2 (602 602 (:REWRITE DEFAULT-CDR))
                   (351 351 (:REWRITE DEFAULT-CAR))
                   (50 50 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                   (10 10
                       (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::EX-FROM-SYNP-EX-FROM-RPX2 (651 21 (:DEFINITION RP::EX-FROM-RP))
                               (567 21 (:DEFINITION RP::IS-RP$INLINE))
                               (417 417 (:REWRITE DEFAULT-CDR))
                               (198 198 (:REWRITE DEFAULT-CAR))
                               (42 42 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                               (21 21
                                   (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                               (1 1
                                  (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE)))
(RP::APPEND-OF-TWO-CONTEXT
     (387 2 (:DEFINITION RP::RP-TERMP))
     (330 2 (:DEFINITION RP::FALIST-CONSISTENT))
     (261 17
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (247 2
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (225 222 (:REWRITE DEFAULT-CDR))
     (161 158 (:REWRITE DEFAULT-CAR))
     (22 11
         (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (11 11 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (11 11 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (10 10
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (10 10 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (6 3
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (3 3
        (:TYPE-PRESCRIPTION RP::IS-RP$INLINE)))
(RP::FLAG-LEMMA-FOR-EVAL-OF-BETA-SEARCH-REDUCE
     (17492 111 (:DEFINITION RP::RP-TERMP))
     (14872 88 (:DEFINITION RP::FALIST-CONSISTENT))
     (11679 246
            (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (11176 88
            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (9143 9116 (:REWRITE DEFAULT-CDR))
     (7050 35
           (:REWRITE RP::RP-TERM-LIST-IMPLIES-PSEUDO-TERM-LISTP))
     (6480 54
           (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (6409 6388 (:REWRITE DEFAULT-CAR))
     (5711 37
           (:REWRITE RP::RP-TERMP-IMPLIES-PSEUDO-TERMP))
     (2833 93 (:DEFINITION RP::RP-TERM-LISTP))
     (792 792
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (625 625
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (420 420 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (211 149
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (176 176
          (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (141 90 (:REWRITE DEFAULT-+-2))
     (90 90 (:REWRITE DEFAULT-+-1))
     (69 23 (:REWRITE FOLD-CONSTS-IN-+))
     (50 24 (:REWRITE BETA-EVAL-CONSTRAINT-3))
     (50 17 (:REWRITE ZP-OPEN))
     (42 42 (:LINEAR LEN-WHEN-PREFIXP))
     (40 8 (:DEFINITION SYMBOL-LISTP))
     (35 35
         (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (34 34 (:TYPE-PRESCRIPTION KWOTE-LST))
     (34 34
         (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (24 24
         (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (24 16 (:REWRITE STR::CONSP-OF-EXPLODE))
     (24 6 (:DEFINITION KWOTE-LST))
     (16 16 (:REWRITE FN-CHECK-DEF-FORMALS))
     (11 11 (:REWRITE DEFAULT-<-2))
     (11 11 (:REWRITE DEFAULT-<-1))
     (10 2 (:DEFINITION ASSOC-EQUAL))
     (8 8
        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (6 6 (:DEFINITION KWOTE)))
(RP::EVAL-OF-BETA-SEARCH-REDUCE)
(RP::EVAL-OF-BETA-SEARCH-REDUCE-SUBTERMS)
(RP::EVAL-OF-BETA-SEARCH-REDUCE-FIXED-LIM
     (1524 2 (:DEFINITION PSEUDO-TERMP))
     (1402 11 (:DEFINITION RP::RP-TERMP))
     (1183 7 (:DEFINITION RP::FALIST-CONSISTENT))
     (889 7
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (856 23
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (749 743 (:REWRITE DEFAULT-CDR))
     (734 8
          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (678 4 (:DEFINITION TRUE-LISTP))
     (616 4
          (:REWRITE RP::RP-TERMP-IMPLIES-PSEUDO-TERMP))
     (590 1 (:DEFINITION RP::BETA-SEARCH-REDUCE))
     (533 533 (:REWRITE DEFAULT-CAR))
     (236 2
          (:REWRITE RP::RP-TERM-LIST-IMPLIES-PSEUDO-TERM-LISTP))
     (130 10 (:DEFINITION RP::RP-TERM-LISTP))
     (124 124 (:TYPE-PRESCRIPTION RP::RP-TERMP))
     (64 64
         (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (63 63
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (62 10 (:DEFINITION LEN))
     (62 6 (:DEFINITION LENGTH))
     (35 35 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (26 2 (:DEFINITION LAMBDA-EXPR-P))
     (25 25 (:TYPE-PRESCRIPTION LEN))
     (22 16
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (20 10 (:REWRITE DEFAULT-+-2))
     (20 2
         (:REWRITE BETA-EVAL-TO-BETA-REDUCE-LAMBDA-EXPR))
     (14 14
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (10 10 (:REWRITE DEFAULT-+-1))
     (10 2 (:DEFINITION SYMBOL-LISTP))
     (6 6
        (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (6 4 (:REWRITE STR::CONSP-OF-EXPLODE))
     (4 4 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (4 4 (:REWRITE FN-CHECK-DEF-FORMALS))
     (4 4 (:LINEAR LEN-WHEN-PREFIXP))
     (4 2
        (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (3 2 (:REWRITE BETA-EVAL-CONSTRAINT-1))
     (3 1 (:DEFINITION QUOTEP))
     (2 2 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
     (2 2
        (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
     (2 2
        (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (2 2
        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (2 2 (:REWRITE BETA-EVAL-CONSTRAINT-3))
     (2 2 (:REWRITE BETA-EVAL-CONSTRAINT-2))
     (1 1 (:TYPE-PRESCRIPTION LAMBDA-EXPR-P)))
(RP::FALIST-CONSISTENT-IMPLIES-FALIST-SYNTAXP
     (2848 511
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (1915 838
           (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (1050 1050 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (18 6 (:REWRITE CONS-EQUAL)))
(RP::EXTRACT-FROM-RP-WITH-CONTEXT-TO-CONTEXT-FROM-RP
     (3 3
        (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP)))
(RP::REMOVE-FROM-ALIST-RETURNS-ALISTP (51 51 (:REWRITE DEFAULT-CAR))
                                      (19 19 (:REWRITE DEFAULT-CDR)))
(RP::LEMMA1)
(RP::GET-LAMBDA-FREE-VARS-OF-CONS-CAR-TERM-SUBTERMS
     (189 1 (:DEFINITION RP::RP-TERMP))
     (161 1 (:DEFINITION RP::FALIST-CONSISTENT))
     (146 146 (:REWRITE DEFAULT-CDR))
     (120 1
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (115 115 (:REWRITE DEFAULT-CAR))
     (63 3
         (:DEFINITION RP::GET-LAMBDA-FREE-VARS-LST))
     (54 6 (:DEFINITION RP::UNION-EQUAL2))
     (27 9 (:DEFINITION RP::IS-MEMBER))
     (27 3 (:DEFINITION RP::REMOVE-VARS))
     (9 9 (:TYPE-PRESCRIPTION RP::IS-MEMBER))
     (8 8 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (5 2
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (4 1
        (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (1 1
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::FLAG-LEMMA-FOR-RP-TERMP-IMPLIES-GET-LAMBDA-FREE-VARS
     (1197 1197 (:REWRITE DEFAULT-CAR))
     (282 42 (:DEFINITION RP::UNION-EQUAL2))
     (118 50 (:DEFINITION RP::IS-MEMBER))
     (108 12 (:DEFINITION RP::REMOVE-VARS))
     (93 93 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (34 34 (:TYPE-PRESCRIPTION RP::IS-MEMBER))
     (12 12
         (:TYPE-PRESCRIPTION RP::REMOVE-VARS)))
(RP::RP-TERMP-IMPLIES-GET-LAMBDA-FREE-VARS)
(RP::RP-TERM-LISTP-IMPLIES-GET-LAMBDA-FREE-VARS-LST)
(RP::GET-LAMBDA-FREE-VARS-OF-BINDINGS
     (24 1
         (:DEFINITION RP::GET-LAMBDA-FREE-VARS))
     (19 19 (:REWRITE DEFAULT-CAR))
     (15 15 (:REWRITE DEFAULT-CDR))
     (15 3 (:DEFINITION ASSOC-EQUAL))
     (10 1 (:DEFINITION RP::RP-TERM-LISTP))
     (9 1 (:DEFINITION RP::REMOVE-VARS))
     (4 1
        (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (4 1 (:DEFINITION STRIP-CDRS))
     (3 1 (:DEFINITION QUOTEP))
     (3 1 (:DEFINITION RP::IS-MEMBER))
     (2 2 (:TYPE-PRESCRIPTION STRIP-CDRS))
     (1 1 (:TYPE-PRESCRIPTION RP::REMOVE-VARS))
     (1 1 (:TYPE-PRESCRIPTION RP::IS-MEMBER))
     (1 1 (:TYPE-PRESCRIPTION RP::IS-LAMBDA))
     (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::RP-TERMP-CONS-CAR-TERM-SUBTERMS
     (1055 1055 (:REWRITE DEFAULT-CDR))
     (812 812 (:REWRITE DEFAULT-CAR))
     (91 19
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (61 61 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (37 31
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::RP-TERM-LISTP-APPEND)
(RP::IS-FALIST-REMOVE-RETURN-LAST-SUBTERMS
     (90 3 (:DEFINITION RP::REMOVE-RETURN-LAST))
     (83 83 (:REWRITE DEFAULT-CDR))
     (36 3
         (:DEFINITION RP::IS-RETURN-LAST$INLINE))
     (28 28 (:REWRITE DEFAULT-CAR))
     (9 3 (:DEFINITION QUOTEP))
     (3 3 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::NOT-IS-FALIST-CONS-QUOTE-RETURN-LAST (1 1 (:REWRITE DEFAULT-CAR)))
(RP::LEMMA1 (1 1 (:REWRITE DEFAULT-CAR)))
(RP::DONT-RW-SYNTAXP-DONT-RW-IF-FIX)
(RP::IS-IF-IMPLIES)
(RP::IS-RP-IMPLIES-FC)
(RP::RULE-SYNTAXP-IMPLIES (720 6
                               (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                          (667 667 (:REWRITE DEFAULT-CDR))
                          (485 485 (:REWRITE DEFAULT-CAR))
                          (42 42 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::RULE-SYNTAXP-IMPLIES-2)
(RP::EX-FROM-RP-LOOSE-OF-EX-FROM-RP-LOOSE (118 118 (:REWRITE DEFAULT-CDR))
                                          (32 32 (:REWRITE DEFAULT-CAR)))
(RP::RP-TERMP-EX-FROM-RP (1567 1567 (:REWRITE DEFAULT-CDR))
                         (1320 11
                               (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                         (1046 1046 (:REWRITE DEFAULT-CAR))
                         (97 97 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                         (31 1 (:DEFINITION RP::EX-FROM-RP)))
(RP::RP-TERMP-CADR (1200 10
                         (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                   (1132 1132 (:REWRITE DEFAULT-CDR))
                   (760 760 (:REWRITE DEFAULT-CAR))
                   (69 69 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                   (40 25
                       (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                   (32 8
                       (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP)))
(RP::RP-TERMP-CADDR (981 8
                         (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                    (956 956 (:REWRITE DEFAULT-CDR))
                    (773 30 (:REWRITE RP::RP-TERMP-CADR))
                    (647 647 (:REWRITE DEFAULT-CAR))
                    (112 20
                         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                    (60 60 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                    (48 24
                        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                    (3 3 (:TYPE-PRESCRIPTION BOOLEANP)))
(RP::RP-TERMP-CADDDR (3013 58 (:REWRITE RP::RP-TERMP-CADDR))
                     (2505 20
                           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                     (2463 2463 (:REWRITE DEFAULT-CDR))
                     (1590 1590 (:REWRITE DEFAULT-CAR))
                     (863 63 (:REWRITE RP::RP-TERMP-CADR))
                     (158 36
                          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                     (141 141 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                     (140 140
                          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
                     (101 56
                          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                     (15 15 (:TYPE-PRESCRIPTION BOOLEANP)))
(RP::RP-TERMP-CADDDDR (3615 69 (:REWRITE RP::RP-TERMP-CADDR))
                      (2925 2925 (:REWRITE DEFAULT-CDR))
                      (2625 21
                            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                      (1836 1836 (:REWRITE DEFAULT-CAR))
                      (913 74 (:REWRITE RP::RP-TERMP-CADR))
                      (867 42 (:REWRITE RP::RP-TERMP-CADDDR))
                      (252 76
                           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                      (172 172 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                      (141 141
                           (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
                      (137 77
                           (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                      (15 15 (:TYPE-PRESCRIPTION BOOLEANP)))
(RP::EX-FROM-RP-LOOSE-IS-EX-FROM-RP
     (1419 1419 (:REWRITE DEFAULT-CDR))
     (1142 17 (:DEFINITION RP::FALIST-CONSISTENT))
     (921 921 (:REWRITE DEFAULT-CAR))
     (605 10
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (104 45
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (90 90 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (73 17
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (58 14 (:REWRITE RP::RP-TERMP-CADDR))
     (47 14 (:REWRITE RP::RP-TERMP-CADR))
     (5 5
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::CAR-OF-EX-FROM-RP-IS-NOT-RP
     (1297 1297 (:REWRITE DEFAULT-CDR))
     (1142 17 (:DEFINITION RP::FALIST-CONSISTENT))
     (605 10
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (158 60
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (92 92 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (73 17
         (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (58 14 (:REWRITE RP::RP-TERMP-CADDR))
     (47 14 (:REWRITE RP::RP-TERMP-CADR))
     (5 5
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::DONT-RW-SYNTAXP-DONT-RW-SYNTAX-FIX)
(RP::RP-TERMP-IMPLIES-DONT-RW-SYNTAXP)
(RP::RP-TERMP-EX-FROM-FALIST
     (410 2 (:DEFINITION RP::RP-TERMP))
     (322 2 (:DEFINITION RP::FALIST-CONSISTENT))
     (240 2
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (210 210 (:REWRITE DEFAULT-CDR))
     (140 140 (:REWRITE DEFAULT-CAR))
     (16 4 (:REWRITE RP::RP-TERMP-CADR))
     (16 4 (:REWRITE RP::RP-TERMP-CADDR))
     (10 10 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (10 4
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (8 2
        (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (2 2
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (2 1
        (:TYPE-PRESCRIPTION RP::RP-TERMP-EX-FROM-FALIST)))
(RP::IS-FALIST-STRICT-TO-IS-FALIST
     (148 148 (:REWRITE DEFAULT-CDR))
     (120 1
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (118 118 (:REWRITE DEFAULT-CAR))
     (8 8 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (8 2 (:REWRITE RP::RP-TERMP-CADR))
     (8 2 (:REWRITE RP::RP-TERMP-CADDR))
     (5 2
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (4 1
        (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (1 1
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::RP-TERMP-TRANS*-LIST
     (1199 7 (:DEFINITION RP::FALIST-CONSISTENT))
     (847 7
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (813 733 (:REWRITE DEFAULT-CDR))
     (551 515 (:REWRITE DEFAULT-CAR))
     (261 14
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (56 15 (:REWRITE RP::RP-TERMP-CADR))
     (52 14 (:REWRITE RP::RP-TERMP-CADDR))
     (35 35 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (27 9
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (15 15
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::CONSP-RP-TRANS-LST (27 27 (:REWRITE DEFAULT-CDR))
                        (26 1 (:DEFINITION RP::RP-TRANS))
                        (16 16 (:REWRITE DEFAULT-CAR))
                        (8 1 (:DEFINITION RP::IS-FALIST))
                        (7 1 (:DEFINITION RP::TRANS-LIST))
                        (3 1 (:DEFINITION QUOTEP))
                        (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(RP::IS-RP-RP-TRANS-LST (324 302 (:REWRITE DEFAULT-CDR))
                        (209 197 (:REWRITE DEFAULT-CAR))
                        (161 1 (:DEFINITION RP::FALIST-CONSISTENT))
                        (120 1
                             (:DEFINITION RP::FALIST-CONSISTENT-AUX))
                        (20 5 (:REWRITE RP::RP-TERMP-CADR))
                        (20 5 (:REWRITE RP::RP-TERMP-CADDR))
                        (18 1 (:DEFINITION RP::TRANS-LIST))
                        (15 15 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                        (10 7
                            (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
                        (8 1 (:DEFINITION RP::IS-FALIST))
                        (4 1
                           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
                        (1 1
                           (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::FLAG-LEMMA-FOR-RP-TERMP-OF-RP-TRANS
     (5518 45
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (1039 117 (:REWRITE RP::RP-TERMP-CADR))
     (606 41 (:REWRITE RP::RP-TERMP-TRANS*-LIST))
     (241 241 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (24 6 (:REWRITE RP::RP-TERMP-CADDDR)))
(RP::RP-TERMP-OF-RP-TRANS)
(RP::RP-TERM-LISTP-OF-RP-TRANS-LST)
(RP::RP-STATE-NEW-RUN-RETURNS-RP-STATEP
     (245 2
          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (231 1 (:DEFINITION TRUE-LISTP))
     (217 4
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (206 1 (:DEFINITION RP::RP-TERMP))
     (169 1 (:DEFINITION RP::FALIST-CONSISTENT))
     (139 127 (:REWRITE DEFAULT-CDR))
     (127 1
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (88 76 (:REWRITE DEFAULT-CAR))
     (41 41 (:REWRITE NTH-WHEN-PREFIXP))
     (36 4 (:DEFINITION UPDATE-NTH))
     (30 15 (:DEFINITION NTH))
     (30 2 (:DEFINITION RP::RP-TERM-LISTP))
     (27 27 (:TYPE-PRESCRIPTION RP::RP-TERMP))
     (12 12
         (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (9 9
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (8 3 (:REWRITE RP::RP-TERMP-CADR))
     (6 2 (:DEFINITION ALISTP))
     (5 5 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (4 2 (:REWRITE RP::RP-TERMP-CADDR))
     (4 2 (:REWRITE DEFAULT-+-2))
     (2 2 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (2 2 (:REWRITE DEFAULT-+-1))
     (2 2
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
(RP::RP-TERM-LISTP-OF-APPEND)
(RP::RP-STATE-PRESERVEDP-OF-THE-SAME
     (245 2
          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (231 1 (:DEFINITION TRUE-LISTP))
     (217 4
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (206 1 (:DEFINITION RP::RP-TERMP))
     (169 1 (:DEFINITION RP::FALIST-CONSISTENT))
     (128 128 (:REWRITE DEFAULT-CDR))
     (127 1
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (74 74 (:REWRITE DEFAULT-CAR))
     (36 18 (:DEFINITION NTH))
     (30 2 (:DEFINITION RP::RP-TERM-LISTP))
     (27 27 (:TYPE-PRESCRIPTION RP::RP-TERMP))
     (18 18 (:REWRITE NTH-WHEN-PREFIXP))
     (12 12
         (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (9 9
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (8 3 (:REWRITE RP::RP-TERMP-CADR))
     (5 5 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (4 2 (:REWRITE RP::RP-TERMP-CADDR))
     (4 2 (:REWRITE DEFAULT-+-2))
     (3 3
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (2 2 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (2 2 (:REWRITE DEFAULT-+-1))
     (1 1
        (:REWRITE RP::RP-STATE-PRESERVEDP-SK-NECC)))
(RP::RP-STATE-PRESERVEDP-IMPLIES-RP-STATEP
     (490 4
          (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (462 2 (:DEFINITION TRUE-LISTP))
     (434 8
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (412 2 (:DEFINITION RP::RP-TERMP))
     (338 2 (:DEFINITION RP::FALIST-CONSISTENT))
     (256 256 (:REWRITE DEFAULT-CDR))
     (254 2
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (148 148 (:REWRITE DEFAULT-CAR))
     (72 36 (:DEFINITION NTH))
     (60 4 (:DEFINITION RP::RP-TERM-LISTP))
     (54 54 (:TYPE-PRESCRIPTION RP::RP-TERMP))
     (36 36 (:REWRITE NTH-WHEN-PREFIXP))
     (24 24
         (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (18 18
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (16 6 (:REWRITE RP::RP-TERMP-CADR))
     (10 10 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (8 8 (:REWRITE DEFAULT-<-2))
     (8 8 (:REWRITE DEFAULT-<-1))
     (8 4 (:REWRITE RP::RP-TERMP-CADDR))
     (8 4 (:REWRITE DEFAULT-+-2))
     (5 5
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (4 4 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (4 4 (:REWRITE DEFAULT-+-1))
     (1 1
        (:REWRITE RP::RP-STATE-PRESERVEDP-SK-NECC)))
(RP::RP-STATE-PRESERVEDP-IMPLIES-VALID-RP-STATE-SYNTAXP
     (7 7
        (:REWRITE RP::VALID-RP-STATE-SYNTAXP-AUX-NECC))
     (4 4
        (:REWRITE RP::RP-STATE-PRESERVEDP-SK-NECC))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 4 (:REWRITE DEFAULT-CAR))
     (3 3
        (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP)))
