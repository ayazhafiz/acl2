(RP::RP-EQUAL-CNT-MEMOIZED)
(RP::IS-CAR-X-PP+)
(RP::ARE-C-INSTANCES$INLINE)
(RP::ARE-C-INSTANCES-IMPLIES-FC)
(RP::ARE-S-INSTANCES$INLINE)
(RP::ARE-S-INSTANCES-IMPLIES-FC)
(RP::NTH-OF-CONSTANT (11 5 (:REWRITE ZP-OPEN))
                     (6 2 (:REWRITE FOLD-CONSTS-IN-+))
                     (5 5 (:REWRITE DEFAULT-CDR))
                     (5 5 (:REWRITE DEFAULT-CAR))
                     (5 5 (:REWRITE DEFAULT-+-2))
                     (5 5 (:REWRITE DEFAULT-+-1))
                     (3 3 (:REWRITE NTH-WHEN-PREFIXP))
                     (3 3 (:REWRITE DEFAULT-<-2))
                     (3 3 (:REWRITE DEFAULT-<-1))
                     (1 1
                        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP)))
(RP::RP-EQUAL-ITER-PP
     (19208 134 (:DEFINITION APPLY$-BADGEP))
     (17476 466 (:REWRITE RP::IS-IF-RP-TERMP))
     (15080 15080 (:REWRITE DEFAULT-CDR))
     (14348 170
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (12666 120 (:DEFINITION SUBSETP-EQUAL))
     (10860 900 (:DEFINITION MEMBER-EQUAL))
     (8310 8310 (:REWRITE DEFAULT-CAR))
     (6864 192 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (6834 480
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (5300 136
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (4360 20 (:DEFINITION RP::RP-EQUAL-ITER-PP))
     (3416 968 (:REWRITE O-P-O-INFP-CAR))
     (1800 1800 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (1644 140 (:DEFINITION NATP))
     (1560 1560 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (1440 1440
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (1108 188
           (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (960 960
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (882 882 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (646 646
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (596 164
          (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (583 583 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (449 9 (:REWRITE O<=-O-FINP-DEF))
     (438 186
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (424 134 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (420 210
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (408 408 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (294 166 (:REWRITE RP::CONS-COUNT-ATOM))
     (266 46 (:REWRITE RP::NOT-INCLUDE-RP))
     (210 210
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (192 192
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (176 44 (:DEFINITION RP::INCLUDE-FNC))
     (140 140
          (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (140 140
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (132 66
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (126 30 (:DEFINITION ALL-NILS))
     (120 30 (:DEFINITION LEN))
     (120 20
          (:REWRITE RP::PSEUDO-TERMLISTP-EXTRACT-FROM-RP))
     (106 104 (:REWRITE RP::MEASURE-LEMMA1))
     (84 84 (:TYPE-PRESCRIPTION LEN))
     (78 74 (:REWRITE DEFAULT-<-2))
     (78 74 (:REWRITE DEFAULT-<-1))
     (62 31 (:REWRITE DEFAULT-+-2))
     (60 60 (:TYPE-PRESCRIPTION ALL-NILS))
     (54 54
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (50 31 (:REWRITE DEFAULT-+-1))
     (45 9 (:REWRITE AC-<))
     (44 44 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (36 36
         (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
     (32 32
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (30 30 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (28 28 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (27 9 (:REWRITE O-INFP-O-FINP-O<=))
     (24 24
         (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
     (24 24 (:LINEAR LEN-WHEN-PREFIXP))
     (12 12 (:REWRITE RP::MEASURE-LEMMA1-2))
     (12 12 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (12 12 (:LINEAR BOUNDS-POSITION-EQUAL))
     (9 9 (:REWRITE |a < b & b < c  =>  a < c|))
     (4 4
        (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
     (2 2 (:REWRITE RP::EX-FROM-RP-X2)))
(RP::RP-EQUAL-CNT-ITER (8 8
                          (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP)))
(RP::RP-EQUAL-ITER-PP+-META
     (357 2 (:DEFINITION RP::RP-TERMP))
     (234 2 (:DEFINITION RP::FALIST-CONSISTENT))
     (154 1
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (153 153 (:REWRITE DEFAULT-CDR))
     (98 98 (:REWRITE DEFAULT-CAR))
     (88 7 (:REWRITE RP::IS-IF-RP-TERMP))
     (50 14 (:REWRITE O-P-O-INFP-CAR))
     (24 24 (:TYPE-PRESCRIPTION O-P))
     (14 3 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (14 3
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (12 12 (:REWRITE O-P-DEF-O-FINP-1))
     (12 2
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (11 11
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (9 9 (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (7 7 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (6 2
        (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (6 1 (:REWRITE RP::NOT-INCLUDE-RP))
     (4 1 (:DEFINITION RP::INCLUDE-FNC))
     (3 3
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (2 2
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (2 2 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (1 1 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (1 1
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::RP-EVLT-OF-EX-FROM-RP-REVERSE)
(RP::LEMMA1
     (59738 200 (:DEFINITION RP::RP-TERMP))
     (42354 200 (:DEFINITION RP::FALIST-CONSISTENT))
     (40705 72 (:REWRITE RP::RP-EVL-OF-RP-EQUAL2))
     (32710 200
            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (23379 19387 (:REWRITE DEFAULT-CAR))
     (19807 72
            (:REWRITE RP::RP-EVL-OF-RP-EQUAL-LOOSE))
     (16484 7583 (:REWRITE O-P-O-INFP-CAR))
     (8870 68 (:REWRITE RP::RP-TERMP-OF-RP-TRANS))
     (8332 106 (:DEFINITION RP::RP-EQUAL))
     (7484 808 (:REWRITE RP::IS-IF-RP-TERMP))
     (6784 422 (:REWRITE RP::RP-TERMP-CADR))
     (6318 212 (:DEFINITION RP::EX-FROM-RP))
     (5960 44
           (:REWRITE RP::RP-EVL-OF-RP-EQUAL2-SUBTERMS))
     (5502 72 (:REWRITE RP::RP-EVL-OF-RP-EQUAL))
     (4493 267 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (4394 22 (:DEFINITION RP::RP-EQUAL2-SUBTERMS))
     (4167 2367 (:REWRITE O-P-DEF-O-FINP-1))
     (3966 233 (:DEFINITION RP::IS-SYNP$INLINE))
     (3667 318 (:DEFINITION RP::INCLUDE-FNC))
     (3403 212 (:REWRITE RP::NOT-INCLUDE-RP))
     (2726 85 (:DEFINITION RP::RP-EQUAL-SUBTERMS))
     (2644 22
           (:REWRITE RP::RP-EQUAL-IMPLIES-RP-EQUAL2))
     (2331 568
           (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (2244 2244
           (:TYPE-PRESCRIPTION RP::TRANS-LIST))
     (1992 44
           (:REWRITE RP::RP-EQUAL-SUBTERMS-IMPLIES-RP-EQUAL2-SUBTERMS))
     (1800 1800
           (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (1586 267
           (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (1367 1367 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (1248 1248
           (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (1221 1221
           (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (1218 106
           (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
     (1126 44
           (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS))
     (1104 125
           (:REWRITE RP::RP-TRANS-LST-IS-LST-WHEN-LIST-IS-ABSENT))
     (1087 21 (:REWRITE RP::RP-EVLT-OF-RP-EQUAL))
     (1081 1081
           (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (1013 191 (:REWRITE RP::RP-EQUAL-REFLEXIVE))
     (970 276
          (:REWRITE RP::RP-EQUAL-SUBTERMS-REFLEXIVE))
     (966 186
          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (834 267 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (834 267 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (834 267 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (834 267 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (834 267 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (834 267 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (834 267 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (834 267 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (834 267 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (834 267 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (834 267 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (834 267 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (834 267 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (834 267 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (834 267
          (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (834 267 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (801 89
          (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (786 247 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (772 386 (:REWRITE RP::RP-TERMP-CADDR))
     (772 386 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (766 44
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-LOOSESUBTERMS))
     (744 247 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (712 712 (:TYPE-PRESCRIPTION O-FINP))
     (678 22
          (:DEFINITION RP::RP-EQUAL-LOOSE-SUBTERMS))
     (637 637
          (:TYPE-PRESCRIPTION RP::RP-EQUAL-SUBTERMS))
     (599 599
          (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (568 568
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (516 159 (:REWRITE RP::RP-EVL-LST-OF-ATOM))
     (492 6 (:REWRITE RP::RP-EQUAL-IS-SYMMETRIC))
     (488 488 (:TYPE-PRESCRIPTION RP::RP-EQUAL))
     (465 465 (:TYPE-PRESCRIPTION KWOTE-LST))
     (384 186
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (378 44
          (:REWRITE RP::RP-EQUAL2-SUBTERMS-REFLEXIVE))
     (372 372
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (323 38
          (:REWRITE RP::RP-EVLT-LST-OF-RP-EQUAL-LST))
     (301 44
          (:REWRITE RP::RP-EVL-OF-TRANS-LIST-LEMMA-2))
     (269 269
          (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (180 22 (:REWRITE RP::RP-EQUAL2-REFLEXIVE))
     (110 110
          (:TYPE-PRESCRIPTION RP::RP-EQUAL2-SUBTERMS))
     (110 110
          (:TYPE-PRESCRIPTION RP::RP-EQUAL-LOOSE-SUBTERMS))
     (78 6 (:DEFINITION KWOTE-LST))
     (66 66 (:TYPE-PRESCRIPTION RP::RP-EQUAL2))
     (66 66
         (:TYPE-PRESCRIPTION RP::RP-EQUAL-LOOSE))
     (54 18
         (:REWRITE RP::CONSP-OF-RP-EVL-OF-TRANS-LIST))
     (37 37
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (33 7
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (11 11
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (6 6 (:DEFINITION KWOTE)))
(RP::RP-EVLT-OF-RP-EQUAL-ITER-PP+-CORRECT
     (406 46
          (:REWRITE RP::RP-TRANS-LST-IS-LST-WHEN-LIST-IS-ABSENT))
     (371 22
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-LOOSESUBTERMS))
     (368 368
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (311 19
          (:DEFINITION RP::RP-EQUAL-LOOSE-SUBTERMS))
     (280 40
          (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (264 90 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (260 78 (:REWRITE RP::RP-EVL-OF-VARIABLE))
     (229 229 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (170 23
          (:REWRITE RP::NOT-INCLUDE-EX-FROM-RP))
     (166 46 (:REWRITE RP::RP-EVL-LST-OF-ATOM))
     (119 119
          (:REWRITE RP::RP-EQUAL-SUBTERMS-REFLEXIVE))
     (106 106 (:REWRITE RP::CONSP-RP-TRANS-LST))
     (96 78 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (96 78 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (96 78 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (96 78 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (96 78
         (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (96 78 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (96 78 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (96 78 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (96 78
         (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (96 78 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (96 78 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (96 78 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (96 78 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (96 78 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
     (96 78 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (96 78 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (96 78 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (96 78 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (96 78 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (96 78 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (96 78 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (96 78 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (96 78
         (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (96 78 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (95 95
         (:TYPE-PRESCRIPTION RP::RP-EQUAL-LOOSE-SUBTERMS))
     (93 81 (:DEFINITION RP::IS-SYNP$INLINE))
     (91 73
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (81 81
         (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (73 73
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (72 24
         (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (67 19
         (:REWRITE RP::RP-EVLT-LST-OF-RP-EQUAL-LST))
     (57 57
         (:TYPE-PRESCRIPTION RP::RP-EQUAL-LOOSE))
     (48 48
         (:TYPE-PRESCRIPTION RP::RP-EQUAL-SUBTERMS))
     (46 22
         (:REWRITE RP::RP-EVL-OF-TRANS-LIST-LEMMA-2))
     (8 2
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (6 6 (:REWRITE RP::EX-FROM-RP-X2))
     (4 2 (:DEFINITION APPLY$-BADGEP))
     (2 2 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (2 2 (:DEFINITION WEAK-APPLY$-BADGE-P)))
(RP::RP-EVLT-OF-RP-EQUAL-ITER-PP+
     (52403 106 (:DEFINITION RP::RP-TERMP))
     (47819 18 (:REWRITE RP::RP-EVL-OF-RP-EQUAL2))
     (43035 30 (:REWRITE RP::RP-TERMP-OF-RP-TRANS))
     (33988 60 (:DEFINITION RP::RP-TERM-LISTP))
     (26035 285
            (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (24926 92 (:DEFINITION APPLY$-BADGEP))
     (20436 116
            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (20073 513 (:REWRITE RP::IS-IF-RP-TERMP))
     (19743 273 (:REWRITE RP::RP-TERMP-CADR))
     (19148 168 (:DEFINITION SUBSETP-EQUAL))
     (17245 85 (:DEFINITION RP::FALIST-CONSISTENT))
     (15788 1260 (:DEFINITION MEMBER-EQUAL))
     (14007 87
            (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (10514 420 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (9920 672
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (5763 1763 (:REWRITE O-P-O-INFP-CAR))
     (4814 18
           (:REWRITE RP::RP-EVL-OF-RP-EQUAL-LOOSE))
     (4774 68
           (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (4518 10 (:REWRITE RP::LEMMA1))
     (4399 71 (:DEFINITION RP::RP-EQUAL))
     (3818 168 (:DEFINITION RP::EX-FROM-RP))
     (2860 10
           (:REWRITE RP::RP-EVL-OF-RP-EQUAL2-SUBTERMS))
     (2520 2520 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (2478 2478 (:TYPE-PRESCRIPTION RP::RP-TERMP))
     (2354 213 (:DEFINITION RP::INCLUDE-FNC))
     (2308 168 (:REWRITE RP::NOT-INCLUDE-RP))
     (2184 2184 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (2120 10 (:DEFINITION RP::RP-EQUAL2-SUBTERMS))
     (2016 2016
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (1606 1197 (:REWRITE O-P-DEF-O-FINP-1))
     (1344 1344
           (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (1340 40 (:DEFINITION RP::RP-EQUAL-SUBTERMS))
     (1270 10
           (:REWRITE RP::RP-EQUAL-IMPLIES-RP-EQUAL2))
     (1214 156 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (1176 1176 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (1160 84
           (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
     (984 18 (:REWRITE RP::RP-EVL-OF-RP-EQUAL))
     (960 84 (:DEFINITION NATP))
     (960 20
          (:REWRITE RP::RP-EQUAL-SUBTERMS-IMPLIES-RP-EQUAL2-SUBTERMS))
     (949 79 (:DEFINITION RP::IS-SYNP$INLINE))
     (920 42 (:DEFINITION TRUE-LISTP))
     (783 783
          (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (771 771 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (766 766
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (711 711
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (707 230
          (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (701 61
          (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
     (668 10 (:REWRITE RP::RP-EVLT-OF-RP-EQUAL))
     (634 634 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (602 602
          (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (570 285
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (546 546
          (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (540 10
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS))
     (491 151
          (:REWRITE RP::RP-EQUAL-SUBTERMS-REFLEXIVE))
     (440 220 (:REWRITE RP::RP-TERMP-CADDR))
     (440 220 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (420 420
          (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (399 111 (:REWRITE RP::RP-EQUAL-REFLEXIVE))
     (366 366 (:TYPE-PRESCRIPTION RP::TRANS-LIST))
     (360 10
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-LOOSESUBTERMS))
     (342 342
          (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (336 168
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (330 10
          (:DEFINITION RP::RP-EQUAL-LOOSE-SUBTERMS))
     (309 154
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (294 294 (:TYPE-PRESCRIPTION LEN))
     (294 42 (:DEFINITION LEN))
     (290 26
          (:REWRITE RP::RP-TRANS-LST-IS-LST-WHEN-LIST-IS-ABSENT))
     (285 285 (:TYPE-PRESCRIPTION QUOTEP))
     (270 270
          (:TYPE-PRESCRIPTION RP::RP-EQUAL-SUBTERMS))
     (268 92 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (253 154 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (253 154 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (253 154 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (253 154 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (253 154 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (253 154 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (253 154 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (253 154 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (253 154 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (253 154 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (253 154
          (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (253 154 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (252 126
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (252 42 (:DEFINITION ALL-NILS))
     (246 106
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (238 238 (:TYPE-PRESCRIPTION O-FINP))
     (238 149 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (238 149
          (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (238 149 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (238 149 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (230 230
          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (216 24
          (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (210 210 (:TYPE-PRESCRIPTION ALL-NILS))
     (200 126 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (185 185 (:TYPE-PRESCRIPTION RP::RP-EQUAL))
     (180 20
          (:REWRITE RP::RP-EQUAL2-SUBTERMS-REFLEXIVE))
     (168 168 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (160 10
          (:REWRITE RP::RP-EVLT-LST-OF-RP-EQUAL-LST))
     (126 126
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (118 118
          (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (100 100 (:LINEAR LEN-WHEN-PREFIXP))
     (98 26 (:REWRITE RP::RP-EVL-LST-OF-ATOM))
     (90 10 (:REWRITE RP::RP-EQUAL2-REFLEXIVE))
     (84 84
         (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
     (84 42 (:REWRITE DEFAULT-+-2))
     (50 50
         (:TYPE-PRESCRIPTION RP::RP-EQUAL2-SUBTERMS))
     (50 50
         (:TYPE-PRESCRIPTION RP::RP-EQUAL-LOOSE-SUBTERMS))
     (50 50 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
     (50 50 (:LINEAR BOUNDS-POSITION-EQUAL))
     (42 42 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (42 42 (:REWRITE DEFAULT-<-2))
     (42 42 (:REWRITE DEFAULT-<-1))
     (42 42 (:REWRITE DEFAULT-+-1))
     (40 40
         (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
     (40 20 (:REWRITE RP::RP-TERMP-CADDDR))
     (30 30 (:TYPE-PRESCRIPTION RP::RP-EQUAL2))
     (30 30
         (:TYPE-PRESCRIPTION RP::RP-EQUAL-LOOSE))
     (24 12 (:REWRITE RP::RP-TERMP-CADDDDR))
     (10 10
         (:REWRITE RP::RP-EVL-OF-TRANS-LIST-LEMMA-2)))
(RP::RP-VALID-TERMP-RP-EQUAL-ITER-PP+-META
     (584 2 (:DEFINITION RP::RP-TERMP))
     (398 2 (:DEFINITION RP::FALIST-CONSISTENT))
     (308 2
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (211 211 (:REWRITE DEFAULT-CDR))
     (147 147 (:REWRITE DEFAULT-CAR))
     (84 24 (:REWRITE O-P-O-INFP-CAR))
     (40 40 (:TYPE-PRESCRIPTION O-P))
     (32 8 (:REWRITE RP::IS-IF-RP-TERMP))
     (20 20 (:REWRITE O-P-DEF-O-FINP-1))
     (18 4
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (16 4 (:REWRITE RP::RP-TERMP-CADR))
     (16 4 (:REWRITE RP::RP-TERMP-CADDR))
     (16 4 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (14 2
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (12 12
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (12 2 (:REWRITE RP::NOT-INCLUDE-RP))
     (10 10 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (8 4 (:DEFINITION QUOTEP))
     (8 2
        (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (8 2 (:DEFINITION RP::INCLUDE-FNC))
     (7 7 (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (4 4
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (2 2 (:TYPE-PRESCRIPTION QUOTEP))
     (2 2 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
     (2 2
        (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)))
(RP::VALID-SC-RP-EQUAL-ITER-PP+-META
     (5422 3 (:DEFINITION RP::VALID-SC))
     (4461 36 (:DEFINITION RP::INCLUDE-FNC))
     (4067 3
           (:REWRITE RP::CAR-OF-EX-FROM-RP-IS-NOT-RP))
     (4045 28 (:DEFINITION RP::RP-TERMP))
     (2967 14 (:DEFINITION RP::RP-TERM-LISTP))
     (2347 13 (:DEFINITION RP::FALIST-CONSISTENT))
     (1771 11
           (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (1480 1458 (:REWRITE DEFAULT-CDR))
     (1452 84 (:REWRITE RP::IS-IF-RP-TERMP))
     (1115 1079 (:REWRITE DEFAULT-CAR))
     (856 33 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (850 33 (:REWRITE RP::RP-TERMP-CADDR))
     (694 51 (:REWRITE RP::RP-TERMP-CADR))
     (642 172 (:REWRITE O-P-O-INFP-CAR))
     (405 3 (:DEFINITION RP::EVAL-AND-ALL))
     (285 51
          (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (250 6 (:DEFINITION RP::RP-TRANS))
     (241 96 (:DEFINITION QUOTEP))
     (170 150 (:REWRITE O-P-DEF-O-FINP-1))
     (135 135
          (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
     (108 6 (:DEFINITION RP::TRANS-LIST))
     (102 51
          (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
     (100 6
          (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
     (99 99
         (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
     (99 30
         (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
     (87 87
         (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
     (84 6 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (81 7 (:REWRITE RP::NOT-INCLUDE-RP))
     (74 74
         (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
     (72 6 (:DEFINITION RP::IS-SYNP$INLINE))
     (72 4 (:DEFINITION RP::EX-FROM-RP))
     (71 71 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (71 3 (:REWRITE RP::VALID-SC-EX-FROM-RP))
     (60 12
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (54 54
         (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
     (54 54 (:TYPE-PRESCRIPTION QUOTEP))
     (48 6 (:DEFINITION RP::IS-FALIST))
     (46 46
         (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
     (38 10 (:REWRITE RP::VALID-SC-CADR))
     (37 7 (:REWRITE RP::VALID-SC-CADDR))
     (37 3 (:REWRITE RP::NOT-INCLUDE-EX-FROM-RP))
     (36 12 (:DEFINITION APPLY$-BADGEP))
     (36 6
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (36 3
         (:REWRITE RP::NOT-INCLUDE-RP-MEANS-VALID-SC-LST))
     (30 30
         (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (27 3
         (:DEFINITION RP::INCLUDE-FNC-SUBTERMS))
     (24 24 (:REWRITE RP::CONSP-RP-TRANS-LST))
     (24 12 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (20 20 (:TYPE-PRESCRIPTION O-FINP))
     (18 6 (:REWRITE RP::RP-EVL-OF-VARIABLE))
     (17 3 (:REWRITE RP::VALID-SC-OF-EX-FROM-RP))
     (16 3
         (:REWRITE RP::QUOTEP-TERM-WITH-EX-FROM-RP))
     (12 12
         (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
     (12 12
         (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP))
     (12 12 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (6 6
        (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
     (6 6 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-RP-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-QUOTE))
     (6 6
        (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-LAMBDA))
     (6 6
        (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-IF-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
     (6 6
        (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
     (6 6 (:REWRITE RP::RP-EVL-OF-<-CALL))
     (4 2 (:REWRITE RP::VALID-SC-CADDDR))
     (3 3 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
     (3 3 (:TYPE-PRESCRIPTION RP::EVAL-AND-ALL))
     (1 1 (:REWRITE RP::VALID-SC-NIL)))
(RP::DONT-RW-SYNTAXP-RP-EQUAL-ITER-PP+-META)
(RP::RP-EQUAL-ITER-PP+-META_FOR_EQUAL_VALID
     (584 2 (:DEFINITION RP::RP-TERMP))
     (431 1 (:DEFINITION RP::VALID-SC))
     (398 2 (:DEFINITION RP::FALIST-CONSISTENT))
     (341 326 (:REWRITE DEFAULT-CDR))
     (308 2
          (:DEFINITION RP::FALIST-CONSISTENT-AUX))
     (249 219 (:REWRITE DEFAULT-CAR))
     (195 5 (:DEFINITION RP::RP-TRANS))
     (139 14 (:DEFINITION RP::INCLUDE-FNC))
     (135 1 (:DEFINITION RP::EVAL-AND-ALL))
     (122 31 (:REWRITE O-P-O-INFP-CAR))
     (101 7
          (:REWRITE RP::NOT-INCLUDE-RP-MEANS-VALID-SC))
     (90 5 (:DEFINITION RP::TRANS-LIST))
     (57 5 (:REWRITE RP::EX-FROM-SYNP-LEMMA1))
     (54 54 (:TYPE-PRESCRIPTION O-P))
     (50 22 (:DEFINITION QUOTEP))
     (48 4 (:DEFINITION RP::IS-SYNP$INLINE))
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
     (18 3
         (:REWRITE RP::EVL-OF-EXTRACT-FROM-RP-2))
     (16 16 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (16 4 (:REWRITE RP::RP-TERMP-CADR))
     (16 4 (:REWRITE RP::RP-TERMP-CADDR))
     (16 4 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
     (15 1 (:REWRITE RP::VALID-SC-EX-FROM-RP))
     (15 1 (:DEFINITION RP::EX-FROM-RP))
     (14 2
         (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
     (13 5 (:REWRITE RP::RP-EVL-OF-VARIABLE))
     (12 12
         (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
     (12 12
         (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
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
     (6 6
        (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
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
        (:TYPE-PRESCRIPTION RP::IS-SYNP$INLINE))
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
