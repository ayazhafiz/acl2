(ALL-DEFUNS-IN-WORLD
     (200 8 (:DEFINITION FGETPROP))
     (148 74
          (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
     (147 129 (:REWRITE DEFAULT-CAR))
     (129 91 (:REWRITE DEFAULT-CDR))
     (118 118
          (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
     (88 44
         (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (12 6 (:DEFINITION TRUE-LISTP)))
(ENQUOTE-LIST)
(SYMBOLIC-LENGTH
     (380 31 (:DEFINITION LENGTH))
     (311 37 (:DEFINITION LEN))
     (301 145 (:REWRITE DEFAULT-+-2))
     (188 145 (:REWRITE DEFAULT-+-1))
     (104 26 (:REWRITE COMMUTATIVITY-OF-+))
     (104 26 (:DEFINITION INTEGER-ABS))
     (80 40
         (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
     (65 65
         (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
     (57 57
         (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (57 38 (:REWRITE STR::CONSP-OF-EXPLODE))
     (54 6 (:DEFINITION SYMBOL-LISTP))
     (50 25
         (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (41 32 (:REWRITE DEFAULT-<-2))
     (38 19
         (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (36 32 (:REWRITE DEFAULT-<-1))
     (26 26 (:REWRITE DEFAULT-UNARY-MINUS))
     (23 23
         (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (22 22
         (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (19 19
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (13 13 (:REWRITE DEFAULT-REALPART))
     (13 13 (:REWRITE DEFAULT-NUMERATOR))
     (13 13 (:REWRITE DEFAULT-IMAGPART))
     (13 13 (:REWRITE DEFAULT-DENOMINATOR))
     (6 6 (:TYPE-PRESCRIPTION SYMBOL-LISTP)))
(SYMBOLIC-ELEMENTS
     (380 31 (:DEFINITION LENGTH))
     (311 37 (:DEFINITION LEN))
     (301 145 (:REWRITE DEFAULT-+-2))
     (188 145 (:REWRITE DEFAULT-+-1))
     (104 26 (:REWRITE COMMUTATIVITY-OF-+))
     (104 26 (:DEFINITION INTEGER-ABS))
     (80 40
         (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
     (67 67 (:TYPE-PRESCRIPTION LEN))
     (65 65
         (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
     (57 57
         (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (57 38 (:REWRITE STR::CONSP-OF-EXPLODE))
     (54 6 (:DEFINITION SYMBOL-LISTP))
     (50 25
         (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (41 32 (:REWRITE DEFAULT-<-2))
     (38 19
         (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (36 32 (:REWRITE DEFAULT-<-1))
     (26 26 (:REWRITE DEFAULT-UNARY-MINUS))
     (23 23
         (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (22 22
         (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (19 19
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (13 13 (:REWRITE DEFAULT-REALPART))
     (13 13 (:REWRITE DEFAULT-NUMERATOR))
     (13 13 (:REWRITE DEFAULT-IMAGPART))
     (13 13 (:REWRITE DEFAULT-DENOMINATOR))
     (6 6 (:TYPE-PRESCRIPTION SYMBOL-LISTP)))
(SYMBOLIC-CAR
     (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (2 2 (:REWRITE DEFAULT-CDR))
     (2 2 (:REWRITE DEFAULT-CAR))
     (2 1
        (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
     (1 1
        (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP)))
(SYMBOLIC-CDR (6 6 (:REWRITE DEFAULT-CDR))
              (4 4 (:REWRITE DEFAULT-CAR))
              (3 3
                 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP)))
(SYMBOLIC-STRIP-CARS
     (1311 111 (:DEFINITION LENGTH))
     (1100 140 (:DEFINITION LEN))
     (839 399 (:REWRITE DEFAULT-+-2))
     (502 399 (:REWRITE DEFAULT-+-1))
     (384 192
          (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
     (304 304
          (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
     (275 275 (:TYPE-PRESCRIPTION LEN))
     (243 27 (:DEFINITION SYMBOL-LISTP))
     (240 60 (:REWRITE COMMUTATIVITY-OF-+))
     (240 60 (:DEFINITION INTEGER-ABS))
     (224 112
          (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (171 171
          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (171 114 (:REWRITE STR::CONSP-OF-EXPLODE))
     (114 57
          (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (96 74 (:REWRITE DEFAULT-<-2))
     (95 95
         (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (88 88
         (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (83 74 (:REWRITE DEFAULT-<-1))
     (60 60 (:REWRITE DEFAULT-UNARY-MINUS))
     (57 57
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (56 2 (:DEFINITION SYMBOLIC-LENGTH))
     (30 30 (:REWRITE DEFAULT-REALPART))
     (30 30 (:REWRITE DEFAULT-NUMERATOR))
     (30 30 (:REWRITE DEFAULT-IMAGPART))
     (30 30 (:REWRITE DEFAULT-DENOMINATOR))
     (28 1 (:DEFINITION SYMBOLIC-ELEMENTS))
     (27 27 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
     (5 1 (:DEFINITION ENQUOTE-LIST)))
(CHAR-TO-NAT)
(MAX-VAL-OF-CHARS)
(MY-PREFIXP)
(SYMBOL-TO-STRING (3 3 (:REWRITE DEFAULT-SYMBOL-NAME))
                  (3 3 (:REWRITE DEFAULT-CDR))
                  (3 3 (:REWRITE DEFAULT-CAR))
                  (1 1
                     (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME)))
(THING-BEING-CHECKEDP)
(THING-BEING-CHECKED-TO-STRING)
(CHECK-FIRST-ARG-AS-CTX)
(CHECK-KEYS-OF-ALIST-WRT-FORMAT-STRING)
(CHECK-CALL-OF-FMT-FUNCTION)
(CHECK-CALL-OF-HARD-ERROR)
(CHECK-CALL-OF-ILLEGAL)
(CHECK-CALL-OF-EQUAL)
(CHECK-CALL-OF-EQL)
(CHECK-CALL-OF-EQ)
(CHECK-CALL-OF-=)
(FILTER-SUBST)
(POSSIBLY-NEGATED-MBTP
     (206 16 (:DEFINITION LENGTH))
     (196 97 (:REWRITE DEFAULT-+-2))
     (166 18 (:DEFINITION LEN))
     (128 97 (:REWRITE DEFAULT-+-1))
     (122 86 (:REWRITE DEFAULT-CDR))
     (80 20 (:REWRITE COMMUTATIVITY-OF-+))
     (80 20 (:DEFINITION INTEGER-ABS))
     (36 36
         (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (36 24 (:REWRITE STR::CONSP-OF-EXPLODE))
     (31 25 (:REWRITE DEFAULT-<-2))
     (29 25 (:REWRITE DEFAULT-<-1))
     (28 28 (:TYPE-PRESCRIPTION LEN))
     (24 12
         (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
     (24 12
         (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (22 22
         (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
     (20 20 (:REWRITE DEFAULT-UNARY-MINUS))
     (20 10
         (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (18 2 (:DEFINITION SYMBOL-LISTP))
     (12 12
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (10 10 (:REWRITE DEFAULT-REALPART))
     (10 10 (:REWRITE DEFAULT-NUMERATOR))
     (10 10 (:REWRITE DEFAULT-IMAGPART))
     (10 10 (:REWRITE DEFAULT-DENOMINATOR))
     (9 9 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (5 5
        (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (2 2 (:TYPE-PRESCRIPTION SYMBOL-LISTP)))
(TRY-TO-RESOLVE)
(CHECK-CALL-OF-IF)
(CHECK-DEFUN)
(CHECK-DEFUNS)
(RUN-LINTER-FN)
