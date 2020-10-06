(GL::VARS-TO-BDD-BINDINGS)
(GL::BFR-SAT-BDDIFY)
(GL::UBDDP-VAL-ALISTP-VARS-TO-BDD-BINDINGS
     (32 28 (:REWRITE DEFAULT-CDR))
     (30 24 (:REWRITE DEFAULT-CAR))
     (30 3 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (28 28
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (12 3
         (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
     (9 9 (:REWRITE DEFAULT-<-2))
     (9 9 (:REWRITE DEFAULT-<-1))
     (9 3
        (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (7 7 (:REWRITE DEFAULT-+-2))
     (7 7 (:REWRITE DEFAULT-+-1))
     (6 6
        (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
     (6 6 (:TYPE-PRESCRIPTION ALISTP))
     (6 2 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (3 3
        (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
     (3 3 (:REWRITE ALISTP-WHEN-ATOM)))
(GL::HONS-ASSOC-EQUAL-VARS-TO-BDD-BINDINGS
     (314 314
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (301 148 (:REWRITE DEFAULT-+-2))
     (267 138 (:REWRITE DEFAULT-CDR))
     (220 52 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (192 148 (:REWRITE DEFAULT-+-1))
     (120 33
          (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (108 12 (:REWRITE SUBSETP-CAR-MEMBER))
     (101 98 (:REWRITE DEFAULT-CAR))
     (96 96 (:TYPE-PRESCRIPTION BOOLEANP))
     (80 64 (:REWRITE SUBSETP-MEMBER . 3))
     (79 15 (:REWRITE CONSP-OF-HONS-ASSOC-EQUAL))
     (64 64 (:REWRITE SUBSETP-MEMBER . 4))
     (54 18
         (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
     (52 52 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (52 52 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (51 51
         (:TYPE-PRESCRIPTION GL::VARS-TO-BDD-BINDINGS))
     (48 24 (:REWRITE DEFAULT-UNARY-MINUS))
     (42 14 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (41 38 (:REWRITE DEFAULT-<-1))
     (38 38 (:REWRITE DEFAULT-<-2))
     (38 38 (:META CANCEL_PLUS-LESSP-CORRECT))
     (31 31 (:REWRITE SUBSETP-MEMBER . 2))
     (31 31 (:REWRITE SUBSETP-MEMBER . 1))
     (28 28 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (24 12
         (:REWRITE LOOKUP-IN-BOOLEAN-VAL-ALIST))
     (14 14 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (14 14 (:REWRITE SUBSETP-TRANS2))
     (14 14 (:REWRITE SUBSETP-TRANS))
     (12 12
         (:TYPE-PRESCRIPTION BOOLEAN-VAL-ALISTP))
     (8 4
        (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (6 6
        (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY))
     (3 3
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (2 2 (:TYPE-PRESCRIPTION HONS-ACONS)))
(GL::VARS-TO-BDD-ENV)
(GL::NTH-VARS-TO-BDD-ENV
     (300 300
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (260 92
          (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (152 122 (:REWRITE DEFAULT-CDR))
     (98 84 (:REWRITE DEFAULT-CAR))
     (93 57 (:REWRITE DEFAULT-+-2))
     (73 45 (:REWRITE DEFAULT-<-2))
     (57 57 (:REWRITE DEFAULT-+-1))
     (57 15 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (55 55
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY))
     (47 47 (:META CANCEL_PLUS-LESSP-CORRECT))
     (47 45 (:REWRITE DEFAULT-<-1))
     (40 40
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (30 30 (:TYPE-PRESCRIPTION BOOLEANP))
     (18 3 (:REWRITE CONSP-OF-HONS-ASSOC-EQUAL))
     (17 17 (:REWRITE ZP-OPEN))
     (15 15 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (15 15 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(GL::LEN-MEMBER-EQUAL (108 108
                           (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                      (59 21 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                      (53 37 (:REWRITE SUBSETP-MEMBER . 3))
                      (43 25 (:REWRITE DEFAULT-+-2))
                      (37 37 (:REWRITE SUBSETP-MEMBER . 4))
                      (36 36 (:TYPE-PRESCRIPTION BOOLEANP))
                      (32 32 (:REWRITE DEFAULT-CDR))
                      (25 25 (:REWRITE DEFAULT-CAR))
                      (25 25 (:REWRITE DEFAULT-+-1))
                      (21 21 (:META CANCEL_TIMES-EQUAL-CORRECT))
                      (21 21 (:META CANCEL_PLUS-EQUAL-CORRECT))
                      (19 12 (:REWRITE DEFAULT-<-2))
                      (18 2 (:REWRITE SUBSETP-CAR-MEMBER))
                      (17 12 (:REWRITE DEFAULT-<-1))
                      (15 15 (:REWRITE SUBSETP-MEMBER . 2))
                      (15 15 (:REWRITE SUBSETP-MEMBER . 1))
                      (12 4 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
                      (8 8 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
                      (4 4 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
                      (4 4 (:REWRITE SUBSETP-TRANS2))
                      (4 4 (:REWRITE SUBSETP-TRANS)))
(GL::NTH-OF-INDEX (90 42 (:REWRITE DEFAULT-+-2))
                  (79 18 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                  (76 76
                      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                  (56 42 (:REWRITE DEFAULT-+-1))
                  (36 20 (:REWRITE SUBSETP-MEMBER . 3))
                  (34 34 (:TYPE-PRESCRIPTION BOOLEANP))
                  (30 5 (:REWRITE <-0-+-NEGATIVE-2))
                  (29 29 (:REWRITE DEFAULT-CDR))
                  (26 26 (:REWRITE DEFAULT-CAR))
                  (20 20 (:REWRITE SUBSETP-MEMBER . 4))
                  (20 10 (:REWRITE DEFAULT-UNARY-MINUS))
                  (18 18 (:META CANCEL_TIMES-EQUAL-CORRECT))
                  (18 18 (:META CANCEL_PLUS-EQUAL-CORRECT))
                  (18 7 (:REWRITE DEFAULT-<-2))
                  (18 2 (:REWRITE SUBSETP-CAR-MEMBER))
                  (12 12 (:META CANCEL_PLUS-LESSP-CORRECT))
                  (12 7 (:REWRITE DEFAULT-<-1))
                  (12 4 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
                  (9 9 (:REWRITE SUBSETP-MEMBER . 2))
                  (9 9 (:REWRITE SUBSETP-MEMBER . 1))
                  (8 8 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
                  (4 4 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
                  (4 4 (:REWRITE SUBSETP-TRANS2))
                  (4 4 (:REWRITE SUBSETP-TRANS)))
(GL::IDX-REWRITE (77 5 (:DEFINITION MEMBER-EQUAL))
                 (38 38
                     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                 (30 10 (:REWRITE MEMBER-WHEN-ATOM))
                 (18 9 (:REWRITE DEFAULT-+-2))
                 (15 5 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                 (13 13 (:REWRITE DEFAULT-CDR))
                 (12 2 (:REWRITE DEFAULT-<-1))
                 (10 10 (:TYPE-PRESCRIPTION BOOLEANP))
                 (10 10 (:REWRITE SUBSETP-MEMBER . 4))
                 (10 10 (:REWRITE SUBSETP-MEMBER . 3))
                 (10 9 (:REWRITE DEFAULT-+-1))
                 (5 5 (:REWRITE DEFAULT-CAR))
                 (5 5 (:META CANCEL_TIMES-EQUAL-CORRECT))
                 (5 5 (:META CANCEL_PLUS-EQUAL-CORRECT))
                 (4 2 (:REWRITE DEFAULT-<-2))
                 (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
                 (2 2 (:REWRITE SUBSETP-MEMBER . 2))
                 (2 2 (:REWRITE SUBSETP-MEMBER . 1))
                 (2 1 (:REWRITE DEFAULT-UNARY-MINUS)))
(GL::NTH-APPEND (306 306
                     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
                (160 80
                     (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                (138 54 (:REWRITE DEFAULT-CDR))
                (136 82 (:REWRITE DEFAULT-+-2))
                (86 82 (:REWRITE DEFAULT-+-1))
                (80 80 (:TYPE-PRESCRIPTION TRUE-LISTP))
                (80 80 (:TYPE-PRESCRIPTION BINARY-APPEND))
                (78 59 (:REWRITE DEFAULT-CAR))
                (66 22
                    (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
                (65 47 (:REWRITE DEFAULT-<-2))
                (64 24 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                (59 59 (:META CANCEL_PLUS-LESSP-CORRECT))
                (53 47 (:REWRITE DEFAULT-<-1))
                (32 32 (:TYPE-PRESCRIPTION BOOLEANP))
                (24 24 (:META CANCEL_TIMES-EQUAL-CORRECT))
                (24 24 (:META CANCEL_PLUS-EQUAL-CORRECT))
                (15 8 (:REWRITE DEFAULT-UNARY-MINUS))
                (15 3 (:REWRITE <-0-+-NEGATIVE-2))
                (6 6 (:REWRITE CDR-OF-APPEND-WHEN-CONSP)))
(GL::AIG-Q-COMPOSE-VARS-TO-BDD-ENV
     (6985 13 (:DEFINITION AIG-Q-COMPOSE))
     (6327 313 (:REWRITE SUBSETP-CAR-MEMBER))
     (3764 3764
           (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (3704 428 (:REWRITE SUBSETP-MEMBER . 2))
     (3203 356 (:REWRITE SUBSETP-TRANS2))
     (1542 254 (:DEFINITION LEN))
     (1442 80 (:DEFINITION BINARY-APPEND))
     (1440 1208 (:REWRITE DEFAULT-CDR))
     (1208 550 (:REWRITE DEFAULT-+-2))
     (1049 876 (:REWRITE DEFAULT-CAR))
     (1023 334 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (840 168 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (836 128 (:REWRITE ZP-OPEN))
     (804 134
          (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (733 140
          (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
     (688 182
          (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (682 550 (:REWRITE DEFAULT-+-1))
     (612 298 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (535 225 (:REWRITE DEFAULT-<-1))
     (480 40 (:DEFINITION GL::VARS-TO-BDD-ENV))
     (450 450 (:TYPE-PRESCRIPTION BOOLEANP))
     (438 438 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (438 438 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (428 428 (:REWRITE SUBSETP-MEMBER . 1))
     (426 225 (:REWRITE DEFAULT-<-2))
     (379 371 (:REWRITE SUBSETP-MEMBER . 3))
     (371 371 (:REWRITE SUBSETP-MEMBER . 4))
     (353 353 (:REWRITE SUBSETP-TRANS))
     (336 112 (:REWRITE SET::SFIX-WHEN-EMPTY))
     (282 81
          (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (252 26 (:REWRITE MEMBER-OF-CONS))
     (224 224
          (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (214 32 (:REWRITE SUBSETP-CONS-2))
     (189 9
          (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
     (182 94 (:REWRITE DEFAULT-UNARY-MINUS))
     (177 177
          (:TYPE-PRESCRIPTION GL::VARS-TO-BDD-BINDINGS))
     (116 108 (:REWRITE FOLD-CONSTS-IN-+))
     (102 6 (:REWRITE CONSP-OF-APPEND))
     (97 31 (:REWRITE REPEAT-WHEN-ZP))
     (90 15 (:DEFINITION Q-NOT))
     (84 12 (:REWRITE <-0-+-NEGATIVE-1))
     (78 78
         (:TYPE-PRESCRIPTION GL::VARS-TO-BDD-ENV))
     (68 68 (:TYPE-PRESCRIPTION ZP))
     (55 11 (:REWRITE CONSP-OF-HONS-ASSOC-EQUAL))
     (49 49
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY))
     (36 12
         (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (32 16
         (:REWRITE COMMUTATIVITY-OF-APPEND-UNDER-SET-EQUIV))
     (30 3 (:REWRITE <-+-NEGATIVE-0-1))
     (25 10 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
     (25 7 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
     (24 8
         (:REWRITE APPEND-OF-CONS-UNDER-SET-EQUIV))
     (15 15
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (15 15 (:DEFINITION HONS))
     (15 1
         (:REWRITE |(qs-subset y (q-and x y))|))
     (15 1
         (:REWRITE |(qs-subset x (q-and x y))|))
     (12 12 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (12 12
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (10 10
         (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
     (10 10
         (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
     (9 7
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (4 4
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (3 3 (:TYPE-PRESCRIPTION Q-NOT))
     (1 1 (:TYPE-PRESCRIPTION HONS-ACONS)))
(GL::BFR-SAT-BDDIFY-UNSAT
     (1045 36 (:DEFINITION AIG-VARS))
     (386 122
          (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
     (311 67 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
     (300 6 (:DEFINITION AIG-Q-COMPOSE))
     (218 218
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (216 27
          (:DEFINITION GL::VARS-TO-BDD-BINDINGS))
     (202 170 (:REWRITE DEFAULT-CAR))
     (195 195
          (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
     (192 24 (:REWRITE AIG-Q-COMPOSE-OF-VAR))
     (180 36 (:REWRITE SET::INSERT-IDENTITY))
     (166 166 (:TYPE-PRESCRIPTION BOOLEANP))
     (150 150 (:REWRITE DEFAULT-CDR))
     (150 14 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
     (146 146
          (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
     (144 144
          (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (126 9 (:DEFINITION GL::VARS-TO-BDD-ENV))
     (108 108 (:TYPE-PRESCRIPTION SET::IN-TYPE))
     (108 36 (:REWRITE SET::UNION-EMPTY-Y))
     (108 36 (:REWRITE SET::UNION-EMPTY-X))
     (96 8 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (84 14
         (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
     (72 72
         (:TYPE-PRESCRIPTION TRUE-LISTP-AIG-VARS))
     (72 36 (:REWRITE SET::IN-TAIL))
     (72 24 (:REWRITE AIG-Q-COMPOSE-OF-CONST))
     (52 17
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
     (50 50 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (50 50 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (48 8
         (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
     (45 9 (:DEFINITION HONS-GET))
     (42 6
         (:REWRITE AIG-Q-COMPOSE-OF-NOT-UNDER-BDD-EQUIV))
     (36 36 (:REWRITE SET::INSERT-WHEN-EMPTY))
     (36 6 (:DEFINITION Q-NOT))
     (30 10 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
     (27 27 (:DEFINITION HONS-ACONS))
     (27 9 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (24 24
         (:TYPE-PRESCRIPTION GL::VARS-TO-BDD-ENV))
     (24 8
         (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
     (24 8 (:REWRITE ALISTP-WHEN-ATOM))
     (24 6
         (:REWRITE AIG-Q-COMPOSE-OF-AND-UNDER-BDD-EQUIV))
     (18 18 (:TYPE-PRESCRIPTION BDD-SAT-DFS))
     (17 17
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (16 16
         (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
     (16 16 (:TYPE-PRESCRIPTION ALISTP))
     (16 8
         (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
     (14 14
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (14 14
         (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
     (10 10
         (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
     (10 10
         (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
     (9 9 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
     (9 9
        (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY))
     (8 8 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (6 6 (:DEFINITION HONS)))
