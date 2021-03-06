(ORDP)
(ORDP-MY-DEL-REDUCTION (110 110 (:REWRITE DEFAULT-CDR))
                       (22 22 (:META CANCEL_TIMES-EQUAL-CORRECT))
                       (22 22 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(ORDP-DEDUCES-NOT-PERM-IF-<
     (2304 40
           (:REWRITE FALSIFIER-WITNESSES-FOR-HOW-MANY-IN-PERM))
     (1664 108 (:DEFINITION HOW-MANY))
     (726 726 (:TYPE-PRESCRIPTION HOW-MANY))
     (550 550 (:REWRITE DEFAULT-CDR))
     (388 194 (:REWRITE DEFAULT-+-2))
     (319 319 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (319 319 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (276 92 (:REWRITE UNICITY-OF-0))
     (202 49 (:REWRITE <<-ASYMMETRIC))
     (194 194 (:REWRITE DEFAULT-+-1))
     (184 92 (:DEFINITION FIX))
     (108 108
          (:REWRITE PERM-IMPLIES-HOW-MANY-EQUAL-NEW))
     (104 100 (:REWRITE <<-TRANSITIVE)))
(ORDP-CONSP-REDUCTION (76 6 (:DEFINITION HOW-MANY))
                      (44 44 (:TYPE-PRESCRIPTION HOW-MANY))
                      (31 31 (:REWRITE DEFAULT-CDR))
                      (20 10 (:REWRITE DEFAULT-+-2))
                      (15 5 (:REWRITE UNICITY-OF-0))
                      (14 10 (:REWRITE <<=-TRANSITIVE))
                      (10 10 (:REWRITE DEFAULT-+-1))
                      (10 5 (:DEFINITION FIX))
                      (9 9 (:META CANCEL_TIMES-EQUAL-CORRECT))
                      (9 9 (:META CANCEL_PLUS-EQUAL-CORRECT))
                      (8 2 (:REWRITE <<-ASYMMETRIC))
                      (6 6
                         (:REWRITE PERM-IMPLIES-HOW-MANY-EQUAL-NEW))
                      (4 4 (:REWRITE <<-TRANSITIVE))
                      (4 1 (:DEFINITION MY-DEL))
                      (1 1 (:TYPE-PRESCRIPTION MEMBERP)))
(PERM-ORDP-UNIQUE (316 22 (:DEFINITION HOW-MANY))
                  (209 209 (:REWRITE DEFAULT-CDR))
                  (180 180 (:TYPE-PRESCRIPTION HOW-MANY))
                  (168 168 (:REWRITE DEFAULT-CAR))
                  (94 12
                      (:REWRITE ORDP-DEDUCES-NOT-PERM-IF-<))
                  (84 42 (:REWRITE DEFAULT-+-2))
                  (63 21 (:REWRITE UNICITY-OF-0))
                  (44 44 (:META CANCEL_TIMES-EQUAL-CORRECT))
                  (44 44 (:META CANCEL_PLUS-EQUAL-CORRECT))
                  (42 42 (:REWRITE DEFAULT-+-1))
                  (42 21 (:DEFINITION FIX))
                  (22 22
                      (:REWRITE PERM-IMPLIES-HOW-MANY-EQUAL-NEW))
                  (12 12 (:TYPE-PRESCRIPTION <<))
                  (11 11 (:REWRITE <<-TRANSITIVE))
                  (10 10 (:REWRITE <<-IRREFLEXIVE)))
(ISORT-IS-A-PERMUTATION (1370 49
                              (:REWRITE ORDP-DEDUCES-NOT-PERM-IF-<))
                        (1189 85 (:DEFINITION ORDP))
                        (850 814 (:REWRITE DEFAULT-CDR))
                        (751 687 (:REWRITE DEFAULT-CAR))
                        (494 246 (:REWRITE DEFAULT-+-2))
                        (357 357 (:TYPE-PRESCRIPTION ORDP))
                        (348 116 (:REWRITE UNICITY-OF-0))
                        (335 16 (:REWRITE ORDP-MY-DEL-REDUCTION))
                        (318 318 (:TYPE-PRESCRIPTION INSERT))
                        (308 77 (:REWRITE <<-ASYMMETRIC))
                        (259 259 (:META CANCEL_TIMES-EQUAL-CORRECT))
                        (259 259 (:META CANCEL_PLUS-EQUAL-CORRECT))
                        (246 246 (:REWRITE DEFAULT-+-1))
                        (232 116 (:DEFINITION FIX))
                        (158 156 (:REWRITE <<-TRANSITIVE))
                        (118 118
                             (:REWRITE PERM-IMPLIES-HOW-MANY-EQUAL-NEW))
                        (103 103 (:REWRITE <<=-TRANSITIVE)))
(ISORT-IS-ORDERED (202 157 (:REWRITE DEFAULT-CDR))
                  (172 43 (:REWRITE <<-ASYMMETRIC))
                  (98 90 (:REWRITE <<-TRANSITIVE))
                  (4 4 (:REWRITE <<-IRREFLEXIVE)))
(INSERT-PRESERVES-TRUE-LISTP (24 6 (:REWRITE <<-ASYMMETRIC))
                             (15 13 (:REWRITE <<-TRANSITIVE))
                             (11 8 (:REWRITE DEFAULT-CDR))
                             (9 9 (:REWRITE DEFAULT-CAR))
                             (1 1 (:REWRITE CDR-CONS))
                             (1 1 (:REWRITE <<-IRREFLEXIVE)))
(ISORT-IS-A-TRUE-LISTP (34 3 (:DEFINITION INSERT))
                       (12 3 (:REWRITE <<-ASYMMETRIC))
                       (10 10 (:REWRITE DEFAULT-CDR))
                       (9 9 (:TYPE-PRESCRIPTION <<))
                       (9 9 (:REWRITE DEFAULT-CAR))
                       (6 6 (:REWRITE <<-TRANSITIVE)))
(ANY-ORDERED-PERMUTATION-OF-INTEGERS-IS-ISORT)
