(ASSOCIATIVITY-OF-B-AND (24 12 (:REWRITE EQUAL-1-HACK))
                        (18 6 (:DEFINITION BITP))
                        (12 12
                            (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
                        (6 6 (:TYPE-PRESCRIPTION BITP)))
(ASSOCIATIVITY-OF-B-IOR (24 12 (:REWRITE EQUAL-1-HACK))
                        (18 6 (:DEFINITION BITP))
                        (12 12
                            (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
                        (6 6 (:TYPE-PRESCRIPTION BITP)))
(SIMPLIFY-BIT-FUNCTIONS-2 (64 32 (:REWRITE EQUAL-1-HACK))
                          (48 16 (:DEFINITION BITP))
                          (32 32
                              (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
                          (16 16 (:TYPE-PRESCRIPTION BITP)))
(B-AND-B-IOR (56 28 (:REWRITE EQUAL-1-HACK))
             (42 14 (:DEFINITION BITP))
             (28 28
                 (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
             (14 14 (:TYPE-PRESCRIPTION BITP)))
(B-XOR-B-NOT (40 20 (:REWRITE EQUAL-1-HACK))
             (34 14 (:DEFINITION BITP))
             (20 20
                 (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
             (14 14 (:TYPE-PRESCRIPTION BITP)))
(B-XOR-CONSTANT)
(B-NOT-OPEN-0)
(B-NOT-OPEN-1)
(BFIX-B-FUNCTIONS (64 32 (:REWRITE EQUAL-1-HACK))
                  (48 16 (:DEFINITION BITP))
                  (32 32
                      (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
                  (16 16 (:TYPE-PRESCRIPTION BITP))
                  (2 2 (:REWRITE B-XOR-CONSTANT))
                  (2 2 (:REWRITE B-NOT-OPEN-1)))
(COMMUTATIVITY2-OF-B-FUNCTIONS (90 45 (:REWRITE EQUAL-1-HACK))
                               (76 20 (:REWRITE B-XOR-CONSTANT))
                               (68 28 (:DEFINITION BITP))
                               (49 49
                                   (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
                               (48 4 (:DEFINITION UNSIGNED-BYTE-P))
                               (36 4 (:DEFINITION INTEGER-RANGE-P))
                               (28 28 (:TYPE-PRESCRIPTION BITP))
                               (8 8 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                               (8 8
                                  (:REWRITE REMOVE-REDUNDANT-LESS-THANS))
                               (8 8 (:REWRITE DEFAULT-<-2))
                               (8 8 (:REWRITE DEFAULT-<-1))
                               (4 4 (:REWRITE REMOVE-REDUNDANT-<=-HYPS))
                               (4 4
                                  (:REWRITE INTEGER-RANGE-P-EXTEND-UPPER))
                               (4 4
                                  (:REWRITE INTEGER-RANGE-P-EXTEND-LOWER))
                               (4 4 (:REWRITE B-NOT-OPEN-1)))
(EQUAL-K-B-AND (45 9 (:REWRITE BFIX-BITP))
               (40 19 (:REWRITE EQUAL-1-HACK))
               (27 9 (:DEFINITION BITP))
               (18 18
                   (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
               (9 9 (:TYPE-PRESCRIPTION BITP))
               (1 1
                  (:REWRITE REMOVE-REDUNDANT-LESS-THANS))
               (1 1 (:REWRITE DEFAULT-<-2))
               (1 1 (:REWRITE DEFAULT-<-1)))
(EQUAL-K-B-IOR (40 8 (:REWRITE BFIX-BITP))
               (36 17 (:REWRITE EQUAL-1-HACK))
               (24 8 (:DEFINITION BITP))
               (16 16
                   (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
               (8 8 (:TYPE-PRESCRIPTION BITP))
               (1 1
                  (:REWRITE REMOVE-REDUNDANT-LESS-THANS))
               (1 1 (:REWRITE DEFAULT-<-2))
               (1 1 (:REWRITE DEFAULT-<-1)))
(B-XOR-REWRITE (31 7 (:REWRITE BFIX-BITP))
               (20 10 (:REWRITE EQUAL-1-HACK))
               (17 7 (:DEFINITION BITP))
               (10 10
                   (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
               (7 7 (:TYPE-PRESCRIPTION BITP))
               (2 2 (:REWRITE B-NOT-OPEN-1))
               (1 1 (:REWRITE B-XOR-CONSTANT)))
(B-EQV-REWRITE (31 7 (:REWRITE BFIX-BITP))
               (20 10 (:REWRITE EQUAL-1-HACK))
               (17 7 (:DEFINITION BITP))
               (10 10
                   (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
               (7 7 (:TYPE-PRESCRIPTION BITP))
               (2 2 (:REWRITE B-NOT-OPEN-1)))
(B-NOR-REWRITE (26 6 (:REWRITE BFIX-BITP))
               (24 1 (:REWRITE B-NOT-OPEN-1))
               (22 11 (:REWRITE EQUAL-1-HACK))
               (15 5 (:DEFINITION BITP))
               (11 11
                   (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
               (5 5 (:TYPE-PRESCRIPTION BITP)))
(B-NAND-REWRITE (26 6 (:REWRITE BFIX-BITP))
                (24 1 (:REWRITE B-NOT-OPEN-1))
                (22 11 (:REWRITE EQUAL-1-HACK))
                (15 5 (:DEFINITION BITP))
                (11 11
                    (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
                (5 5 (:TYPE-PRESCRIPTION BITP)))
(B-ANDC1-REWRITE (18 4 (:REWRITE BFIX-BITP))
                 (12 6 (:REWRITE EQUAL-1-HACK))
                 (10 4 (:DEFINITION BITP))
                 (6 6
                    (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
                 (4 4 (:TYPE-PRESCRIPTION BITP))
                 (1 1 (:REWRITE B-NOT-OPEN-1)))
(B-ANDC2-REWRITE (18 4 (:REWRITE BFIX-BITP))
                 (12 6 (:REWRITE EQUAL-1-HACK))
                 (10 4 (:DEFINITION BITP))
                 (6 6
                    (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
                 (4 4 (:TYPE-PRESCRIPTION BITP))
                 (1 1 (:REWRITE B-NOT-OPEN-1)))
(B-ORC1-REWRITE (18 4 (:REWRITE BFIX-BITP))
                (12 6 (:REWRITE EQUAL-1-HACK))
                (10 4 (:DEFINITION BITP))
                (6 6
                   (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
                (4 4 (:TYPE-PRESCRIPTION BITP))
                (1 1 (:REWRITE B-NOT-OPEN-1)))
(B-ORC2-REWRITE (18 4 (:REWRITE BFIX-BITP))
                (12 6 (:REWRITE EQUAL-1-HACK))
                (10 4 (:DEFINITION BITP))
                (6 6
                   (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
                (4 4 (:TYPE-PRESCRIPTION BITP))
                (1 1 (:REWRITE B-NOT-OPEN-1)))
(UNSIGNED-BYTE-P-B-XOR)
(UNSIGNED-BYTE-P-B-AND)
(UNSIGNED-BYTE-P-B-IOR)
(UNSIGNED-BYTE-P-B-FUNCTIONS (40 8 (:REWRITE BFIX-BITP))
                             (32 16 (:REWRITE EQUAL-1-HACK))
                             (24 8 (:DEFINITION BITP))
                             (20 20
                                 (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
                             (14 10 (:REWRITE DEFAULT-<-2))
                             (10 10 (:REWRITE REMOVE-REDUNDANT-<=-HYPS))
                             (10 10 (:REWRITE DEFAULT-<-1))
                             (8 8 (:TYPE-PRESCRIPTION BITP))
                             (4 4 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
                             (2 2
                                (:REWRITE INTEGER-RANGE-P-EXTEND-UPPER))
                             (2 2
                                (:REWRITE INTEGER-RANGE-P-EXTEND-LOWER))
                             (2 2
                                (:REWRITE EXPT-WHEN-I-IS-NOT-AN-INTEGERP)))
(B-XOR-EQUAL-0-REWRITE (24 12 (:REWRITE EQUAL-1-HACK))
                       (15 5 (:DEFINITION BITP))
                       (12 12
                           (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
                       (5 5 (:TYPE-PRESCRIPTION BITP))
                       (2 2 (:REWRITE B-NOT-OPEN-1)))
(B-XOR-EQUAL-1-REWRITE (20 10 (:REWRITE EQUAL-1-HACK))
                       (12 4 (:DEFINITION BITP))
                       (10 10
                           (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
                       (4 4 (:TYPE-PRESCRIPTION BITP))
                       (2 2 (:REWRITE B-NOT-OPEN-1)))
(B-IOR-UPPER-BOUND)
(UNSIGNED-BYTE-P-B-NOT (6 4 (:REWRITE DEFAULT-<-2))
                       (5 1 (:REWRITE BFIX-BITP))
                       (4 4
                          (:REWRITE REMOVE-REDUNDANT-LESS-THANS))
                       (4 4 (:REWRITE REMOVE-REDUNDANT-<=-HYPS))
                       (4 4 (:REWRITE DEFAULT-<-1))
                       (4 2 (:REWRITE EQUAL-1-HACK))
                       (3 3
                          (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
                       (3 1 (:DEFINITION BITP))
                       (2 2 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
                       (1 1 (:TYPE-PRESCRIPTION BITP))
                       (1 1
                          (:REWRITE INTEGER-RANGE-P-EXTEND-UPPER))
                       (1 1
                          (:REWRITE INTEGER-RANGE-P-EXTEND-LOWER))
                       (1 1
                          (:REWRITE EXPT-WHEN-I-IS-NOT-AN-INTEGERP))
                       (1 1 (:REWRITE B-NOT-OPEN-1)))
(LOGEXT-16-OF-B-NOT
     (114 114 (:TYPE-PRESCRIPTION MOD-TYPE . 4))
     (114 114 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
     (114 114 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
     (114 114 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
     (77 10
         (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
     (42 28 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
     (31 31 (:REWRITE REMOVE-REDUNDANT-<=-HYPS))
     (28 14
         (:REWRITE EXPT-WHEN-I-IS-NOT-AN-INTEGERP))
     (25 4 (:REWRITE DEFAULT-*-2))
     (22 19 (:REWRITE DEFAULT-<-2))
     (19 19 (:REWRITE DEFAULT-<-1))
     (16 4
         (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
     (16 4
         (:REWRITE MOD-WHEN-Y-IS-NOT-AN-ACL2-NUMBERP))
     (15 4
         (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 3))
     (14 14
         (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
     (14 14 (:REWRITE EXPONENTS-ADD))
     (13 4
         (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 2))
     (13 4 (:REWRITE DEFAULT-*-1))
     (12 3
         (:REWRITE FLOOR-WHEN-J-IS-NOT-AN-ACL2-NUMBERP))
     (12 1 (:REWRITE FOLD-CONSTS-IN-*))
     (10 7 (:REWRITE DEFAULT-+-2))
     (10 7 (:REWRITE DEFAULT-+-1))
     (10 5 (:REWRITE EQUAL-1-HACK))
     (10 2 (:REWRITE BFIX-BITP))
     (6 6
        (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
     (6 3 (:LINEAR EXPT-LESS-THAN-1-HACK))
     (6 2 (:DEFINITION BITP))
     (4 4
        (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 3))
     (4 4
        (:REWRITE MOD-WHEN-X-IS-NOT-AN-ACL2-NUMBERP))
     (4 1 (:REWRITE DEFAULT-UNARY-MINUS))
     (3 3
        (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (2 2 (:TYPE-PRESCRIPTION BITP))
     (2 2 (:REWRITE INTEGERP-+-MINUS-*-4))
     (2 2 (:REWRITE B-NOT-OPEN-1)))
(LOGHEAD-OF-B-NOT
     (36 4 (:LINEAR MOD-BOUNDED-BY-MODULUS))
     (24 24 (:TYPE-PRESCRIPTION MOD-TYPE . 4))
     (24 24 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
     (24 24 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
     (24 24 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
     (22 16 (:REWRITE DEFAULT-<-2))
     (22 16 (:REWRITE DEFAULT-<-1))
     (20 2 (:LINEAR MOD-TYPE . 4))
     (20 2 (:LINEAR MOD-TYPE . 3))
     (18 2 (:LINEAR MOD-TYPE . 2))
     (18 2 (:LINEAR MOD-TYPE . 1))
     (16 16
         (:REWRITE REMOVE-REDUNDANT-LESS-THANS))
     (10 2 (:REWRITE BFIX-BITP))
     (8 4 (:REWRITE EQUAL-1-HACK))
     (7 7 (:REWRITE REMOVE-REDUNDANT-<=-HYPS))
     (6 2 (:DEFINITION BITP))
     (5 5
        (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
     (5 1
        (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 3))
     (4 4 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
     (4 1
        (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 2))
     (3 1
        (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
     (3 1
        (:REWRITE MOD-WHEN-Y-IS-NOT-AN-ACL2-NUMBERP))
     (2 2 (:TYPE-PRESCRIPTION BITP))
     (2 2
        (:REWRITE EXPT-WHEN-I-IS-NOT-AN-INTEGERP))
     (2 2 (:REWRITE B-NOT-OPEN-1))
     (1 1
        (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 3))
     (1 1
        (:REWRITE MOD-WHEN-X-IS-NOT-AN-ACL2-NUMBERP))
     (1 1 (:LINEAR EXPT-LESS-THAN-1-HACK)))
(LOGTAIL-OF-B-NOT (144 24 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
                  (136 4 (:REWRITE FLOOR-=-X/Y . 3))
                  (81 49 (:REWRITE DEFAULT-<-2))
                  (80 4 (:REWRITE FLOOR-=-X/Y . 2))
                  (77 49 (:REWRITE DEFAULT-<-1))
                  (64 8 (:REWRITE INTEGERP-+-MINUS-*-4))
                  (64 4 (:REWRITE RTL1))
                  (64 4 (:REWRITE FLOOR-DETERMINED-1))
                  (55 15
                      (:REWRITE INTEGERP-*-CONSTANT-MEANS-1))
                  (49 49
                      (:REWRITE REMOVE-REDUNDANT-LESS-THANS))
                  (48 24 (:REWRITE DEFAULT-*-2))
                  (44 12 (:REWRITE DEFAULT-UNARY-/))
                  (44 6 (:REWRITE EQUAL-1-HACK))
                  (40 4 (:REWRITE FLOOR-TYPE-3 . 3))
                  (40 4 (:REWRITE FLOOR-TYPE-3 . 2))
                  (36 24 (:REWRITE DEFAULT-*-1))
                  (36 4 (:REWRITE FLOOR-TYPE-4 . 3))
                  (36 4 (:REWRITE FLOOR-TYPE-4 . 2))
                  (28 4 (:REWRITE INTEGERP-/))
                  (20 2 (:LINEAR FLOOR-TYPE-2 . 2))
                  (20 2 (:LINEAR FLOOR-TYPE-2 . 1))
                  (18 2 (:LINEAR X*Y>1-POSITIVE))
                  (18 2 (:LINEAR FLOOR-TYPE-1 . 2))
                  (18 2 (:LINEAR FLOOR-TYPE-1 . 1))
                  (18 2
                      (:LINEAR FLOOR-BOUNDED-BY-/-BETTER-2-ALT))
                  (18 2
                      (:LINEAR FLOOR-BOUNDED-BY-/-BETTER-1-ALT))
                  (16 8 (:REWRITE NUMERATOR-WHEN-INTEGERP))
                  (15 15
                      (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
                  (15 15
                      (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
                  (15 15
                      (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
                  (15 15 (:REWRITE REMOVE-REDUNDANT-<=-HYPS))
                  (12 4 (:REWRITE EQUAL-NEGATION-SAME-SIGN))
                  (11 5
                      (:REWRITE FLOOR-WHEN-J-IS-NOT-AN-ACL2-NUMBERP))
                  (9 5
                     (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
                  (6 2 (:REWRITE DEFAULT-+-2))
                  (5 1 (:REWRITE BFIX-BITP))
                  (4 4
                     (:REWRITE MOVE---TO-CONSTANT-IN-EQUAL))
                  (3 1 (:DEFINITION BITP))
                  (2 2 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
                  (2 2 (:REWRITE DEFAULT-+-1))
                  (1 1 (:TYPE-PRESCRIPTION BITP))
                  (1 1
                     (:REWRITE EXPT-WHEN-I-IS-NOT-AN-INTEGERP))
                  (1 1 (:REWRITE B-NOT-OPEN-1)))
