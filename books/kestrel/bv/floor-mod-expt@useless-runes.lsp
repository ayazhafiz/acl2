(FLOOR-OF-SHIFTING-LEMMA2-HELPER
 (3792 94 (:REWRITE FLOOR-WHEN-<))
 (2973 1 (:REWRITE FLOOR-UNIQUE-EQUAL-VERSION))
 (2843 31
       (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
 (2482 43 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (1760 13
       (:LINEAR MY-FLOOR-LOWER-BOUND-ALT-LINEAR))
 (1586 13
       (:LINEAR *-OF-FLOOR-UPPER-BOUND-LINEAR))
 (1158 29 (:LINEAR MOD-BOUND-LINEAR-ARG2))
 (989 24 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (988 1
      (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (736 64 (:REWRITE MOD-WHEN-MULTIPLE))
 (730 730
      (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
 (730 730
      (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
 (567 387 (:REWRITE DEFAULT-*-2))
 (415 387 (:REWRITE DEFAULT-*-1))
 (398 270 (:REWRITE DEFAULT-<-2))
 (310 270 (:REWRITE DEFAULT-<-1))
 (295 5 (:REWRITE <-OF-*-AND-0))
 (176 64 (:REWRITE MOD-WHEN-<))
 (166 166 (:REWRITE DEFAULT-UNARY-/))
 (135 95
      (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (135 95
      (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (130 94
      (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (130 94
      (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (112 112
      (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP-ALT))
 (112 112 (:REWRITE INTEGERP-OF-*))
 (94 94
     (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (94 94 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
 (80 16 (:REWRITE DEFAULT-+-2))
 (67 67
     (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (65 13
     (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
 (64 64
     (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (64 64
     (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (64 64
     (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (64 64
     (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (55 5 (:REWRITE <-OF-FLOOR-AND-0))
 (48 48 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (48 48
     (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (48 48 (:LINEAR <-OF-*-AND-*))
 (40 29
     (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
 (39 13 (:DEFINITION NATP))
 (24 24 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (24 24 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (20 2 (:REWRITE <-OF-*-OF-/-ARG2-ARG2))
 (18 18 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (16 16 (:REWRITE DEFAULT-+-1))
 (15 5 (:REWRITE <-OF-FLOOR-AND-0-2))
 (14 14 (:REWRITE <-OF-0-AND-FLOOR))
 (14 6
     (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR))
 (13 13 (:TYPE-PRESCRIPTION NATP))
 (12 2 (:REWRITE /-OF-*))
 (10 2 (:REWRITE <-OF-/-AND-CONSTANT-1))
 (8 8
    (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 (7 7
    (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (6 3 (:REWRITE UNICITY-OF-1))
 (4 4 (:LINEAR <=-OF-/-LINEAR))
 (4 2 (:REWRITE /-OF-/))
 (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (1 1
    (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT)))
(FLOOR-OF-SHIFTING-LEMMA2
     (1926 10 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
     (1245 5
           (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
     (692 6 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (670 2
          (:LINEAR MY-FLOOR-LOWER-BOUND-ALT-LINEAR))
     (638 2
          (:LINEAR *-OF-FLOOR-UPPER-BOUND-LINEAR))
     (495 5 (:LINEAR MOD-BOUND-LINEAR-ARG2))
     (460 134 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
     (413 17 (:REWRITE FLOOR-WHEN-<))
     (320 2 (:REWRITE <-OF-*-AND-0))
     (310 10 (:REWRITE MOD-WHEN-<))
     (248 2 (:REWRITE <-OF-*-OF-/-ARG2-ARG1))
     (200 10 (:REWRITE MOD-WHEN-MULTIPLE))
     (200 10
          (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
     (198 198
          (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (198 198
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (180 48 (:REWRITE DEFAULT-*-2))
     (175 35 (:REWRITE DEFAULT-UNARY-/))
     (149 65 (:REWRITE DEFAULT-<-2))
     (134 134 (:LINEAR EXPT-BOUND-LINEAR))
     (110 5 (:REWRITE EQUAL-OF-0-AND-MOD))
     (86 48 (:REWRITE DEFAULT-*-1))
     (76 2 (:REWRITE <-OF-FLOOR-AND-0))
     (75 25
         (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP))
     (69 65 (:REWRITE DEFAULT-<-1))
     (51 17
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (30 10
         (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (30 10
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (25 25 (:REWRITE INTEGERP-OF-*))
     (18 2 (:REWRITE DEFAULT-+-2))
     (18 2
         (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR))
     (17 17
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (17 17
         (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (17 17
         (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (17 17
         (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (17 17 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (15 5 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (12 12 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (12 12
         (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (12 12 (:LINEAR <-OF-*-AND-*))
     (10 10
         (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (10 10
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (10 10
         (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
     (10 2
         (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
     (8 2 (:REWRITE UNICITY-OF-1))
     (6 6 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (6 6 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (6 6 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (6 6 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (6 6 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (6 2 (:REWRITE DEFAULT-+-1))
     (6 2 (:REWRITE <-OF-FLOOR-AND-0-2))
     (6 2 (:DEFINITION FIX))
     (5 5
        (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
     (4 4 (:REWRITE <-OF-0-AND-EXPT))
     (4 4 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
     (2 2 (:TYPE-PRESCRIPTION NATP))
     (2 2
        (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN)))
(MOD-OF-FLOOR-AND-EXPT-OF-ONE-LESS
     (130 5
          (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
     (100 5 (:REWRITE MOD-WHEN-MULTIPLE))
     (71 5 (:REWRITE MOD-WHEN-<))
     (68 2 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (50 10 (:REWRITE DEFAULT-UNARY-/))
     (41 41 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (40 10 (:REWRITE INTEGERP-OF-*))
     (34 14 (:REWRITE DEFAULT-*-2))
     (33 33
         (:TYPE-PRESCRIPTION FLOOR-TYPE-WHEN-NONPOSITIVE-AND-NONNEGATIVE))
     (33 33
         (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
     (33 33
         (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (30 10
         (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP))
     (24 14 (:REWRITE DEFAULT-<-2))
     (23 1 (:LINEAR FLOOR-BOUND-BETTER-LINEAR))
     (19 1 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
     (15 5
         (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (15 5
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (14 14 (:REWRITE DEFAULT-<-1))
     (14 14 (:REWRITE DEFAULT-*-1))
     (10 10
         (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (9 3 (:REWRITE FLOOR-WHEN-<))
     (7 1 (:REWRITE INTEGERP-OF-EXPT-WHEN-NATP))
     (6 6 (:LINEAR EXPT-BOUND-LINEAR))
     (6 2 (:REWRITE COMMUTATIVITY-OF-*))
     (5 5
        (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (5 5
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (5 5
        (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
     (4 2 (:REWRITE DEFAULT-+-2))
     (3 3
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (3 3
        (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (3 3
        (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (3 3
        (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (3 3
        (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (3 3 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (3 1
        (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
     (3 1
        (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
     (3 1 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
     (2 2 (:REWRITE DEFAULT-+-1)))
