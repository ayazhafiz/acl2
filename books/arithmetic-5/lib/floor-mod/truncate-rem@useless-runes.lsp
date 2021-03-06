(REWRITE-TRUNCATE-TO-FLOOR
     (363 39 (:REWRITE REDUCE-RATIONALP-*))
     (192 192 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (192 192
          (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (192 192
          (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (192 192
          (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
     (192 192
          (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (187 45 (:REWRITE RATIONALP-X))
     (186 186
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (186 186
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (186 186
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (186 186
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (182 22 (:REWRITE ACL2-NUMBERP-X))
     (144 12 (:DEFINITION RFIX))
     (114 56 (:REWRITE DEFAULT-LESS-THAN-1))
     (68 32
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (68 32
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (63 63 (:REWRITE REDUCE-INTEGERP-+))
     (63 63 (:REWRITE INTEGERP-MINUS-X))
     (63 63 (:META META-INTEGERP-CORRECT))
     (61 32 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (56 56 (:REWRITE DEFAULT-LESS-THAN-2))
     (54 6 (:REWRITE RATIONALP-/))
     (49 49 (:REWRITE DEFAULT-TIMES-2))
     (46 11 (:REWRITE DEFAULT-MINUS))
     (42 42 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (42 42
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (42 42
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (42 42
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (42 42
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (42 42 (:REWRITE INTEGERP-<-CONSTANT))
     (42 42 (:REWRITE CONSTANT-<-INTEGERP))
     (42 42
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (42 42
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (42 42
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (42 42
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (42 42 (:REWRITE |(< c (- x))|))
     (42 42
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (42 42
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (42 42
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (42 42
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (42 42 (:REWRITE |(< (/ x) (/ y))|))
     (42 42 (:REWRITE |(< (- x) c)|))
     (42 42 (:REWRITE |(< (- x) (- y))|))
     (39 39 (:REWRITE REDUCE-RATIONALP-+))
     (39 39 (:REWRITE RATIONALP-MINUS-X))
     (39 39 (:META META-RATIONALP-CORRECT))
     (39 38 (:REWRITE |(equal (- x) (- y))|))
     (38 38
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (38 38
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (38 38 (:REWRITE |(equal c (/ x))|))
     (38 38 (:REWRITE |(equal c (- x))|))
     (38 38 (:REWRITE |(equal (/ x) c)|))
     (38 38 (:REWRITE |(equal (/ x) (/ y))|))
     (38 38 (:REWRITE |(equal (- x) c)|))
     (37 33
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (37 33 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (33 33 (:REWRITE SIMPLIFY-SUMS-<))
     (33 33
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (33 33
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (32 32
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (28 28
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (25 25 (:REWRITE |(< (/ x) 0)|))
     (25 25 (:REWRITE |(< (* x y) 0)|))
     (17 17
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (17 17
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (17 17 (:REWRITE |(< 0 (/ x))|))
     (17 17 (:REWRITE |(< 0 (* x y))|))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (10 6 (:REWRITE DEFAULT-PLUS-2))
     (7 6 (:REWRITE DEFAULT-PLUS-1))
     (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (6 6
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (6 6 (:REWRITE INTEGERP-/))
     (6 6 (:REWRITE |(not (equal x (/ y)))|))
     (6 6 (:REWRITE |(equal x (/ y))|))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (2 2
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1 (:REWRITE NORMALIZE-ADDENDS)))
(REWRITE-REM-TO-MOD
     (1246 246 (:REWRITE ACL2-NUMBERP-X))
     (671 18 (:REWRITE DEFAULT-MINUS))
     (669 29 (:REWRITE DEFAULT-PLUS-2))
     (590 590
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (590 590
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (590 590
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (590 590
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (558 153 (:REWRITE RATIONALP-X))
     (464 4 (:REWRITE FLOOR-ZERO . 3))
     (318 4 (:REWRITE CANCEL-FLOOR-+))
     (316 42 (:REWRITE DEFAULT-LESS-THAN-1))
     (276 50 (:REWRITE DEFAULT-LESS-THAN-2))
     (207 87
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (207 87
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (183 87 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (183 87 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (183 87
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (183 87
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (183 87
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (183 87
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (176 4 (:REWRITE FLOOR-ZERO . 5))
     (176 4 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (176 4 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (153 153 (:REWRITE REDUCE-RATIONALP-+))
     (153 153 (:REWRITE REDUCE-RATIONALP-*))
     (153 153 (:REWRITE RATIONALP-MINUS-X))
     (153 153 (:META META-RATIONALP-CORRECT))
     (153 81 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (153 81
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (153 81
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (153 81
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (153 81
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (153 81
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (153 81
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (150 4 (:REWRITE FLOOR-ZERO . 4))
     (146 4 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (146 4 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (135 135 (:REWRITE REDUCE-INTEGERP-+))
     (135 135 (:REWRITE INTEGERP-MINUS-X))
     (135 135 (:META META-INTEGERP-CORRECT))
     (126 4 (:REWRITE |(* (- x) y)|))
     (116 4 (:REWRITE FLOOR-=-X/Y . 3))
     (114 4
          (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (114 4 (:REWRITE FLOOR-CANCEL-*-CONST))
     (114 4
          (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (114 4
          (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (112 4 (:REWRITE FLOOR-ZERO . 2))
     (104 2 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (104 2 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (102 4 (:REWRITE FLOOR-=-X/Y . 2))
     (89 2 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (89 2 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (86 2 (:REWRITE MOD-ZERO . 4))
     (85 85
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (80 80
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (65 2 (:REWRITE MOD-CANCEL-*-CONST))
     (57 2
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (57 2
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (57 2
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (46 46 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (46 46 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (46 46 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (46 46 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (46 46 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (46 46
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (46 46
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (46 46 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (46 46 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (46 46
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (46 46
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (46 46 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (46 46 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (46 22
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (46 22 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (25 2
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (22 22 (:REWRITE SIMPLIFY-SUMS-<))
     (22 22
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (22 22
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (22 22
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (22 22
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (22 22 (:REWRITE INTEGERP-<-CONSTANT))
     (22 22 (:REWRITE CONSTANT-<-INTEGERP))
     (22 22
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (22 22
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (22 22
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (22 22
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (22 22 (:REWRITE |(< c (- x))|))
     (22 22
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (22 22
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (22 22
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (22 22
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (22 22 (:REWRITE |(< (/ x) (/ y))|))
     (22 22 (:REWRITE |(< (- x) c)|))
     (22 22 (:REWRITE |(< (- x) (- y))|))
     (17 2 (:REWRITE MOD-X-Y-=-X . 4))
     (17 2 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (16 2 (:REWRITE CANCEL-MOD-+))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (12 12 (:REWRITE |(< (/ x) 0)|))
     (12 12 (:REWRITE |(< (* x y) 0)|))
     (9 9
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 8 (:REWRITE |(< 0 (/ x))|))
     (8 8 (:REWRITE |(< 0 (* x y))|))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 6
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal c (- x))|))
     (6 6 (:REWRITE |(equal (/ x) c)|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (6 6 (:REWRITE |(- (* c x))|))
     (4 4
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (4 4 (:REWRITE |(floor x (- y))| . 2))
     (4 4 (:REWRITE |(floor x (- y))| . 1))
     (4 4
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (4 4 (:REWRITE |(floor (- x) y)| . 2))
     (4 4 (:REWRITE |(floor (- x) y)| . 1))
     (4 4
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (4 4
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (4 4
        (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (3 2 (:REWRITE MOD-ZERO . 3))
     (2 2 (:REWRITE MOD-X-Y-=-X . 3))
     (2 2 (:REWRITE MOD-X-Y-=-X . 2))
     (2 2
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:REWRITE |(mod x (- y))| . 3))
     (2 2 (:REWRITE |(mod x (- y))| . 2))
     (2 2 (:REWRITE |(mod x (- y))| . 1))
     (2 2
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (2 2 (:REWRITE |(mod (- x) y)| . 3))
     (2 2 (:REWRITE |(mod (- x) y)| . 2))
     (2 2 (:REWRITE |(mod (- x) y)| . 1))
     (2 2
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (2 2
        (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
     (2 2
        (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
     (2 2 (:REWRITE |(+ c (+ d x))|))
     (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN)))
(REWRITE-CEILING-TO-FLOOR
     (200 24 (:REWRITE ACL2-NUMBERP-X))
     (120 120 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (120 120
          (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (120 120
          (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (120 120
          (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
     (120 120
          (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (118 27 (:REWRITE RATIONALP-X))
     (100 100
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (100 100
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (100 100
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (100 100
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (80 26 (:REWRITE REDUCE-RATIONALP-*))
     (39 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (39 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (33 33 (:REWRITE DEFAULT-TIMES-2))
     (29 29 (:REWRITE REDUCE-INTEGERP-+))
     (29 29 (:REWRITE INTEGERP-MINUS-X))
     (29 29 (:META META-INTEGERP-CORRECT))
     (29 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (26 26 (:REWRITE REDUCE-RATIONALP-+))
     (26 26 (:REWRITE RATIONALP-MINUS-X))
     (26 26 (:META META-RATIONALP-CORRECT))
     (24 2 (:DEFINITION RFIX))
     (23 9 (:REWRITE DEFAULT-PLUS-2))
     (16 4 (:REWRITE DEFAULT-MINUS))
     (14 4 (:REWRITE DEFAULT-LESS-THAN-1))
     (13 13
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (13 13
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (11 9 (:REWRITE DEFAULT-PLUS-1))
     (9 1 (:REWRITE RATIONALP-/))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal c (- x))|))
     (6 6 (:REWRITE |(equal (/ x) c)|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE NORMALIZE-ADDENDS))
     (4 4 (:REWRITE INTEGERP-<-CONSTANT))
     (4 4 (:REWRITE DEFAULT-LESS-THAN-2))
     (4 4 (:REWRITE CONSTANT-<-INTEGERP))
     (4 4
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (4 4
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (4 4
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (4 4
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (4 4 (:REWRITE |(< c (- x))|))
     (4 4
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (4 4
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (4 4
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (4 4
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (/ x) (/ y))|))
     (4 4 (:REWRITE |(< (- x) c)|))
     (4 4 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (3 3 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (3 3
        (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (2 2
        (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (1 1 (:REWRITE INTEGERP-/))
     (1 1 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE |(equal x (/ y))|))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(REWRITE-ROUND-TO-FLOOR
     (3235 23
           (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (3170 23
           (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (2230 22
           (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (2204 740 (:REWRITE DEFAULT-PLUS-2))
     (2171 22
           (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (1805 400
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1693 740 (:REWRITE DEFAULT-PLUS-1))
     (1686 1144 (:REWRITE DEFAULT-TIMES-2))
     (1325 1325
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1325 1325
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1325 1325
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (1208 1208
           (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (1208 1208
           (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (1208 1208
           (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (1208 1208
           (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (1172 380 (:REWRITE |(< c (- x))|))
     (1145 428 (:REWRITE DEFAULT-LESS-THAN-1))
     (1096 370 (:REWRITE |(< (- x) c)|))
     (1024 302 (:REWRITE DEFAULT-MINUS))
     (1003 319
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (898 24 (:REWRITE CANCEL-MOD-+))
     (876 876
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (876 876
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (876 876
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (876 876
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (819 428 (:REWRITE DEFAULT-LESS-THAN-2))
     (671 23
          (:REWRITE |(< x (/ y)) with (< y 0)|))
     (670 22
          (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (659 23
          (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (646 22
          (:REWRITE |(< (/ x) y) with (< x 0)|))
     (614 24 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (607 14 (:REWRITE FLOOR-ZERO . 3))
     (605 24 (:REWRITE MOD-X-Y-=-X . 3))
     (580 24 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (576 98 (:REWRITE RATIONALP-X))
     (576 24 (:REWRITE MOD-X-Y-=-X . 4))
     (524 60 (:REWRITE ACL2-NUMBERP-X))
     (468 90 (:REWRITE REDUCE-RATIONALP-*))
     (463 463
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (462 14 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (451 14 (:REWRITE FLOOR-ZERO . 4))
     (430 14 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (422 14 (:REWRITE FLOOR-ZERO . 5))
     (406 380 (:REWRITE |(< (- x) (- y))|))
     (404 400
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (404 400
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (380 380
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (380 380
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (380 380
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (380 380
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (380 380
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (380 380
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (380 380
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (380 380
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (380 380 (:REWRITE |(< (/ x) (/ y))|))
     (360 24 (:REWRITE MOD-ZERO . 4))
     (348 14 (:REWRITE CANCEL-FLOOR-+))
     (318 24 (:REWRITE MOD-ZERO . 3))
     (289 275 (:META META-INTEGERP-CORRECT))
     (275 275 (:REWRITE REDUCE-INTEGERP-+))
     (268 268
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (266 14 (:REWRITE FLOOR-=-X/Y . 2))
     (255 71
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (255 71
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (242 14 (:REWRITE FLOOR-=-X/Y . 3))
     (220 24
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (219 219 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (219 219
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (219 219
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (218 218
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (218 218 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (218 218 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (217 217 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (217 217
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (210 14
          (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (192 32 (:REWRITE |(+ (* c x) (* d x))|))
     (192 24 (:REWRITE |(integerp (- x))|))
     (176 66 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (168 14 (:DEFINITION RFIX))
     (149 149 (:REWRITE |(< (* x y) 0)|))
     (143 143 (:REWRITE |(< (/ x) 0)|))
     (130 130
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (130 130
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (130 130
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (122 24 (:REWRITE |(mod x 1)|))
     (109 109
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (109 109
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (109 109
          (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (109 109
          (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (98 14 (:REWRITE |(floor x 1)|))
     (90 90 (:REWRITE REDUCE-RATIONALP-+))
     (90 90 (:REWRITE RATIONALP-MINUS-X))
     (90 90 (:META META-RATIONALP-CORRECT))
     (89 89
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (89 89
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (89 89 (:REWRITE |(equal (/ x) (/ y))|))
     (89 89 (:REWRITE |(< (+ c/d x) y)|))
     (84 8 (:LINEAR MOD-BOUNDS-3))
     (83 83 (:REWRITE |(equal c (/ x))|))
     (83 83 (:REWRITE |(equal c (- x))|))
     (83 83 (:REWRITE |(equal (/ x) c)|))
     (83 83 (:REWRITE |(equal (- x) c)|))
     (83 83 (:REWRITE |(< x (+ c/d y))|))
     (77 77 (:REWRITE |(< (+ (- c) x) y)|))
     (75 75 (:REWRITE |(< y (+ (- c) x))|))
     (72 8 (:REWRITE RATIONALP-/))
     (71 71
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (64 64
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (57 57
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (43 43 (:REWRITE FOLD-CONSTS-IN-+))
     (33 33 (:REWRITE |(< 0 (* x y))|))
     (31 31
         (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
     (31 31
         (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
     (29 29 (:REWRITE |(< 0 (/ x))|))
     (28 28
         (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
     (28 28
         (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
     (26 26
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (26 26
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (26 26
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (26 26
         (:REWRITE |(< 0 (* x (/ y))) rationalp (* x (/ y))|))
     (24 24 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (24 24 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (24 24 (:REWRITE MOD-X-Y-=-X . 2))
     (24 24
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (24 24
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (24 24 (:REWRITE MOD-CANCEL-*-CONST))
     (24 24 (:REWRITE |(mod x (- y))| . 3))
     (24 24 (:REWRITE |(mod x (- y))| . 2))
     (24 24 (:REWRITE |(mod x (- y))| . 1))
     (24 24
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (24 24
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (24 24 (:REWRITE |(mod (- x) y)| . 3))
     (24 24 (:REWRITE |(mod (- x) y)| . 2))
     (24 24 (:REWRITE |(mod (- x) y)| . 1))
     (24 24 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (24 24
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (24 24
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-4G))
     (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-3G))
     (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-2G))
     (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-1G))
     (20 17
         (:LINEAR NUMERATOR-GOES-DOWN-BY-INTEGER-DIVISION-LINEAR
                  . 4))
     (20 17
         (:LINEAR NUMERATOR-GOES-DOWN-BY-INTEGER-DIVISION-LINEAR
                  . 2))
     (16 16 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (16 16 (:REWRITE |(equal (+ (- c) x) y)|))
     (16 16 (:LINEAR MOD-BOUNDS-2))
     (16 10 (:REWRITE INTEGERP-/))
     (16 2 (:REWRITE INTEGERP-MOD-2))
     (16 2 (:REWRITE INTEGERP-MOD-1))
     (14 14 (:REWRITE FLOOR-ZERO . 2))
     (14 14 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (14 14 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (14 14
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (14 14
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (14 14 (:REWRITE FLOOR-CANCEL-*-CONST))
     (14 14 (:REWRITE |(floor x (- y))| . 2))
     (14 14 (:REWRITE |(floor x (- y))| . 1))
     (14 14
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (14 14
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (14 14 (:REWRITE |(floor (- x) y)| . 2))
     (14 14 (:REWRITE |(floor (- x) y)| . 1))
     (14 14
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (14 14 (:REWRITE |(equal (* x y) 0)|))
     (12 12 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (12 12 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (12 12 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (12 12 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (12 12
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (12 12
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (12 12
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (12 12
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (12 12
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (12 12
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (12 12
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (12 12
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (12 12
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (12 12
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (12 12
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (12 12
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (8 8 (:TYPE-PRESCRIPTION ABS))
     (7 7 (:REWRITE |(not (equal x (/ y)))|))
     (7 7 (:REWRITE |(equal x (/ y))|))
     (2 2
        (:REWRITE |(<= -1 (* x (/ y))) with (< y 0)|))
     (2 2
        (:REWRITE |(<= -1 (* x (/ y))) with (< 0 y)|))
     (2 2
        (:REWRITE |(< (* x (/ y)) -1) with (< y 0)|))
     (2 2
        (:REWRITE |(< (* x (/ y)) -1) with (< 0 y)|)))
(ASH-TO-FLOOR
 (195 24 (:REWRITE DEFAULT-TIMES-2))
 (163
  163
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (163 163
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (163
     163
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (163 163
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (163 163
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (163 163
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (154 154 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
 (154 154
      (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
 (154 154
      (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
 (154 154
      (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
 (116 4 (:REWRITE ODD-EXPT-THM))
 (112 4
      (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (112 4
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (112 4 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (112 4 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (72 36 (:REWRITE DEFAULT-LESS-THAN-2))
 (65 29 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (63 63 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (63 63 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (63 63 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (63 63 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (63 63
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (55 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (51 36 (:REWRITE DEFAULT-LESS-THAN-1))
 (42 24 (:REWRITE DEFAULT-TIMES-1))
 (40 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (39 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (39 3
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (39 3
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (39 3
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (39 3
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (32 32
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (32 32
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (32 32
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (32 32
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (32 32 (:REWRITE INTEGERP-<-CONSTANT))
 (32 32 (:REWRITE CONSTANT-<-INTEGERP))
 (32 32
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (32 32
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (32 32
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (32 32
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (32 32 (:REWRITE |(< c (- x))|))
 (32 32
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (32 32
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (32 32
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (32 32
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (32 32 (:REWRITE |(< (/ x) (/ y))|))
 (32 32 (:REWRITE |(< (- x) c)|))
 (32 32 (:REWRITE |(< (- x) (- y))|))
 (29 29 (:REWRITE SIMPLIFY-SUMS-<))
 (29 29
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (25 11 (:REWRITE DEFAULT-PLUS-2))
 (24 7 (:REWRITE DEFAULT-MINUS))
 (22 11 (:REWRITE DEFAULT-PLUS-1))
 (21 21 (:REWRITE REDUCE-INTEGERP-+))
 (21 21 (:REWRITE INTEGERP-MINUS-X))
 (21 21 (:META META-INTEGERP-CORRECT))
 (21 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (21 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (21 3
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (21 3
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (21 3
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (21 3
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (21 3
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (21 3
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (21 3
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (21 3
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (20 20
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (20 20
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (20 20
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (17 8 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (16 16 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (16 16 (:REWRITE |(< 0 (/ x))|))
 (16 16 (:REWRITE |(< 0 (* x y))|))
 (16 16 (:REWRITE |(< (/ x) 0)|))
 (16 16 (:REWRITE |(< (* x y) 0)|))
 (16 7
     (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
 (15 15
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (15 15 (:REWRITE DEFAULT-EXPT-1))
 (15 15 (:REWRITE |(expt 1/c n)|))
 (15 15 (:REWRITE |(expt (- x) n)|))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (10 9 (:REWRITE |(equal (- x) (- y))|))
 (9 9
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (9 9
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (9 9 (:REWRITE |(equal c (/ x))|))
 (9 9 (:REWRITE |(equal c (- x))|))
 (9 9 (:REWRITE |(equal (/ x) c)|))
 (9 9 (:REWRITE |(equal (/ x) (/ y))|))
 (9 9 (:REWRITE |(equal (- x) c)|))
 (8 8
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (4 4
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (4 4 (:REWRITE DEFAULT-DIVIDE))
 (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (3 3
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|)))
