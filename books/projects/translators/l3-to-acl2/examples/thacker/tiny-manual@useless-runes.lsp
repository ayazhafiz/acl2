(CAST-FUNCT-TO-NAT)
(CAST-FUNCT-FROM-NAT)
(TYPE-FUNCT)
(ARB-FUNCT)
(ARB-FUNCT-IS-FUNCT)
(TYPE-FUNCT-LIST)
(CAST-SHIFTT-TO-NAT)
(CAST-SHIFTT-FROM-NAT)
(TYPE-SHIFTT)
(ARB-SHIFTT)
(ARB-SHIFTT-IS-SHIFTT)
(TYPE-SHIFTT-LIST)
(CAST-CONDITIONT-TO-NAT)
(CAST-CONDITIONT-FROM-NAT)
(TYPE-CONDITIONT)
(ARB-CONDITIONT)
(ARB-CONDITIONT-IS-CONDITIONT)
(TYPE-CONDITIONT-LIST)
(CAST-EXCEPTION-TO-NAT)
(CAST-EXCEPTION-FROM-NAT)
(TYPE-EXCEPTION)
(ARB-EXCEPTION)
(ARB-EXCEPTION-IS-EXCEPTION)
(TYPE-EXCEPTION-LIST)
(MAP-UPDATE-DMI-REC
     (28 4 (:DEFINITION LEN))
     (16 16 (:REWRITE DEFAULT-CDR))
     (9 5 (:REWRITE DEFAULT-PLUS-2))
     (8 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (8 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (7 7 (:REWRITE THE-FLOOR-BELOW))
     (7 7 (:REWRITE THE-FLOOR-ABOVE))
     (7 7 (:REWRITE SIMPLIFY-SUMS-<))
     (7 7
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (7 7
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (7 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (7 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7 7 (:REWRITE INTEGERP-<-CONSTANT))
     (7 7 (:REWRITE DEFAULT-LESS-THAN-2))
     (7 7 (:REWRITE DEFAULT-LESS-THAN-1))
     (7 7 (:REWRITE CONSTANT-<-INTEGERP))
     (7 7
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (7 7
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (7 7
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (7 7
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (7 7 (:REWRITE |(< c (- x))|))
     (7 7
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (7 7
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (7 7
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (7 7
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (7 7 (:REWRITE |(< (/ x) (/ y))|))
     (7 7 (:REWRITE |(< (- x) c)|))
     (7 7 (:REWRITE |(< (- x) (- y))|))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5 (:REWRITE NORMALIZE-ADDENDS))
     (5 5 (:REWRITE DEFAULT-PLUS-1))
     (5 5 (:REWRITE DEFAULT-CAR))
     (5 1 (:DEFINITION RP))
     (5 1 (:DEFINITION IMP))
     (5 1 (:DEFINITION DMP))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (2 1 (:DEFINITION TRUE-LISTP))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|)))
(MAP-UPDATE-DMI)
(MAP-UPDATE-IMI-REC
     (28 4 (:DEFINITION LEN))
     (16 16 (:REWRITE DEFAULT-CDR))
     (9 5 (:REWRITE DEFAULT-PLUS-2))
     (8 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (8 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (7 7 (:REWRITE THE-FLOOR-BELOW))
     (7 7 (:REWRITE THE-FLOOR-ABOVE))
     (7 7 (:REWRITE SIMPLIFY-SUMS-<))
     (7 7
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (7 7
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (7 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (7 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7 7 (:REWRITE INTEGERP-<-CONSTANT))
     (7 7 (:REWRITE DEFAULT-LESS-THAN-2))
     (7 7 (:REWRITE DEFAULT-LESS-THAN-1))
     (7 7 (:REWRITE CONSTANT-<-INTEGERP))
     (7 7
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (7 7
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (7 7
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (7 7
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (7 7 (:REWRITE |(< c (- x))|))
     (7 7
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (7 7
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (7 7
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (7 7
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (7 7 (:REWRITE |(< (/ x) (/ y))|))
     (7 7 (:REWRITE |(< (- x) c)|))
     (7 7 (:REWRITE |(< (- x) (- y))|))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5 (:REWRITE NORMALIZE-ADDENDS))
     (5 5 (:REWRITE DEFAULT-PLUS-1))
     (5 5 (:REWRITE DEFAULT-CAR))
     (5 1 (:DEFINITION RP))
     (5 1 (:DEFINITION IMP))
     (5 1 (:DEFINITION DMP))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (2 1 (:DEFINITION TRUE-LISTP))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|)))
(MAP-UPDATE-IMI)
(MAP-UPDATE-RI-REC
     (28 4 (:DEFINITION LEN))
     (16 16 (:REWRITE DEFAULT-CDR))
     (9 5 (:REWRITE DEFAULT-PLUS-2))
     (8 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (8 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (7 7 (:REWRITE THE-FLOOR-BELOW))
     (7 7 (:REWRITE THE-FLOOR-ABOVE))
     (7 7 (:REWRITE SIMPLIFY-SUMS-<))
     (7 7
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (7 7
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (7 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (7 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7 7 (:REWRITE INTEGERP-<-CONSTANT))
     (7 7 (:REWRITE DEFAULT-LESS-THAN-2))
     (7 7 (:REWRITE DEFAULT-LESS-THAN-1))
     (7 7 (:REWRITE CONSTANT-<-INTEGERP))
     (7 7
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (7 7
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (7 7
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (7 7
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (7 7 (:REWRITE |(< c (- x))|))
     (7 7
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (7 7
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (7 7
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (7 7
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (7 7 (:REWRITE |(< (/ x) (/ y))|))
     (7 7 (:REWRITE |(< (- x) c)|))
     (7 7 (:REWRITE |(< (- x) (- y))|))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5 (:REWRITE NORMALIZE-ADDENDS))
     (5 5 (:REWRITE DEFAULT-PLUS-1))
     (5 5 (:REWRITE DEFAULT-CAR))
     (5 1 (:DEFINITION RP))
     (5 1 (:DEFINITION IMP))
     (5 1 (:DEFINITION DMP))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (2 1 (:DEFINITION TRUE-LISTP))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|)))
(MAP-UPDATE-RI)
(FUNCTION0 (294 294 (:REWRITE DEFAULT-CDR))
           (203 70
                (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
           (198 102 (:REWRITE DEFAULT-PLUS-2))
           (139 70
                (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
           (102 102 (:REWRITE DEFAULT-PLUS-1))
           (101 101
                (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
           (101 101 (:REWRITE NORMALIZE-ADDENDS))
           (84 84 (:REWRITE DEFAULT-CAR))
           (80 80 (:REWRITE UNSIGNED-BYTE-P-MONOTONE))
           (80 16 (:REWRITE ACL2-NUMBERP-X))
           (70 70 (:REWRITE SIMPLIFY-SUMS-EQUAL))
           (70 70
               (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
           (70 70
               (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
           (70 70
               (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
           (70 70 (:REWRITE |(equal c (/ x))|))
           (70 70 (:REWRITE |(equal c (- x))|))
           (70 70 (:REWRITE |(equal (/ x) c)|))
           (70 70 (:REWRITE |(equal (/ x) (/ y))|))
           (70 70 (:REWRITE |(equal (- x) c)|))
           (70 70 (:REWRITE |(equal (- x) (- y))|))
           (65 13 (:DEFINITION RP))
           (65 13 (:DEFINITION IMP))
           (65 13 (:DEFINITION DMP))
           (32 8 (:REWRITE RATIONALP-X))
           (26 13 (:DEFINITION TRUE-LISTP))
           (9 9 (:REWRITE |(equal x (if a b c))|))
           (9 9 (:REWRITE |(equal (if a b c) x)|))
           (9 9 (:REWRITE |(+ x (if a b c))|))
           (8 8 (:REWRITE REDUCE-RATIONALP-+))
           (8 8 (:REWRITE REDUCE-RATIONALP-*))
           (8 8 (:REWRITE REDUCE-INTEGERP-+))
           (8 8 (:REWRITE RATIONALP-MINUS-X))
           (8 8 (:REWRITE INTEGERP-MINUS-X))
           (8 8 (:META META-RATIONALP-CORRECT))
           (8 8 (:META META-INTEGERP-CORRECT))
           (5 5
              (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
           (5 5
              (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
           (2 2 (:REWRITE DEFAULT-MINUS))
           (1 1
              (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
           (1 1
              (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
           (1 1
              (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
           (1 1
              (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(SHIFTER (50 9
             (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
         (40 8 (:REWRITE ACL2-NUMBERP-X))
         (28 14 (:REWRITE DEFAULT-PLUS-2))
         (21 21 (:REWRITE DEFAULT-CDR))
         (18 9
             (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
         (16 4 (:REWRITE RATIONALP-X))
         (14 14
             (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
         (14 14 (:REWRITE NORMALIZE-ADDENDS))
         (14 14 (:REWRITE DEFAULT-PLUS-1))
         (9 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
         (9 9
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
         (9 9
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
         (9 9
            (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
         (9 9 (:REWRITE |(equal c (/ x))|))
         (9 9 (:REWRITE |(equal c (- x))|))
         (9 9 (:REWRITE |(equal (/ x) c)|))
         (9 9 (:REWRITE |(equal (/ x) (/ y))|))
         (9 9 (:REWRITE |(equal (- x) c)|))
         (9 9 (:REWRITE |(equal (- x) (- y))|))
         (6 6 (:REWRITE DEFAULT-CAR))
         (4 4 (:REWRITE REDUCE-RATIONALP-+))
         (4 4 (:REWRITE REDUCE-RATIONALP-*))
         (4 4 (:REWRITE REDUCE-INTEGERP-+))
         (4 4 (:REWRITE RATIONALP-MINUS-X))
         (4 4 (:REWRITE INTEGERP-MINUS-X))
         (4 4 (:REWRITE |(equal x (if a b c))|))
         (4 4 (:REWRITE |(equal (if a b c) x)|))
         (4 4 (:META META-RATIONALP-CORRECT))
         (4 4 (:META META-INTEGERP-CORRECT))
         (1 1 (:REWRITE UNSIGNED-BYTE-P-MONOTONE)))
(ALU (1762 1762 (:REWRITE DEFAULT-CDR))
     (997 518 (:REWRITE DEFAULT-PLUS-2))
     (772 227
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (537 537 (:REWRITE DEFAULT-CAR))
     (518 518 (:REWRITE DEFAULT-PLUS-1))
     (514 514
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (514 514 (:REWRITE NORMALIZE-ADDENDS))
     (452 227
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (400 80 (:REWRITE ACL2-NUMBERP-X))
     (227 227 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (227 227
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (227 227
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (227 227
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (227 227 (:REWRITE |(equal c (/ x))|))
     (227 227 (:REWRITE |(equal c (- x))|))
     (227 227 (:REWRITE |(equal (/ x) c)|))
     (227 227 (:REWRITE |(equal (/ x) (/ y))|))
     (227 227 (:REWRITE |(equal (- x) c)|))
     (227 227 (:REWRITE |(equal (- x) (- y))|))
     (190 38 (:DEFINITION RP))
     (190 38 (:DEFINITION IMP))
     (190 38 (:DEFINITION DMP))
     (160 40 (:REWRITE RATIONALP-X))
     (76 38 (:DEFINITION TRUE-LISTP))
     (67 67 (:REWRITE |(+ x (if a b c))|))
     (40 40 (:REWRITE REDUCE-RATIONALP-+))
     (40 40 (:REWRITE REDUCE-RATIONALP-*))
     (40 40 (:REWRITE REDUCE-INTEGERP-+))
     (40 40 (:REWRITE RATIONALP-MINUS-X))
     (40 40 (:REWRITE INTEGERP-MINUS-X))
     (40 40 (:REWRITE DEFAULT-LOGAND-2))
     (40 40 (:REWRITE DEFAULT-LOGAND-1))
     (40 40 (:META META-RATIONALP-CORRECT))
     (40 40 (:META META-INTEGERP-CORRECT))
     (34 34 (:REWRITE |(equal x (if a b c))|))
     (34 34 (:REWRITE |(equal (if a b c) x)|))
     (12 4 (:DEFINITION UPDATE-NTH))
     (8 8 (:REWRITE DEFAULT-MINUS))
     (8 8 (:REWRITE DEFAULT-LOGXOR-2))
     (8 8 (:REWRITE DEFAULT-LOGXOR-1))
     (8 8 (:REWRITE DEFAULT-LOGIOR-2))
     (8 8 (:REWRITE DEFAULT-LOGIOR-1)))
(INCPC (205 205 (:REWRITE DEFAULT-CDR))
       (168 58
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
       (154 88 (:REWRITE DEFAULT-PLUS-2))
       (112 58
            (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
       (88 88 (:REWRITE DEFAULT-PLUS-1))
       (72 72
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
       (72 72 (:REWRITE NORMALIZE-ADDENDS))
       (70 14 (:REWRITE ACL2-NUMBERP-X))
       (69 69 (:REWRITE UNSIGNED-BYTE-P-MONOTONE))
       (61 61 (:REWRITE DEFAULT-CAR))
       (60 60
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
       (58 58 (:REWRITE SIMPLIFY-SUMS-EQUAL))
       (58 58
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
       (58 58 (:REWRITE |(equal c (/ x))|))
       (58 58 (:REWRITE |(equal c (- x))|))
       (58 58 (:REWRITE |(equal (/ x) c)|))
       (58 58 (:REWRITE |(equal (/ x) (/ y))|))
       (58 58 (:REWRITE |(equal (- x) c)|))
       (58 58 (:REWRITE |(equal (- x) (- y))|))
       (50 10 (:DEFINITION RP))
       (50 10 (:DEFINITION IMP))
       (50 10 (:DEFINITION DMP))
       (28 7 (:REWRITE RATIONALP-X))
       (21 21
           (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
       (21 21
           (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
       (20 10 (:DEFINITION TRUE-LISTP))
       (8 8 (:REWRITE DEFAULT-LOGAND-2))
       (8 8 (:REWRITE DEFAULT-LOGAND-1))
       (7 7 (:REWRITE REDUCE-RATIONALP-+))
       (7 7 (:REWRITE REDUCE-RATIONALP-*))
       (7 7 (:REWRITE REDUCE-INTEGERP-+))
       (7 7 (:REWRITE RATIONALP-MINUS-X))
       (7 7 (:REWRITE INTEGERP-MINUS-X))
       (7 7 (:META META-RATIONALP-CORRECT))
       (7 7 (:META META-INTEGERP-CORRECT))
       (5 5
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
       (4 4 (:REWRITE |(equal x (if a b c))|))
       (4 4 (:REWRITE |(equal (if a b c) x)|))
       (3 3 (:REWRITE THE-FLOOR-BELOW))
       (3 3 (:REWRITE THE-FLOOR-ABOVE))
       (3 3
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
       (3 3
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
       (3 3 (:REWRITE SIMPLIFY-SUMS-<))
       (3 3
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
       (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
       (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
       (3 3
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
       (3 3
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
       (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
       (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
       (3 3 (:REWRITE INTEGERP-<-CONSTANT))
       (3 3 (:REWRITE DEFAULT-LESS-THAN-2))
       (3 3 (:REWRITE DEFAULT-LESS-THAN-1))
       (3 3 (:REWRITE CONSTANT-<-INTEGERP))
       (3 3
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
       (3 3
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
       (3 3
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
       (3 3
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
       (3 3 (:REWRITE |(< c (- x))|))
       (3 3
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
       (3 3
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
       (3 3
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
       (3 3
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
       (3 3 (:REWRITE |(< (/ x) 0)|))
       (3 3 (:REWRITE |(< (/ x) (/ y))|))
       (3 3 (:REWRITE |(< (- x) c)|))
       (3 3 (:REWRITE |(< (- x) (- y))|))
       (3 3 (:REWRITE |(< (* x y) 0)|)))
(RP-YIELDS-UNSIGNED-BYTE-P-32
     (23 14 (:REWRITE DEFAULT-PLUS-2))
     (22 14 (:REWRITE DEFAULT-LESS-THAN-2))
     (19 13
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (18 11
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (18 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (17 11 (:REWRITE SIMPLIFY-SUMS-<))
     (14 14 (:REWRITE THE-FLOOR-BELOW))
     (14 14 (:REWRITE THE-FLOOR-ABOVE))
     (14 14
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (14 14
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (14 14
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 14 (:REWRITE NORMALIZE-ADDENDS))
     (14 14 (:REWRITE DEFAULT-PLUS-1))
     (14 14 (:REWRITE DEFAULT-LESS-THAN-1))
     (14 14 (:REWRITE DEFAULT-CAR))
     (13 13 (:REWRITE INTEGERP-<-CONSTANT))
     (13 13 (:REWRITE CONSTANT-<-INTEGERP))
     (13 13
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (13 13
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (13 13
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (13 13
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (13 13 (:REWRITE |(< c (- x))|))
     (13 13
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (13 13
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (13 13
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (13 13
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (13 13 (:REWRITE |(< (/ x) (/ y))|))
     (13 13 (:REWRITE |(< (- x) c)|))
     (13 13 (:REWRITE |(< (- x) (- y))|))
     (12 12 (:REWRITE DEFAULT-CDR))
     (7 7 (:REWRITE ZP-OPEN))
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:META META-INTEGERP-CORRECT))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|)))
(UNSIGNED-BYTE-P-ASH-NEGATIVE
 (68
   68
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (68
  68
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (68 68
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (68 68
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (68 68
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (68 68
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (52 2 (:LINEAR EXPT-X->=-X))
 (52 2 (:LINEAR EXPT-X->-X))
 (28 10 (:REWRITE SIMPLIFY-SUMS-<))
 (28 10
     (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
 (28 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (28 10 (:REWRITE DEFAULT-LESS-THAN-2))
 (10 10 (:REWRITE |arith (expt x c)|))
 (10 10 (:REWRITE |arith (expt 1/c n)|))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (10 10
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (10 10 (:REWRITE INTEGERP-<-CONSTANT))
 (10 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (10 10 (:REWRITE CONSTANT-<-INTEGERP))
 (10 10
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (10 10
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (10 10
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (10 10
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (10 10 (:REWRITE |(< c (- x))|))
 (10 10
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (10 10
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (10 10
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (10 10
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (10 10 (:REWRITE |(< (/ x) (/ y))|))
 (10 10 (:REWRITE |(< (- x) c)|))
 (10 10 (:REWRITE |(< (- x) (- y))|))
 (8 4 (:TYPE-PRESCRIPTION NATP-EXPT))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (4 4 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 1 (:REWRITE ASH-0))
 (3 3 (:REWRITE UNSIGNED-BYTE-P-MONOTONE))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:TYPE-PRESCRIPTION ZIP))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE ODD-EXPT-THM))
 (2 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE ZIP-OPEN))
 (1 1 (:REWRITE ASH-GOES-TO-0)))
(NORM (117624 216 (:REWRITE ASH-0))
      (114096 216 (:REWRITE ZIP-OPEN))
      (51200 1600 (:REWRITE ZP-OPEN))
      (29040 240 (:LINEAR LOGAND-BOUNDS-POS . 2))
      (26736 240 (:LINEAR LOGAND-UPPER-BOUND . 2))
      (24822 24822 (:REWRITE DEFAULT-CDR))
      (23712 3360
             (:REWRITE PREFER-POSITIVE-ADDENDS-<))
      (18240 3552
             (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
      (15055 7114 (:REWRITE DEFAULT-PLUS-2))
      (10032 1680
             (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
      (9696 3360
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
      (8890 7114 (:REWRITE DEFAULT-PLUS-1))
      (8400 240 (:LINEAR LOGAND-UPPER-BOUND . 1))
      (8160 240 (:LINEAR LOGAND-BOUNDS-POS . 1))
      (7754 1408
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
      (7440 3552 (:REWRITE DEFAULT-LESS-THAN-1))
      (7290 5850 (:REWRITE NORMALIZE-ADDENDS))
      (6624 192 (:REWRITE |(+ y (+ x z))|))
      (6196 6196 (:REWRITE DEFAULT-CAR))
      (5754 5754
            (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
      (5232 240 (:LINEAR LOGAND-BOUNDS-NEG . 2))
      (5232 240 (:LINEAR LOGAND-BOUNDS-NEG . 1))
      (4754 1408
            (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
      (4590 510 (:DEFINITION RP))
      (4416 3264 (:REWRITE SIMPLIFY-SUMS-<))
      (3984 3552 (:REWRITE DEFAULT-LESS-THAN-2))
      (3786 642 (:REWRITE ACL2-NUMBERP-X))
      (3648 3360 (:REWRITE |(< (- x) c)|))
      (3648 3360 (:REWRITE |(< (- x) (- y))|))
      (3552 3552 (:REWRITE THE-FLOOR-BELOW))
      (3552 3552 (:REWRITE THE-FLOOR-ABOVE))
      (3552 3552
            (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
      (3552 3552
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
      (3360 3360
            (:REWRITE REMOVE-STRICT-INEQUALITIES))
      (3360 3360 (:REWRITE INTEGERP-<-CONSTANT))
      (3360 3360 (:REWRITE CONSTANT-<-INTEGERP))
      (3360 3360
            (:REWRITE |(< c (/ x)) positive c --- present in goal|))
      (3360 3360
            (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
      (3360 3360
            (:REWRITE |(< c (/ x)) negative c --- present in goal|))
      (3360 3360
            (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
      (3360 3360 (:REWRITE |(< c (- x))|))
      (3360 3360
            (:REWRITE |(< (/ x) c) positive c --- present in goal|))
      (3360 3360
            (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
      (3360 3360
            (:REWRITE |(< (/ x) c) negative c --- present in goal|))
      (3360 3360
            (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
      (3360 3360 (:REWRITE |(< (/ x) (/ y))|))
      (3360 48 (:LINEAR LOGIOR-BOUNDS-POS . 2))
      (3360 48 (:LINEAR LOGIOR-BOUNDS-POS . 1))
      (3312 48 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
      (3312 48 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
      (3168 3168
            (:REWRITE REMOVE-WEAK-INEQUALITIES))
      (2944 544 (:REWRITE DEFAULT-LOGAND-2))
      (2688 384 (:REWRITE |(+ 0 x)|))
      (2112 1680
            (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
      (1924 1924
            (:REWRITE UNSIGNED-BYTE-P-MONOTONE))
      (1896 24 (:REWRITE LOGXOR-=-0))
      (1872 24 (:REWRITE LOGIOR-=-0))
      (1728 1296
            (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
      (1696 1408 (:REWRITE SIMPLIFY-SUMS-EQUAL))
      (1648 1648
            (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
      (1648 1648
            (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
      (1648 1648 (:REWRITE |(< 0 (/ x))|))
      (1648 1648 (:REWRITE |(< 0 (* x y))|))
      (1572 321 (:REWRITE RATIONALP-X))
      (1530 170 (:DEFINITION IMP))
      (1464 168
            (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
      (1408 1408
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
      (1408 1408
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
      (1408 1408
            (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
      (1408 1408 (:REWRITE |(equal c (/ x))|))
      (1408 1408 (:REWRITE |(equal c (- x))|))
      (1408 1408 (:REWRITE |(equal (/ x) c)|))
      (1408 1408 (:REWRITE |(equal (/ x) (/ y))|))
      (1408 1408 (:REWRITE |(equal (- x) c)|))
      (1408 1408 (:REWRITE |(equal (- x) (- y))|))
      (1296 1296 (:TYPE-PRESCRIPTION BINARY-LOGAND))
      (1216 1216 (:REWRITE |(< (* x y) 0)|))
      (1024 1024 (:REWRITE |(< (/ x) 0)|))
      (928 928
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
      (928 928
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
      (850 170 (:DEFINITION DMP))
      (789 789 (:REWRITE |(+ x (if a b c))|))
      (768 192 (:DEFINITION FIX))
      (640 544 (:REWRITE DEFAULT-LOGAND-1))
      (576 576
           (:TYPE-PRESCRIPTION NATP-ARB-UNSIGNED-BYTE))
      (456 168
           (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
      (456 168
           (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
      (456 168
           (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
      (384 384 (:REWRITE |(< (+ c/d x) y)|))
      (384 96 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
      (340 170 (:DEFINITION TRUE-LISTP))
      (321 321 (:REWRITE REDUCE-RATIONALP-+))
      (321 321 (:REWRITE REDUCE-RATIONALP-*))
      (321 321 (:REWRITE REDUCE-INTEGERP-+))
      (321 321 (:REWRITE RATIONALP-MINUS-X))
      (321 321 (:REWRITE INTEGERP-MINUS-X))
      (321 321 (:META META-RATIONALP-CORRECT))
      (321 321 (:META META-INTEGERP-CORRECT))
      (216 216 (:TYPE-PRESCRIPTION ZIP))
      (216 216
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
      (216 216 (:REWRITE ASH-GOES-TO-0))
      (192 192 (:REWRITE |(< (+ (- c) x) y)|))
      (192 96 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
      (168 168 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
      (168 168 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
      (144 48 (:LINEAR ARB32-UPPER-BOUND))
      (134 134 (:REWRITE |(equal x (if a b c))|))
      (134 134 (:REWRITE |(equal (if a b c) x)|))
      (128 32 (:REWRITE DEFAULT-MINUS))
      (128 32 (:REWRITE DEFAULT-LOGXOR-2))
      (128 32 (:REWRITE DEFAULT-LOGXOR-1))
      (128 32 (:REWRITE DEFAULT-LOGIOR-2))
      (128 32 (:REWRITE DEFAULT-LOGIOR-1))
      (96 96 (:REWRITE |(+ x (- x))|))
      (96 32 (:DEFINITION UPDATE-NTH))
      (32 32 (:REWRITE |(equal (+ (- c) x) y)|)))
(DFN-NORMAL (102792 51396
                    (:TYPE-PRESCRIPTION RP-YIELDS-UNSIGNED-BYTE-P-32))
            (17811 17811 (:REWRITE DEFAULT-CDR))
            (5738 2874 (:REWRITE DEFAULT-PLUS-2))
            (3983 3983 (:REWRITE DEFAULT-CAR))
            (3672 408 (:DEFINITION RP))
            (3264 272
                  (:REWRITE RP-YIELDS-UNSIGNED-BYTE-P-32))
            (3130 855
                  (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
            (2874 2874
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
            (2874 2874 (:REWRITE NORMALIZE-ADDENDS))
            (2874 2874 (:REWRITE DEFAULT-PLUS-1))
            (1780 356 (:REWRITE ACL2-NUMBERP-X))
            (1706 855
                  (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
            (1224 136 (:DEFINITION IMP))
            (855 855 (:REWRITE SIMPLIFY-SUMS-EQUAL))
            (855 855
                 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
            (855 855
                 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
            (855 855
                 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
            (855 855 (:REWRITE |(equal c (/ x))|))
            (855 855 (:REWRITE |(equal c (- x))|))
            (855 855 (:REWRITE |(equal (/ x) c)|))
            (855 855 (:REWRITE |(equal (/ x) (/ y))|))
            (855 855 (:REWRITE |(equal (- x) c)|))
            (855 855 (:REWRITE |(equal (- x) (- y))|))
            (712 178 (:REWRITE RATIONALP-X))
            (680 136 (:DEFINITION DMP))
            (522 522 (:REWRITE |(+ x (if a b c))|))
            (272 136 (:DEFINITION TRUE-LISTP))
            (178 178 (:REWRITE REDUCE-RATIONALP-+))
            (178 178 (:REWRITE REDUCE-RATIONALP-*))
            (178 178 (:REWRITE REDUCE-INTEGERP-+))
            (178 178 (:REWRITE RATIONALP-MINUS-X))
            (178 178 (:REWRITE INTEGERP-MINUS-X))
            (178 178 (:META META-RATIONALP-CORRECT))
            (178 178 (:META META-INTEGERP-CORRECT))
            (132 132 (:REWRITE |(equal x (if a b c))|))
            (132 132 (:REWRITE |(equal (if a b c) x)|)))
(DFN-STOREDM
     (23420 23420
            (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (20480 640 (:REWRITE ZP-OPEN))
     (19217 19217 (:REWRITE DEFAULT-CDR))
     (7619 1731
           (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
     (7424 128 (:LINEAR LOGAND-UPPER-BOUND . 2))
     (6634 3642 (:REWRITE DEFAULT-PLUS-2))
     (4621 4621 (:REWRITE DEFAULT-CAR))
     (3968 1536
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3968 1536
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3672 408 (:DEFINITION RP))
     (3642 3642
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3642 3642 (:REWRITE NORMALIZE-ADDENDS))
     (3642 3642 (:REWRITE DEFAULT-PLUS-1))
     (3200 1536 (:REWRITE DEFAULT-LESS-THAN-1))
     (3110 853
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2112 2112 (:TYPE-PRESCRIPTION NATP))
     (2048 512 (:REWRITE DEFAULT-LOGAND-2))
     (1760 352 (:REWRITE ACL2-NUMBERP-X))
     (1702 853
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1664 1664 (:REWRITE THE-FLOOR-BELOW))
     (1664 1664 (:REWRITE THE-FLOOR-ABOVE))
     (1536 1536 (:REWRITE SIMPLIFY-SUMS-<))
     (1536 1536
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1536 1536
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1536 1536
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1536 1536
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1536 1536
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1536 1536 (:REWRITE INTEGERP-<-CONSTANT))
     (1536 1536 (:REWRITE DEFAULT-LESS-THAN-2))
     (1536 1536 (:REWRITE CONSTANT-<-INTEGERP))
     (1536 1536
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1536 1536
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1536 1536
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1536 1536
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1536 1536 (:REWRITE |(< c (- x))|))
     (1536 1536
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1536 1536
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1536 1536
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1536 1536
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1536 1536 (:REWRITE |(< (/ x) (/ y))|))
     (1536 1536 (:REWRITE |(< (- x) c)|))
     (1536 1536 (:REWRITE |(< (- x) (- y))|))
     (1224 136 (:DEFINITION IMP))
     (853 853 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (853 853
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (853 853
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (853 853
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (853 853 (:REWRITE |(equal c (/ x))|))
     (853 853 (:REWRITE |(equal c (- x))|))
     (853 853 (:REWRITE |(equal (/ x) c)|))
     (853 853 (:REWRITE |(equal (/ x) (/ y))|))
     (853 853 (:REWRITE |(equal (- x) c)|))
     (853 853 (:REWRITE |(equal (- x) (- y))|))
     (704 176 (:REWRITE RATIONALP-X))
     (680 136 (:DEFINITION DMP))
     (640 640
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (640 640
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (640 640 (:REWRITE |(< 0 (/ x))|))
     (640 640 (:REWRITE |(< 0 (* x y))|))
     (522 522 (:REWRITE |(+ x (if a b c))|))
     (512 512 (:REWRITE DEFAULT-LOGAND-1))
     (384 384
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (384 384
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (384 384 (:REWRITE |(< (/ x) 0)|))
     (384 384 (:REWRITE |(< (* x y) 0)|))
     (272 136 (:DEFINITION TRUE-LISTP))
     (176 176 (:REWRITE REDUCE-RATIONALP-+))
     (176 176 (:REWRITE REDUCE-RATIONALP-*))
     (176 176 (:REWRITE REDUCE-INTEGERP-+))
     (176 176 (:REWRITE RATIONALP-MINUS-X))
     (176 176 (:REWRITE INTEGERP-MINUS-X))
     (176 176 (:META META-RATIONALP-CORRECT))
     (176 176 (:META META-INTEGERP-CORRECT))
     (132 132 (:REWRITE |(equal x (if a b c))|))
     (132 132 (:REWRITE |(equal (if a b c) x)|)))
(DFN-STOREIM
     (23420 23420
            (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (20480 640 (:REWRITE ZP-OPEN))
     (19217 19217 (:REWRITE DEFAULT-CDR))
     (7619 1731
           (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
     (7424 128 (:LINEAR LOGAND-UPPER-BOUND . 2))
     (6634 3642 (:REWRITE DEFAULT-PLUS-2))
     (4621 4621 (:REWRITE DEFAULT-CAR))
     (3968 1536
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3968 1536
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3672 408 (:DEFINITION RP))
     (3642 3642
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3642 3642 (:REWRITE NORMALIZE-ADDENDS))
     (3642 3642 (:REWRITE DEFAULT-PLUS-1))
     (3200 1536 (:REWRITE DEFAULT-LESS-THAN-1))
     (3110 853
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2112 2112 (:TYPE-PRESCRIPTION NATP))
     (2048 512 (:REWRITE DEFAULT-LOGAND-2))
     (1760 352 (:REWRITE ACL2-NUMBERP-X))
     (1702 853
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1664 1664 (:REWRITE THE-FLOOR-BELOW))
     (1664 1664 (:REWRITE THE-FLOOR-ABOVE))
     (1536 1536 (:REWRITE SIMPLIFY-SUMS-<))
     (1536 1536
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1536 1536
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1536 1536
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1536 1536
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1536 1536
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1536 1536 (:REWRITE INTEGERP-<-CONSTANT))
     (1536 1536 (:REWRITE DEFAULT-LESS-THAN-2))
     (1536 1536 (:REWRITE CONSTANT-<-INTEGERP))
     (1536 1536
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1536 1536
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1536 1536
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1536 1536
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1536 1536 (:REWRITE |(< c (- x))|))
     (1536 1536
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1536 1536
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1536 1536
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1536 1536
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1536 1536 (:REWRITE |(< (/ x) (/ y))|))
     (1536 1536 (:REWRITE |(< (- x) c)|))
     (1536 1536 (:REWRITE |(< (- x) (- y))|))
     (1224 136 (:DEFINITION IMP))
     (853 853 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (853 853
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (853 853
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (853 853
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (853 853 (:REWRITE |(equal c (/ x))|))
     (853 853 (:REWRITE |(equal c (- x))|))
     (853 853 (:REWRITE |(equal (/ x) c)|))
     (853 853 (:REWRITE |(equal (/ x) (/ y))|))
     (853 853 (:REWRITE |(equal (- x) c)|))
     (853 853 (:REWRITE |(equal (- x) (- y))|))
     (704 176 (:REWRITE RATIONALP-X))
     (680 136 (:DEFINITION DMP))
     (640 640
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (640 640
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (640 640 (:REWRITE |(< 0 (/ x))|))
     (640 640 (:REWRITE |(< 0 (* x y))|))
     (522 522 (:REWRITE |(+ x (if a b c))|))
     (512 512 (:REWRITE DEFAULT-LOGAND-1))
     (384 384
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (384 384
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (384 384 (:REWRITE |(< (/ x) 0)|))
     (384 384 (:REWRITE |(< (* x y) 0)|))
     (272 136 (:DEFINITION TRUE-LISTP))
     (176 176 (:REWRITE REDUCE-RATIONALP-+))
     (176 176 (:REWRITE REDUCE-RATIONALP-*))
     (176 176 (:REWRITE REDUCE-INTEGERP-+))
     (176 176 (:REWRITE RATIONALP-MINUS-X))
     (176 176 (:REWRITE INTEGERP-MINUS-X))
     (176 176 (:META META-RATIONALP-CORRECT))
     (176 176 (:META META-INTEGERP-CORRECT))
     (132 132 (:REWRITE |(equal x (if a b c))|))
     (132 132 (:REWRITE |(equal (if a b c) x)|)))
(DFN-OUT (102792 51396
                 (:TYPE-PRESCRIPTION RP-YIELDS-UNSIGNED-BYTE-P-32))
         (17811 17811 (:REWRITE DEFAULT-CDR))
         (5738 2874 (:REWRITE DEFAULT-PLUS-2))
         (3983 3983 (:REWRITE DEFAULT-CAR))
         (3672 408 (:DEFINITION RP))
         (3264 272
               (:REWRITE RP-YIELDS-UNSIGNED-BYTE-P-32))
         (3130 855
               (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
         (2874 2874
               (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
         (2874 2874 (:REWRITE NORMALIZE-ADDENDS))
         (2874 2874 (:REWRITE DEFAULT-PLUS-1))
         (1780 356 (:REWRITE ACL2-NUMBERP-X))
         (1706 855
               (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
         (1224 136 (:DEFINITION IMP))
         (855 855 (:REWRITE SIMPLIFY-SUMS-EQUAL))
         (855 855
              (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
         (855 855
              (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
         (855 855
              (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
         (855 855 (:REWRITE |(equal c (/ x))|))
         (855 855 (:REWRITE |(equal c (- x))|))
         (855 855 (:REWRITE |(equal (/ x) c)|))
         (855 855 (:REWRITE |(equal (/ x) (/ y))|))
         (855 855 (:REWRITE |(equal (- x) c)|))
         (855 855 (:REWRITE |(equal (- x) (- y))|))
         (712 178 (:REWRITE RATIONALP-X))
         (680 136 (:DEFINITION DMP))
         (522 522 (:REWRITE |(+ x (if a b c))|))
         (272 136 (:DEFINITION TRUE-LISTP))
         (178 178 (:REWRITE REDUCE-RATIONALP-+))
         (178 178 (:REWRITE REDUCE-RATIONALP-*))
         (178 178 (:REWRITE REDUCE-INTEGERP-+))
         (178 178 (:REWRITE RATIONALP-MINUS-X))
         (178 178 (:REWRITE INTEGERP-MINUS-X))
         (178 178 (:META META-RATIONALP-CORRECT))
         (178 178 (:META META-INTEGERP-CORRECT))
         (132 132 (:REWRITE |(equal x (if a b c))|))
         (132 132 (:REWRITE |(equal (if a b c) x)|)))
(DMP-YIELDS-UNSIGNED-BYTE-P-32
     (60 5
         (:REWRITE RP-YIELDS-UNSIGNED-BYTE-P-32))
     (45 5 (:DEFINITION RP))
     (23 14 (:REWRITE DEFAULT-PLUS-2))
     (22 14 (:REWRITE DEFAULT-LESS-THAN-2))
     (19 19 (:REWRITE DEFAULT-CAR))
     (19 13
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (18 11
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (18 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (17 17 (:REWRITE DEFAULT-CDR))
     (17 11 (:REWRITE SIMPLIFY-SUMS-<))
     (14 14 (:REWRITE THE-FLOOR-BELOW))
     (14 14 (:REWRITE THE-FLOOR-ABOVE))
     (14 14
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (14 14
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (14 14
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 14 (:REWRITE NORMALIZE-ADDENDS))
     (14 14 (:REWRITE DEFAULT-PLUS-1))
     (14 14 (:REWRITE DEFAULT-LESS-THAN-1))
     (13 13 (:REWRITE INTEGERP-<-CONSTANT))
     (13 13 (:REWRITE CONSTANT-<-INTEGERP))
     (13 13
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (13 13
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (13 13
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (13 13
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (13 13 (:REWRITE |(< c (- x))|))
     (13 13
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (13 13
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (13 13
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (13 13
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (13 13 (:REWRITE |(< (/ x) (/ y))|))
     (13 13 (:REWRITE |(< (- x) c)|))
     (13 13 (:REWRITE |(< (- x) (- y))|))
     (7 7 (:REWRITE ZP-OPEN))
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:META META-INTEGERP-CORRECT))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|)))
(DFN-LOADDM
     (209764 92760
             (:TYPE-PRESCRIPTION DMP-YIELDS-UNSIGNED-BYTE-P-32))
     (39680 768 (:REWRITE ZP-OPEN))
     (26495 3215
            (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
     (25416 25416
            (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (24064 256 (:LINEAR LOGAND-UPPER-BOUND . 2))
     (19617 19617 (:REWRITE DEFAULT-CDR))
     (11776 1792
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (11776 1792
            (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (6762 3770 (:REWRITE DEFAULT-PLUS-2))
     (6144 768 (:REWRITE DEFAULT-LOGAND-2))
     (5888 1792 (:REWRITE DEFAULT-LESS-THAN-1))
     (5149 5149 (:REWRITE DEFAULT-CAR))
     (4216 408 (:DEFINITION RP))
     (3770 3770
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3770 3770 (:REWRITE NORMALIZE-ADDENDS))
     (3770 3770 (:REWRITE DEFAULT-PLUS-1))
     (3264 272
           (:REWRITE RP-YIELDS-UNSIGNED-BYTE-P-32))
     (3128 408 (:DEFINITION DMP))
     (3110 853
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2944 1792 (:REWRITE DEFAULT-LESS-THAN-2))
     (1920 1920 (:REWRITE THE-FLOOR-BELOW))
     (1920 1920 (:REWRITE THE-FLOOR-ABOVE))
     (1792 1792 (:REWRITE SIMPLIFY-SUMS-<))
     (1792 1792
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1792 1792
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1792 1792
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1792 1792
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1792 1792
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1792 1792 (:REWRITE INTEGERP-<-CONSTANT))
     (1792 1792 (:REWRITE CONSTANT-<-INTEGERP))
     (1792 1792
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1792 1792
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1792 1792
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1792 1792
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1792 1792 (:REWRITE |(< c (- x))|))
     (1792 1792
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1792 1792
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1792 1792
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1792 1792
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1792 1792 (:REWRITE |(< (/ x) (/ y))|))
     (1792 1792 (:REWRITE |(< (- x) c)|))
     (1792 1792 (:REWRITE |(< (- x) (- y))|))
     (1768 136 (:DEFINITION IMP))
     (1760 352 (:REWRITE ACL2-NUMBERP-X))
     (1702 853
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (853 853 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (853 853
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (853 853
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (853 853
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (853 853 (:REWRITE |(equal c (/ x))|))
     (853 853 (:REWRITE |(equal c (- x))|))
     (853 853 (:REWRITE |(equal (/ x) c)|))
     (853 853 (:REWRITE |(equal (/ x) (/ y))|))
     (853 853 (:REWRITE |(equal (- x) c)|))
     (853 853 (:REWRITE |(equal (- x) (- y))|))
     (768 768
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (768 768
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (768 768 (:REWRITE DEFAULT-LOGAND-1))
     (768 768 (:REWRITE |(< 0 (/ x))|))
     (768 768 (:REWRITE |(< 0 (* x y))|))
     (704 176 (:REWRITE RATIONALP-X))
     (522 522 (:REWRITE |(+ x (if a b c))|))
     (512 512
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (512 512
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (512 512 (:REWRITE |(< (/ x) 0)|))
     (512 512 (:REWRITE |(< (* x y) 0)|))
     (272 136 (:DEFINITION TRUE-LISTP))
     (176 176 (:REWRITE REDUCE-RATIONALP-+))
     (176 176 (:REWRITE REDUCE-RATIONALP-*))
     (176 176 (:REWRITE REDUCE-INTEGERP-+))
     (176 176 (:REWRITE RATIONALP-MINUS-X))
     (176 176 (:REWRITE INTEGERP-MINUS-X))
     (176 176 (:META META-RATIONALP-CORRECT))
     (176 176 (:META META-INTEGERP-CORRECT))
     (132 132 (:REWRITE |(equal x (if a b c))|))
     (132 132 (:REWRITE |(equal (if a b c) x)|)))
(DFN-IN (102792 51396
                (:TYPE-PRESCRIPTION RP-YIELDS-UNSIGNED-BYTE-P-32))
        (102792 51396
                (:TYPE-PRESCRIPTION DMP-YIELDS-UNSIGNED-BYTE-P-32))
        (18467 18467 (:REWRITE DEFAULT-CDR))
        (5738 2874 (:REWRITE DEFAULT-PLUS-2))
        (5368 536 (:DEFINITION RP))
        (4800 400
              (:REWRITE RP-YIELDS-UNSIGNED-BYTE-P-32))
        (4800 400
              (:REWRITE DMP-YIELDS-UNSIGNED-BYTE-P-32))
        (4511 4511 (:REWRITE DEFAULT-CAR))
        (4280 536 (:DEFINITION DMP))
        (3130 855
              (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
        (2874 2874
              (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
        (2874 2874 (:REWRITE NORMALIZE-ADDENDS))
        (2874 2874 (:REWRITE DEFAULT-PLUS-1))
        (1780 356 (:REWRITE ACL2-NUMBERP-X))
        (1768 136 (:DEFINITION IMP))
        (1706 855
              (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
        (855 855 (:REWRITE SIMPLIFY-SUMS-EQUAL))
        (855 855
             (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
        (855 855
             (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
        (855 855
             (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
        (855 855 (:REWRITE |(equal c (/ x))|))
        (855 855 (:REWRITE |(equal c (- x))|))
        (855 855 (:REWRITE |(equal (/ x) c)|))
        (855 855 (:REWRITE |(equal (/ x) (/ y))|))
        (855 855 (:REWRITE |(equal (- x) c)|))
        (855 855 (:REWRITE |(equal (- x) (- y))|))
        (712 178 (:REWRITE RATIONALP-X))
        (522 522 (:REWRITE |(+ x (if a b c))|))
        (272 136 (:DEFINITION TRUE-LISTP))
        (256 256 (:REWRITE THE-FLOOR-BELOW))
        (256 256 (:REWRITE THE-FLOOR-ABOVE))
        (256 256 (:REWRITE SIMPLIFY-SUMS-<))
        (256 256
             (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
        (256 256 (:REWRITE REMOVE-WEAK-INEQUALITIES))
        (256 256
             (:REWRITE REMOVE-STRICT-INEQUALITIES))
        (256 256
             (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
        (256 256
             (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
        (256 256
             (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
        (256 256
             (:REWRITE PREFER-POSITIVE-ADDENDS-<))
        (256 256 (:REWRITE INTEGERP-<-CONSTANT))
        (256 256 (:REWRITE DEFAULT-LESS-THAN-2))
        (256 256 (:REWRITE DEFAULT-LESS-THAN-1))
        (256 256 (:REWRITE CONSTANT-<-INTEGERP))
        (256 256
             (:REWRITE |(< c (/ x)) positive c --- present in goal|))
        (256 256
             (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
        (256 256
             (:REWRITE |(< c (/ x)) negative c --- present in goal|))
        (256 256
             (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
        (256 256 (:REWRITE |(< c (- x))|))
        (256 256
             (:REWRITE |(< (/ x) c) positive c --- present in goal|))
        (256 256
             (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
        (256 256
             (:REWRITE |(< (/ x) c) negative c --- present in goal|))
        (256 256
             (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
        (256 256 (:REWRITE |(< (/ x) (/ y))|))
        (256 256 (:REWRITE |(< (- x) c)|))
        (256 256 (:REWRITE |(< (- x) (- y))|))
        (178 178 (:REWRITE REDUCE-RATIONALP-+))
        (178 178 (:REWRITE REDUCE-RATIONALP-*))
        (178 178 (:REWRITE REDUCE-INTEGERP-+))
        (178 178 (:REWRITE RATIONALP-MINUS-X))
        (178 178 (:REWRITE INTEGERP-MINUS-X))
        (178 178 (:META META-RATIONALP-CORRECT))
        (178 178 (:META META-INTEGERP-CORRECT))
        (132 132 (:REWRITE |(equal x (if a b c))|))
        (132 132 (:REWRITE |(equal (if a b c) x)|))
        (128 128
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
        (128 128
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
        (128 128 (:REWRITE |(< (/ x) 0)|))
        (128 128 (:REWRITE |(< (* x y) 0)|)))
(DFN-JUMP
     (683884 327528
             (:TYPE-PRESCRIPTION DMP-YIELDS-UNSIGNED-BYTE-P-32))
     (146622 204 (:REWRITE ASH-0))
     (141360 204 (:REWRITE ZIP-OPEN))
     (42193 32785 (:REWRITE DEFAULT-CDR))
     (35364 312 (:LINEAR LOGAND-UPPER-BOUND . 2))
     (34816 1088 (:REWRITE ZP-OPEN))
     (34224 312 (:LINEAR LOGAND-BOUNDS-POS . 2))
     (29920 768 (:DEFINITION UPDATE-NTH))
     (26603 4869
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (25312 2368
            (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (20052 8933 (:REWRITE DEFAULT-PLUS-2))
     (18451 13267 (:REWRITE DEFAULT-CAR))
     (17008 2488
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (16838 3214 (:REWRITE ACL2-NUMBERP-X))
     (15097 1461 (:DEFINITION RP))
     (14472 312 (:LINEAR LOGAND-UPPER-BOUND . 1))
     (13231 4869
            (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (12968 1038
            (:REWRITE DMP-YIELDS-UNSIGNED-BYTE-P-32))
     (12289 1525 (:DEFINITION DMP))
     (11784 312 (:LINEAR LOGAND-BOUNDS-POS . 1))
     (11221 8933 (:REWRITE DEFAULT-PLUS-1))
     (10114 1109
            (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
     (9808 2368
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8086 7827
           (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (7276 2488 (:REWRITE DEFAULT-LESS-THAN-1))
     (6995 2101 (:REWRITE DEFAULT-LOGAND-2))
     (6812 1415 (:REWRITE RATIONALP-X))
     (6669 6669
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6331 487 (:DEFINITION IMP))
     (5613 4869 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4933 4933
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4869 4869
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4869 4869 (:REWRITE |(equal c (/ x))|))
     (4869 4869 (:REWRITE |(equal c (- x))|))
     (4869 4869 (:REWRITE |(equal (/ x) c)|))
     (4869 4869 (:REWRITE |(equal (/ x) (/ y))|))
     (4869 4869 (:REWRITE |(equal (- x) c)|))
     (4869 4869 (:REWRITE |(equal (- x) (- y))|))
     (4656 312 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (4656 312 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (4152 36 (:LINEAR LOGIOR-BOUNDS-POS . 2))
     (4152 36 (:LINEAR LOGIOR-BOUNDS-POS . 1))
     (3736 2296 (:REWRITE SIMPLIFY-SUMS-<))
     (3468 36 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
     (3004 2488 (:REWRITE DEFAULT-LESS-THAN-2))
     (2820 18 (:REWRITE LOGIOR-=-0))
     (2752 2368 (:REWRITE |(< (- x) c)|))
     (2752 2368 (:REWRITE |(< (- x) (- y))|))
     (2502 18 (:REWRITE LOGXOR-=-0))
     (2500 2500 (:REWRITE THE-FLOOR-BELOW))
     (2500 2500 (:REWRITE THE-FLOOR-ABOVE))
     (2488 2488
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2488 2488
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2368 2368
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2368 2368 (:REWRITE INTEGERP-<-CONSTANT))
     (2368 2368 (:REWRITE CONSTANT-<-INTEGERP))
     (2368 2368
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (2368 2368
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (2368 2368
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (2368 2368
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (2368 2368 (:REWRITE |(< c (- x))|))
     (2368 2368
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (2368 2368
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (2368 2368
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (2368 2368
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (2368 2368 (:REWRITE |(< (/ x) (/ y))|))
     (2296 2296
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2205 2101 (:REWRITE DEFAULT-LOGAND-1))
     (1908 36 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
     (1792 256
           (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
     (1463 1463 (:REWRITE REDUCE-INTEGERP-+))
     (1463 1463 (:REWRITE INTEGERP-MINUS-X))
     (1463 1463 (:META META-INTEGERP-CORRECT))
     (1415 1415 (:REWRITE REDUCE-RATIONALP-+))
     (1415 1415 (:REWRITE REDUCE-RATIONALP-*))
     (1415 1415 (:REWRITE RATIONALP-MINUS-X))
     (1415 1415 (:META META-RATIONALP-CORRECT))
     (1124 1124
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1124 1124
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1124 1124 (:REWRITE |(< 0 (/ x))|))
     (1124 1124 (:REWRITE |(< 0 (* x y))|))
     (1076 1076 (:REWRITE |(< (* x y) 0)|))
     (974 487 (:DEFINITION TRUE-LISTP))
     (956 956 (:REWRITE |(< (/ x) 0)|))
     (884 884
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (884 884
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (633 129
          (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
     (633 129
          (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
     (633 129
          (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
     (624 24 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (504 88 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (384 384 (:REWRITE |(equal (+ (- c) x) y)|))
     (264 264 (:REWRITE |(< (+ c/d x) y)|))
     (256 256 (:TYPE-PRESCRIPTION UPDATE-NTH))
     (246 35 (:REWRITE DEFAULT-LOGXOR-2))
     (246 35 (:REWRITE DEFAULT-LOGIOR-2))
     (204 204 (:TYPE-PRESCRIPTION ZIP))
     (204 204
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (204 204 (:REWRITE ASH-GOES-TO-0))
     (176 32 (:REWRITE DEFAULT-MINUS))
     (152 35 (:REWRITE DEFAULT-LOGXOR-1))
     (152 35 (:REWRITE DEFAULT-LOGIOR-1))
     (144 144 (:REWRITE |(< (+ (- c) x) y)|))
     (144 48 (:LINEAR ARB32-UPPER-BOUND))
     (102 102 (:REWRITE |(+ x (if a b c))|))
     (35 35 (:REWRITE |(equal x (if a b c))|))
     (35 35 (:REWRITE |(equal (if a b c) x)|))
     (24 8 (:REWRITE DEFAULT-TIMES-2))
     (12 12 (:REWRITE |(< (logand x y) 0)|))
     (8 8
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (8 8 (:REWRITE DEFAULT-TIMES-1)))
(DFN-LOADCONSTANT
     (3761 1903
           (:TYPE-PRESCRIPTION RP-YIELDS-UNSIGNED-BYTE-P-32))
     (3761 1903
           (:TYPE-PRESCRIPTION DMP-YIELDS-UNSIGNED-BYTE-P-32))
     (155 15 (:DEFINITION RP))
     (140 116 (:REWRITE DEFAULT-CDR))
     (120 10
          (:REWRITE RP-YIELDS-UNSIGNED-BYTE-P-32))
     (120 10
          (:REWRITE DMP-YIELDS-UNSIGNED-BYTE-P-32))
     (115 15 (:DEFINITION DMP))
     (79 2 (:DEFINITION UPDATE-NTH))
     (65 5 (:DEFINITION IMP))
     (63 51 (:REWRITE DEFAULT-CAR))
     (55 30 (:REWRITE DEFAULT-PLUS-2))
     (44 22
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (44 22
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (32 1 (:REWRITE ZP-OPEN))
     (30 30 (:REWRITE DEFAULT-PLUS-1))
     (28 28
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (28 28 (:REWRITE NORMALIZE-ADDENDS))
     (22 22 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (22 22
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (22 22
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (22 22
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (22 22 (:REWRITE |(equal c (/ x))|))
     (22 22 (:REWRITE |(equal c (- x))|))
     (22 22 (:REWRITE |(equal (/ x) c)|))
     (22 22 (:REWRITE |(equal (/ x) (/ y))|))
     (22 22 (:REWRITE |(equal (- x) c)|))
     (22 22 (:REWRITE |(equal (- x) (- y))|))
     (10 5 (:DEFINITION TRUE-LISTP))
     (3 3
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
     (3 3
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3 3
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3 (:REWRITE INTEGERP-<-CONSTANT))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-2))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-1))
     (3 3 (:REWRITE CONSTANT-<-INTEGERP))
     (3 3
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (3 3
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (3 3
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (3 3
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (3 3 (:REWRITE |(< c (- x))|))
     (3 3
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (3 3
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (3 3
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (3 3
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (3 3 (:REWRITE |(< (/ x) (/ y))|))
     (3 3 (:REWRITE |(< (- x) c)|))
     (3 3 (:REWRITE |(< (- x) (- y))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE DEFAULT-LOGAND-2))
     (1 1 (:REWRITE DEFAULT-LOGAND-1))
     (1 1 (:REWRITE |(equal x (if a b c))|))
     (1 1 (:REWRITE |(equal (if a b c) x)|))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(DFN-RESERVEDINSTR)
(TYPE-INSTRUCTION)
(ARB-INSTRUCTION)
(ARB-INSTRUCTION-IS-INSTRUCTION (40 40 (:REWRITE DEFAULT-CDR))
                                (8 8 (:REWRITE DEFAULT-CAR))
                                (3 3 (:REWRITE UNSIGNED-BYTE-P-MONOTONE)))
(TYPE-INSTRUCTION-LIST)
(RUN (1835332 917666
              (:TYPE-PRESCRIPTION RP-YIELDS-UNSIGNED-BYTE-P-32))
     (1835332 917666
              (:TYPE-PRESCRIPTION DMP-YIELDS-UNSIGNED-BYTE-P-32))
     (92054 92054 (:REWRITE DEFAULT-CDR))
     (42031 6928
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (35260 7052 (:REWRITE ACL2-NUMBERP-X))
     (33214 33214 (:REWRITE DEFAULT-CAR))
     (25854 2502 (:DEFINITION RP))
     (20016 1668
            (:REWRITE RP-YIELDS-UNSIGNED-BYTE-P-32))
     (20016 1668
            (:REWRITE DMP-YIELDS-UNSIGNED-BYTE-P-32))
     (19182 2502 (:DEFINITION DMP))
     (14676 7338 (:REWRITE DEFAULT-PLUS-2))
     (14104 3526 (:REWRITE RATIONALP-X))
     (13823 6928
            (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (10842 834 (:DEFINITION IMP))
     (7338 7338
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (7338 7338 (:REWRITE NORMALIZE-ADDENDS))
     (7338 7338 (:REWRITE DEFAULT-PLUS-1))
     (6928 6928 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6928 6928
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (6928 6928
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6928 6928
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6928 6928 (:REWRITE |(equal c (/ x))|))
     (6928 6928 (:REWRITE |(equal c (- x))|))
     (6928 6928 (:REWRITE |(equal (/ x) c)|))
     (6928 6928 (:REWRITE |(equal (/ x) (/ y))|))
     (6928 6928 (:REWRITE |(equal (- x) c)|))
     (6928 6928 (:REWRITE |(equal (- x) (- y))|))
     (3526 3526 (:REWRITE REDUCE-RATIONALP-+))
     (3526 3526 (:REWRITE REDUCE-RATIONALP-*))
     (3526 3526 (:REWRITE REDUCE-INTEGERP-+))
     (3526 3526 (:REWRITE RATIONALP-MINUS-X))
     (3526 3526 (:REWRITE INTEGERP-MINUS-X))
     (3526 3526 (:META META-RATIONALP-CORRECT))
     (3526 3526 (:META META-INTEGERP-CORRECT))
     (1668 834 (:DEFINITION TRUE-LISTP)))
(BITS-DIFF-2-FORWARD
     (967 17 (:LINEAR LOGAND-BOUNDS-POS . 2))
     (934 17 (:LINEAR LOGAND-UPPER-BOUND . 2))
     (626 17 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (626 17 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (274 144 (:REWRITE DEFAULT-LESS-THAN-1))
     (214 142 (:REWRITE DEFAULT-PLUS-2))
     (209 111
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (209 111
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (153 142 (:REWRITE DEFAULT-PLUS-1))
     (144 144 (:REWRITE THE-FLOOR-BELOW))
     (144 144 (:REWRITE THE-FLOOR-ABOVE))
     (144 144
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (144 144
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (144 144 (:REWRITE DEFAULT-LESS-THAN-2))
     (122 122
          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (111 111
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (111 111 (:REWRITE INTEGERP-<-CONSTANT))
     (111 111 (:REWRITE CONSTANT-<-INTEGERP))
     (111 111
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (111 111
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (111 111
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (111 111
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (111 111 (:REWRITE |(< c (- x))|))
     (111 111
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (111 111
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (111 111
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (111 111
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (111 111 (:REWRITE |(< (/ x) (/ y))|))
     (111 111 (:REWRITE |(< (- x) c)|))
     (111 111 (:REWRITE |(< (- x) (- y))|))
     (102 102 (:REWRITE |(< (* x y) 0)|))
     (94 94
         (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
     (79 79 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (72 24 (:REWRITE ASH-0))
     (69 69
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (69 69
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (69 69 (:REWRITE |(< (/ x) 0)|))
     (38 38
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (36 18 (:REWRITE DEFAULT-LOGAND-2))
     (34 34 (:REWRITE |(< (+ c/d x) y)|))
     (33 33 (:REWRITE DEFAULT-MINUS))
     (32 32 (:TYPE-PRESCRIPTION ZIP))
     (27 18
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (26 18 (:REWRITE DEFAULT-LOGAND-1))
     (24 24 (:REWRITE ASH-GOES-TO-0))
     (18 18
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (18 18
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (18 18
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (18 18 (:REWRITE |(equal c (/ x))|))
     (18 18 (:REWRITE |(equal c (- x))|))
     (18 18 (:REWRITE |(equal (/ x) c)|))
     (18 18 (:REWRITE |(equal (/ x) (/ y))|))
     (18 18 (:REWRITE |(equal (- x) c)|))
     (18 18 (:REWRITE |(equal (- x) (- y))|))
     (17 17 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (16 16 (:REWRITE ZIP-OPEN))
     (11 11 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (8 8 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(DECODE (9 8
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
        (9 8
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
        (8 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
        (8 8
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
        (8 8
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
        (8 8
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
        (8 8 (:REWRITE |(equal c (/ x))|))
        (8 8 (:REWRITE |(equal c (- x))|))
        (8 8 (:REWRITE |(equal (/ x) c)|))
        (8 8 (:REWRITE |(equal (/ x) (/ y))|))
        (8 8 (:REWRITE |(equal (- x) c)|))
        (8 8 (:REWRITE |(equal (- x) (- y))|))
        (1 1 (:REWRITE UNSIGNED-BYTE-P-MONOTONE))
        (1 1
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(TYPE-INSTRUCTION-IN
     (5120 5120 (:REWRITE DEFAULT-CDR))
     (1680 336 (:REWRITE ACL2-NUMBERP-X))
     (1680 168
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1024 1024 (:REWRITE DEFAULT-CAR))
     (672 168 (:REWRITE RATIONALP-X))
     (336 168
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (168 168 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (168 168 (:REWRITE REDUCE-RATIONALP-+))
     (168 168 (:REWRITE REDUCE-RATIONALP-*))
     (168 168
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (168 168 (:REWRITE REDUCE-INTEGERP-+))
     (168 168
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (168 168 (:REWRITE RATIONALP-MINUS-X))
     (168 168 (:REWRITE INTEGERP-MINUS-X))
     (168 168
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (168 168 (:REWRITE |(equal c (/ x))|))
     (168 168 (:REWRITE |(equal c (- x))|))
     (168 168 (:REWRITE |(equal (/ x) c)|))
     (168 168 (:REWRITE |(equal (/ x) (/ y))|))
     (168 168 (:REWRITE |(equal (- x) c)|))
     (168 168 (:REWRITE |(equal (- x) (- y))|))
     (168 168 (:META META-RATIONALP-CORRECT))
     (168 168 (:META META-INTEGERP-CORRECT)))
(TYPE-INSTRUCTION-JUMP
     (928 928 (:REWRITE DEFAULT-CDR))
     (400 80 (:REWRITE ACL2-NUMBERP-X))
     (400 40
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (256 256 (:REWRITE DEFAULT-CAR))
     (160 40 (:REWRITE RATIONALP-X))
     (80 40
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (40 40 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (40 40 (:REWRITE REDUCE-RATIONALP-+))
     (40 40 (:REWRITE REDUCE-RATIONALP-*))
     (40 40
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (40 40 (:REWRITE REDUCE-INTEGERP-+))
     (40 40
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (40 40 (:REWRITE RATIONALP-MINUS-X))
     (40 40 (:REWRITE INTEGERP-MINUS-X))
     (40 40
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (40 40 (:REWRITE |(equal c (/ x))|))
     (40 40 (:REWRITE |(equal c (- x))|))
     (40 40 (:REWRITE |(equal (/ x) c)|))
     (40 40 (:REWRITE |(equal (/ x) (/ y))|))
     (40 40 (:REWRITE |(equal (- x) c)|))
     (40 40 (:REWRITE |(equal (- x) (- y))|))
     (40 40 (:META META-RATIONALP-CORRECT))
     (40 40 (:META META-INTEGERP-CORRECT)))
(TYPE-INSTRUCTION-LOADCONSTANT (8 8 (:REWRITE DEFAULT-CDR))
                               (6 6 (:REWRITE DEFAULT-CAR)))
(TYPE-INSTRUCTION-LOADDM
     (5120 5120 (:REWRITE DEFAULT-CDR))
     (1680 336 (:REWRITE ACL2-NUMBERP-X))
     (1680 168
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1408 1408 (:REWRITE DEFAULT-CAR))
     (672 168 (:REWRITE RATIONALP-X))
     (336 168
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (168 168 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (168 168 (:REWRITE REDUCE-RATIONALP-+))
     (168 168 (:REWRITE REDUCE-RATIONALP-*))
     (168 168
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (168 168 (:REWRITE REDUCE-INTEGERP-+))
     (168 168
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (168 168 (:REWRITE RATIONALP-MINUS-X))
     (168 168 (:REWRITE INTEGERP-MINUS-X))
     (168 168
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (168 168 (:REWRITE |(equal c (/ x))|))
     (168 168 (:REWRITE |(equal c (- x))|))
     (168 168 (:REWRITE |(equal (/ x) c)|))
     (168 168 (:REWRITE |(equal (/ x) (/ y))|))
     (168 168 (:REWRITE |(equal (- x) c)|))
     (168 168 (:REWRITE |(equal (- x) (- y))|))
     (168 168 (:META META-RATIONALP-CORRECT))
     (168 168 (:META META-INTEGERP-CORRECT)))
(TYPE-INSTRUCTION-NORMAL
     (5120 5120 (:REWRITE DEFAULT-CDR))
     (1680 336 (:REWRITE ACL2-NUMBERP-X))
     (1680 168
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1536 1536 (:REWRITE DEFAULT-CAR))
     (672 168 (:REWRITE RATIONALP-X))
     (336 168
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (168 168 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (168 168 (:REWRITE REDUCE-RATIONALP-+))
     (168 168 (:REWRITE REDUCE-RATIONALP-*))
     (168 168
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (168 168 (:REWRITE REDUCE-INTEGERP-+))
     (168 168
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (168 168 (:REWRITE RATIONALP-MINUS-X))
     (168 168 (:REWRITE INTEGERP-MINUS-X))
     (168 168
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (168 168 (:REWRITE |(equal c (/ x))|))
     (168 168 (:REWRITE |(equal c (- x))|))
     (168 168 (:REWRITE |(equal (/ x) c)|))
     (168 168 (:REWRITE |(equal (/ x) (/ y))|))
     (168 168 (:REWRITE |(equal (- x) c)|))
     (168 168 (:REWRITE |(equal (- x) (- y))|))
     (168 168 (:META META-RATIONALP-CORRECT))
     (168 168 (:META META-INTEGERP-CORRECT)))
(TYPE-INSTRUCTION-OUT
     (5120 5120 (:REWRITE DEFAULT-CDR))
     (1680 336 (:REWRITE ACL2-NUMBERP-X))
     (1680 168
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1664 1664 (:REWRITE DEFAULT-CAR))
     (672 168 (:REWRITE RATIONALP-X))
     (336 168
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (168 168 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (168 168 (:REWRITE REDUCE-RATIONALP-+))
     (168 168 (:REWRITE REDUCE-RATIONALP-*))
     (168 168
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (168 168 (:REWRITE REDUCE-INTEGERP-+))
     (168 168
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (168 168 (:REWRITE RATIONALP-MINUS-X))
     (168 168 (:REWRITE INTEGERP-MINUS-X))
     (168 168
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (168 168 (:REWRITE |(equal c (/ x))|))
     (168 168 (:REWRITE |(equal c (- x))|))
     (168 168 (:REWRITE |(equal (/ x) c)|))
     (168 168 (:REWRITE |(equal (/ x) (/ y))|))
     (168 168 (:REWRITE |(equal (- x) c)|))
     (168 168 (:REWRITE |(equal (- x) (- y))|))
     (168 168 (:META META-RATIONALP-CORRECT))
     (168 168 (:META META-INTEGERP-CORRECT)))
(TYPE-INSTRUCTION-STOREDM
     (5120 5120 (:REWRITE DEFAULT-CDR))
     (1792 1792 (:REWRITE DEFAULT-CAR))
     (1680 336 (:REWRITE ACL2-NUMBERP-X))
     (1680 168
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (672 168 (:REWRITE RATIONALP-X))
     (336 168
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (168 168 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (168 168 (:REWRITE REDUCE-RATIONALP-+))
     (168 168 (:REWRITE REDUCE-RATIONALP-*))
     (168 168
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (168 168 (:REWRITE REDUCE-INTEGERP-+))
     (168 168
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (168 168 (:REWRITE RATIONALP-MINUS-X))
     (168 168 (:REWRITE INTEGERP-MINUS-X))
     (168 168
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (168 168 (:REWRITE |(equal c (/ x))|))
     (168 168 (:REWRITE |(equal c (- x))|))
     (168 168 (:REWRITE |(equal (/ x) c)|))
     (168 168 (:REWRITE |(equal (/ x) (/ y))|))
     (168 168 (:REWRITE |(equal (- x) c)|))
     (168 168 (:REWRITE |(equal (- x) (- y))|))
     (168 168 (:META META-RATIONALP-CORRECT))
     (168 168 (:META META-INTEGERP-CORRECT)))
(TYPE-INSTRUCTION-STOREIM
     (5120 5120 (:REWRITE DEFAULT-CDR))
     (1920 1920 (:REWRITE DEFAULT-CAR))
     (1680 336 (:REWRITE ACL2-NUMBERP-X))
     (1680 168
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (672 168 (:REWRITE RATIONALP-X))
     (336 168
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (168 168 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (168 168 (:REWRITE REDUCE-RATIONALP-+))
     (168 168 (:REWRITE REDUCE-RATIONALP-*))
     (168 168
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (168 168 (:REWRITE REDUCE-INTEGERP-+))
     (168 168
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (168 168 (:REWRITE RATIONALP-MINUS-X))
     (168 168 (:REWRITE INTEGERP-MINUS-X))
     (168 168
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (168 168 (:REWRITE |(equal c (/ x))|))
     (168 168 (:REWRITE |(equal c (- x))|))
     (168 168 (:REWRITE |(equal (/ x) c)|))
     (168 168 (:REWRITE |(equal (/ x) (/ y))|))
     (168 168 (:REWRITE |(equal (- x) c)|))
     (168 168 (:REWRITE |(equal (- x) (- y))|))
     (168 168 (:META META-RATIONALP-CORRECT))
     (168 168 (:META META-INTEGERP-CORRECT)))
(IMP-YIELDS-UNSIGNED-BYTE-P-32
     (198 99
          (:TYPE-PRESCRIPTION RP-YIELDS-UNSIGNED-BYTE-P-32))
     (124 124 (:TYPE-PRESCRIPTION RP))
     (60 5
         (:REWRITE RP-YIELDS-UNSIGNED-BYTE-P-32))
     (60 5
         (:REWRITE DMP-YIELDS-UNSIGNED-BYTE-P-32))
     (45 5 (:DEFINITION RP))
     (45 5 (:DEFINITION DMP))
     (24 24 (:REWRITE DEFAULT-CAR))
     (23 14 (:REWRITE DEFAULT-PLUS-2))
     (22 22 (:REWRITE DEFAULT-CDR))
     (22 14 (:REWRITE DEFAULT-LESS-THAN-2))
     (19 13
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (18 11
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (18 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (17 11 (:REWRITE SIMPLIFY-SUMS-<))
     (14 14 (:REWRITE THE-FLOOR-BELOW))
     (14 14 (:REWRITE THE-FLOOR-ABOVE))
     (14 14
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (14 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (14 14
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (14 14
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 14 (:REWRITE NORMALIZE-ADDENDS))
     (14 14 (:REWRITE DEFAULT-PLUS-1))
     (14 14 (:REWRITE DEFAULT-LESS-THAN-1))
     (13 13 (:REWRITE INTEGERP-<-CONSTANT))
     (13 13 (:REWRITE CONSTANT-<-INTEGERP))
     (13 13
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (13 13
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (13 13
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (13 13
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (13 13 (:REWRITE |(< c (- x))|))
     (13 13
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (13 13
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (13 13
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (13 13
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (13 13 (:REWRITE |(< (/ x) (/ y))|))
     (13 13 (:REWRITE |(< (- x) c)|))
     (13 13 (:REWRITE |(< (- x) (- y))|))
     (7 7 (:REWRITE ZP-OPEN))
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:META META-INTEGERP-CORRECT))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|)))
(BITS-DIFF-1-FORWARD
     (503 9 (:LINEAR LOGAND-BOUNDS-POS . 2))
     (486 9 (:LINEAR LOGAND-UPPER-BOUND . 2))
     (314 9 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (314 9 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (142 76 (:REWRITE DEFAULT-LESS-THAN-1))
     (118 82 (:REWRITE DEFAULT-PLUS-2))
     (109 59
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (109 59 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (89 82 (:REWRITE DEFAULT-PLUS-1))
     (76 76 (:REWRITE THE-FLOOR-BELOW))
     (76 76 (:REWRITE THE-FLOOR-ABOVE))
     (76 76
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (76 76
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (76 76 (:REWRITE DEFAULT-LESS-THAN-2))
     (62 62
         (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (59 59
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (59 59 (:REWRITE INTEGERP-<-CONSTANT))
     (59 59 (:REWRITE CONSTANT-<-INTEGERP))
     (59 59
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (59 59
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (59 59
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (59 59
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (59 59 (:REWRITE |(< c (- x))|))
     (59 59
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (59 59
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (59 59
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (59 59
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (59 59 (:REWRITE |(< (/ x) (/ y))|))
     (59 59 (:REWRITE |(< (- x) c)|))
     (59 59 (:REWRITE |(< (- x) (- y))|))
     (54 54 (:REWRITE |(< (* x y) 0)|))
     (46 46
         (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
     (43 43 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (37 37
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (37 37
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (37 37 (:REWRITE |(< (/ x) 0)|))
     (36 12 (:REWRITE ASH-0))
     (22 22
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (20 10 (:REWRITE DEFAULT-LOGAND-2))
     (19 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (18 18 (:REWRITE |(< (+ c/d x) y)|))
     (17 17 (:REWRITE DEFAULT-MINUS))
     (16 16 (:TYPE-PRESCRIPTION ZIP))
     (14 10 (:REWRITE DEFAULT-LOGAND-1))
     (12 12 (:REWRITE ASH-GOES-TO-0))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (10 10
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (10 10 (:REWRITE |(equal c (/ x))|))
     (10 10 (:REWRITE |(equal c (- x))|))
     (10 10 (:REWRITE |(equal (/ x) c)|))
     (10 10 (:REWRITE |(equal (/ x) (/ y))|))
     (10 10 (:REWRITE |(equal (- x) c)|))
     (10 10 (:REWRITE |(equal (- x) (- y))|))
     (9 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (8 8 (:REWRITE ZIP-OPEN))
     (7 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(NTH-BITS-DIFF-1-OPEN
     (130 65
          (:TYPE-PRESCRIPTION RP-YIELDS-UNSIGNED-BYTE-P-32))
     (130 65
          (:TYPE-PRESCRIPTION DMP-YIELDS-UNSIGNED-BYTE-P-32))
     (65 65 (:TYPE-PRESCRIPTION RP))
     (65 65 (:TYPE-PRESCRIPTION DMP))
     (36 32 (:REWRITE DEFAULT-PLUS-1))
     (32 32 (:REWRITE DEFAULT-PLUS-2))
     (13 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (12 12
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (12 12
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (12 12
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (12 12 (:REWRITE |(equal c (/ x))|))
     (12 12 (:REWRITE |(equal c (- x))|))
     (12 12 (:REWRITE |(equal (/ x) c)|))
     (12 12 (:REWRITE |(equal (/ x) (/ y))|))
     (12 12 (:REWRITE |(equal (- x) c)|))
     (12 12 (:REWRITE |(equal (- x) (- y))|))
     (8 8 (:REWRITE THE-FLOOR-BELOW))
     (8 8 (:REWRITE THE-FLOOR-ABOVE))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (8 8 (:REWRITE SIMPLIFY-SUMS-<))
     (8 8
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (8 8
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (8 8
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:REWRITE INTEGERP-<-CONSTANT))
     (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
     (8 8 (:REWRITE DEFAULT-LESS-THAN-1))
     (8 8 (:REWRITE CONSTANT-<-INTEGERP))
     (8 8 (:REWRITE |(equal (+ (- c) x) y)|))
     (8 8
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (8 8
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (8 8
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (8 8
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (8 8 (:REWRITE |(< c (- x))|))
     (8 8
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (8 8
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (8 8
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (8 8
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (/ x) (/ y))|))
     (8 8 (:REWRITE |(< (- x) c)|))
     (8 8 (:REWRITE |(< (- x) (- y))|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (8 8 (:META META-INTEGERP-CORRECT))
     (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (4 4 (:REWRITE DEFAULT-MINUS))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(NEXT (715496 426769
              (:TYPE-PRESCRIPTION RP-YIELDS-UNSIGNED-BYTE-P-32))
      (715496 426769
              (:TYPE-PRESCRIPTION DMP-YIELDS-UNSIGNED-BYTE-P-32))
      (177348 5475 (:REWRITE ZP-OPEN))
      (111120 7268
              (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
      (76076 4450 (:REWRITE ACL2-NUMBERP-X))
      (39496 7268
             (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
      (35813 2225 (:REWRITE RATIONALP-X))
      (26056 26056 (:REWRITE DEFAULT-CDR))
      (14952 1256 (:DEFINITION RP))
      (13048 1144 (:DEFINITION IMP))
      (9600 800
            (:REWRITE RP-YIELDS-UNSIGNED-BYTE-P-32))
      (9600 800
            (:REWRITE DMP-YIELDS-UNSIGNED-BYTE-P-32))
      (9349 9349 (:REWRITE DEFAULT-CAR))
      (8920 1144 (:DEFINITION DMP))
      (8453 6964 (:REWRITE DEFAULT-PLUS-2))
      (7268 7268 (:REWRITE SIMPLIFY-SUMS-EQUAL))
      (7268 7268
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
      (7268 7268
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
      (7268 7268
            (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
      (7268 7268 (:REWRITE |(equal c (/ x))|))
      (7268 7268 (:REWRITE |(equal c (- x))|))
      (7268 7268 (:REWRITE |(equal (/ x) c)|))
      (7268 7268 (:REWRITE |(equal (/ x) (/ y))|))
      (7268 7268 (:REWRITE |(equal (- x) c)|))
      (7268 7268 (:REWRITE |(equal (- x) (- y))|))
      (7177 6819 (:REWRITE DEFAULT-LESS-THAN-2))
      (6964 6964
            (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
      (6964 6964 (:REWRITE NORMALIZE-ADDENDS))
      (6964 6964 (:REWRITE DEFAULT-PLUS-1))
      (6819 6819 (:REWRITE THE-FLOOR-BELOW))
      (6819 6819 (:REWRITE THE-FLOOR-ABOVE))
      (6819 6819
            (:REWRITE REMOVE-STRICT-INEQUALITIES))
      (6819 6819
            (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
      (6819 6819
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
      (6819 6819
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
      (6819 6819 (:REWRITE INTEGERP-<-CONSTANT))
      (6819 6819 (:REWRITE DEFAULT-LESS-THAN-1))
      (6819 6819 (:REWRITE CONSTANT-<-INTEGERP))
      (6819 6819
            (:REWRITE |(< c (/ x)) positive c --- present in goal|))
      (6819 6819
            (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
      (6819 6819
            (:REWRITE |(< c (/ x)) negative c --- present in goal|))
      (6819 6819
            (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
      (6819 6819 (:REWRITE |(< c (- x))|))
      (6819 6819
            (:REWRITE |(< (/ x) c) positive c --- present in goal|))
      (6819 6819
            (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
      (6819 6819
            (:REWRITE |(< (/ x) c) negative c --- present in goal|))
      (6819 6819
            (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
      (6819 6819 (:REWRITE |(< (/ x) (/ y))|))
      (6819 6819 (:REWRITE |(< (- x) c)|))
      (6819 6819 (:REWRITE |(< (- x) (- y))|))
      (6505 6147
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
      (6505 6147
            (:REWRITE PREFER-POSITIVE-ADDENDS-<))
      (6147 6147 (:REWRITE SIMPLIFY-SUMS-<))
      (5579 5579
            (:REWRITE UNSIGNED-BYTE-P-MONOTONE))
      (5475 5475
            (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
      (5475 5475
            (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
      (5475 5475 (:REWRITE |(< 0 (/ x))|))
      (5475 5475 (:REWRITE |(< 0 (* x y))|))
      (2225 2225 (:REWRITE REDUCE-RATIONALP-+))
      (2225 2225 (:REWRITE REDUCE-RATIONALP-*))
      (2225 2225 (:REWRITE REDUCE-INTEGERP-+))
      (2225 2225 (:REWRITE RATIONALP-MINUS-X))
      (2225 2225 (:REWRITE INTEGERP-MINUS-X))
      (2225 2225 (:META META-RATIONALP-CORRECT))
      (2225 2225 (:META META-INTEGERP-CORRECT))
      (688 344 (:DEFINITION TRUE-LISTP))
      (672 672 (:REWRITE |(< (/ x) 0)|))
      (672 672 (:REWRITE |(< (* x y) 0)|))
      (656 656
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
      (1 1 (:REWRITE |(equal x (if a b c))|)))
(ENC (28884 28884 (:REWRITE DEFAULT-CDR))
     (2107 2107 (:REWRITE DEFAULT-CAR))
     (2038 307
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1780 356 (:REWRITE ACL2-NUMBERP-X))
     (772 386 (:REWRITE DEFAULT-PLUS-2))
     (712 178 (:REWRITE RATIONALP-X))
     (614 307
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (386 386
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (386 386 (:REWRITE NORMALIZE-ADDENDS))
     (386 386 (:REWRITE DEFAULT-PLUS-1))
     (307 307 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (307 307
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (307 307
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (307 307
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (307 307 (:REWRITE |(equal c (/ x))|))
     (307 307 (:REWRITE |(equal c (- x))|))
     (307 307 (:REWRITE |(equal (/ x) c)|))
     (307 307 (:REWRITE |(equal (/ x) (/ y))|))
     (307 307 (:REWRITE |(equal (- x) c)|))
     (307 307 (:REWRITE |(equal (- x) (- y))|))
     (178 178 (:REWRITE REDUCE-RATIONALP-+))
     (178 178 (:REWRITE REDUCE-RATIONALP-*))
     (178 178 (:REWRITE REDUCE-INTEGERP-+))
     (178 178 (:REWRITE RATIONALP-MINUS-X))
     (178 178 (:REWRITE INTEGERP-MINUS-X))
     (178 178 (:META META-RATIONALP-CORRECT))
     (178 178 (:META META-INTEGERP-CORRECT))
     (128 128 (:REWRITE |(equal x (if a b c))|))
     (128 128 (:REWRITE |(equal (if a b c) x)|))
     (48 48 (:REWRITE UNSIGNED-BYTE-P-MONOTONE)))
(ENCODE (167638 167638 (:REWRITE DEFAULT-CDR))
        (33290 6658 (:REWRITE ACL2-NUMBERP-X))
        (33290 3329
               (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
        (21306 21306 (:REWRITE DEFAULT-CAR))
        (13316 3329 (:REWRITE RATIONALP-X))
        (6658 3329
              (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
        (3332 3332 (:REWRITE REDUCE-INTEGERP-+))
        (3332 3332 (:REWRITE INTEGERP-MINUS-X))
        (3332 3332 (:META META-INTEGERP-CORRECT))
        (3329 3329 (:REWRITE SIMPLIFY-SUMS-EQUAL))
        (3329 3329 (:REWRITE REDUCE-RATIONALP-+))
        (3329 3329 (:REWRITE REDUCE-RATIONALP-*))
        (3329 3329
              (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
        (3329 3329
              (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
        (3329 3329 (:REWRITE RATIONALP-MINUS-X))
        (3329 3329
              (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
        (3329 3329 (:REWRITE |(equal c (/ x))|))
        (3329 3329 (:REWRITE |(equal c (- x))|))
        (3329 3329 (:REWRITE |(equal (/ x) c)|))
        (3329 3329 (:REWRITE |(equal (/ x) (/ y))|))
        (3329 3329 (:REWRITE |(equal (- x) c)|))
        (3329 3329 (:REWRITE |(equal (- x) (- y))|))
        (3329 3329 (:META META-RATIONALP-CORRECT)))
(UNSIGNED-BYTE-P-32-ENC
     (11520 2304 (:REWRITE ACL2-NUMBERP-X))
     (11520 1152
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (8794 8794 (:REWRITE DEFAULT-CDR))
     (5462 5462 (:REWRITE DEFAULT-CAR))
     (4608 1152 (:REWRITE RATIONALP-X))
     (2304 1152
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1152 1152 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1152 1152 (:REWRITE REDUCE-RATIONALP-+))
     (1152 1152 (:REWRITE REDUCE-RATIONALP-*))
     (1152 1152
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1152 1152 (:REWRITE REDUCE-INTEGERP-+))
     (1152 1152
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1152 1152 (:REWRITE RATIONALP-MINUS-X))
     (1152 1152 (:REWRITE INTEGERP-MINUS-X))
     (1152 1152
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1152 1152 (:REWRITE |(equal c (/ x))|))
     (1152 1152 (:REWRITE |(equal c (- x))|))
     (1152 1152 (:REWRITE |(equal (/ x) c)|))
     (1152 1152 (:REWRITE |(equal (/ x) (/ y))|))
     (1152 1152 (:REWRITE |(equal (- x) c)|))
     (1152 1152 (:REWRITE |(equal (- x) (- y))|))
     (1152 1152 (:META META-RATIONALP-CORRECT))
     (1152 1152 (:META META-INTEGERP-CORRECT))
     (226 226 (:REWRITE UNSIGNED-BYTE-P-MONOTONE))
     (21 3 (:DEFINITION LEN))
     (12 6 (:REWRITE DEFAULT-PLUS-2))
     (9 9 (:TYPE-PRESCRIPTION LEN))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE NORMALIZE-ADDENDS))
     (6 6 (:REWRITE DEFAULT-PLUS-1))
     (6 3 (:REWRITE DEFAULT-MINUS)))
(UNSIGNED-BYTE-P-32-ENCODE
     (440 88 (:REWRITE ACL2-NUMBERP-X))
     (440 44
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (176 44 (:REWRITE RATIONALP-X))
     (138 138 (:REWRITE DEFAULT-CDR))
     (88 44
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (87 87 (:REWRITE DEFAULT-CAR))
     (44 44 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (44 44 (:REWRITE REDUCE-RATIONALP-+))
     (44 44 (:REWRITE REDUCE-RATIONALP-*))
     (44 44
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (44 44 (:REWRITE REDUCE-INTEGERP-+))
     (44 44
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (44 44 (:REWRITE RATIONALP-MINUS-X))
     (44 44 (:REWRITE INTEGERP-MINUS-X))
     (44 44
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (44 44 (:REWRITE |(equal c (/ x))|))
     (44 44 (:REWRITE |(equal c (- x))|))
     (44 44 (:REWRITE |(equal (/ x) c)|))
     (44 44 (:REWRITE |(equal (/ x) (/ y))|))
     (44 44 (:REWRITE |(equal (- x) c)|))
     (44 44 (:REWRITE |(equal (- x) (- y))|))
     (44 44 (:META META-RATIONALP-CORRECT))
     (44 44 (:META META-INTEGERP-CORRECT))
     (29 29 (:REWRITE UNSIGNED-BYTE-P-MONOTONE)))
(LOADIM (4220 2110
              (:TYPE-PRESCRIPTION RP-YIELDS-UNSIGNED-BYTE-P-32))
        (4220 2110
              (:TYPE-PRESCRIPTION IMP-YIELDS-UNSIGNED-BYTE-P-32))
        (4220 2110
              (:TYPE-PRESCRIPTION DMP-YIELDS-UNSIGNED-BYTE-P-32))
        (175 15 (:DEFINITION RP))
        (175 15 (:DEFINITION IMP))
        (145 145 (:REWRITE DEFAULT-CDR))
        (120 10
             (:REWRITE RP-YIELDS-UNSIGNED-BYTE-P-32))
        (120 10
             (:REWRITE IMP-YIELDS-UNSIGNED-BYTE-P-32))
        (120 10
             (:REWRITE DMP-YIELDS-UNSIGNED-BYTE-P-32))
        (115 15 (:DEFINITION DMP))
        (82 44 (:REWRITE DEFAULT-PLUS-2))
        (63 63 (:REWRITE UNSIGNED-BYTE-P-MONOTONE))
        (53 44 (:REWRITE DEFAULT-PLUS-1))
        (44 22
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
        (44 22
            (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
        (34 34
            (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
        (22 22 (:REWRITE SIMPLIFY-SUMS-EQUAL))
        (22 22
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
        (22 22
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
        (22 22
            (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
        (22 22 (:REWRITE |(equal c (/ x))|))
        (22 22 (:REWRITE |(equal c (- x))|))
        (22 22 (:REWRITE |(equal (/ x) c)|))
        (22 22 (:REWRITE |(equal (/ x) (/ y))|))
        (22 22 (:REWRITE |(equal (- x) c)|))
        (22 22 (:REWRITE |(equal (- x) (- y))|))
        (10 5 (:DEFINITION TRUE-LISTP))
        (5 3
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
        (5 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
        (4 3 (:REWRITE DEFAULT-LESS-THAN-2))
        (4 3 (:REWRITE DEFAULT-LESS-THAN-1))
        (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
        (3 3 (:REWRITE THE-FLOOR-BELOW))
        (3 3 (:REWRITE THE-FLOOR-ABOVE))
        (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
        (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
        (3 3
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
        (3 3
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
        (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
        (3 3 (:REWRITE INTEGERP-<-CONSTANT))
        (3 3 (:REWRITE CONSTANT-<-INTEGERP))
        (3 3
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
        (3 3
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
        (3 3
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
        (3 3
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
        (3 3 (:REWRITE |(< c (- x))|))
        (3 3
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
        (3 3
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
        (3 3
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
        (3 3
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
        (3 3 (:REWRITE |(< (/ x) (/ y))|))
        (3 3 (:REWRITE |(< (- x) c)|))
        (3 3 (:REWRITE |(< (- x) (- y))|))
        (2 2 (:REWRITE DEFAULT-LOGAND-2))
        (2 2 (:REWRITE DEFAULT-LOGAND-1))
        (1 1
           (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
        (1 1
           (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
        (1 1
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
        (1 1
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
        (1 1 (:REWRITE |(equal x (if a b c))|))
        (1 1 (:REWRITE |(equal (if a b c) x)|))
        (1 1 (:REWRITE |(< y (+ (- c) x))|))
        (1 1 (:REWRITE |(< x (+ c/d y))|))
        (1 1 (:REWRITE |(< (/ x) 0)|))
        (1 1 (:REWRITE |(< (* x y) 0)|)))
(INITIALIZE (768 384
                 (:TYPE-PRESCRIPTION RP-YIELDS-UNSIGNED-BYTE-P-32))
            (768 384
                 (:TYPE-PRESCRIPTION IMP-YIELDS-UNSIGNED-BYTE-P-32))
            (768 384
                 (:TYPE-PRESCRIPTION DMP-YIELDS-UNSIGNED-BYTE-P-32))
            (35 3 (:DEFINITION RP))
            (35 3 (:DEFINITION IMP))
            (26 26 (:REWRITE DEFAULT-CDR))
            (24 2
                (:REWRITE RP-YIELDS-UNSIGNED-BYTE-P-32))
            (24 2
                (:REWRITE IMP-YIELDS-UNSIGNED-BYTE-P-32))
            (24 2
                (:REWRITE DMP-YIELDS-UNSIGNED-BYTE-P-32))
            (23 3 (:DEFINITION DMP))
            (13 13 (:REWRITE DEFAULT-CAR))
            (12 12 (:REWRITE UNSIGNED-BYTE-P-MONOTONE))
            (10 5 (:REWRITE DEFAULT-PLUS-2))
            (8 4
               (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
            (8 4
               (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
            (5 5
               (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
            (5 5 (:REWRITE NORMALIZE-ADDENDS))
            (5 5 (:REWRITE DEFAULT-PLUS-1))
            (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
            (4 4
               (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
            (4 4
               (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
            (4 4
               (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
            (4 4 (:REWRITE |(equal c (/ x))|))
            (4 4 (:REWRITE |(equal c (- x))|))
            (4 4 (:REWRITE |(equal (/ x) c)|))
            (4 4 (:REWRITE |(equal (/ x) (/ y))|))
            (4 4 (:REWRITE |(equal (- x) c)|))
            (4 4 (:REWRITE |(equal (- x) (- y))|))
            (2 1 (:DEFINITION TRUE-LISTP)))
