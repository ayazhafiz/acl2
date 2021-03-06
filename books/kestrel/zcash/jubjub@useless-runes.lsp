(ZCASH::PRIMEP-OF-JUBJUB-Q)
(ZCASH::FEP-OF-JUBJUB-A)
(ZCASH::FEP-OF-JUBJUB-D)
(ZCASH::JUBJUB-A-D-DIFFERENT)
(ZCASH::JUBJUB-A-NOT-ZERO)
(ZCASH::JUBJUB-D-NOT-ZERO)
(ZCASH::JUBJUB-Q-NOT-TWO)
(ZCASH::JUBJUB-POINTP)
(ZCASH::BOOLEANP-OF-JUBJUB-POINTP)
(ZCASH::POINT-FINITE-WHEN-JUBJUB-POINTP)
(ZCASH::MAYBE-JUBJUB-POINTP)
(ZCASH::BOOLEANP-OF-MAYBE-JUBJUB-POINTP)
(ZCASH::MAYBE-JUBJUB-POINTP-WHEN-JUBJUB-POINTP)
(ZCASH::JUBJUB-POINT->U
 (1
  1
  (:REWRITE
   ECURVE::POINT-ON-TWISTED-EDWARDS-P-OF-TWISTED-EDWARDS-FIX-CURVE-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
      ECURVE::POINT-ON-TWISTED-EDWARDS-P-OF-POINT-FIX-POINT-NORMALIZE-CONST))
 (1 1
    (:REWRITE ECURVE::POINT-KIND-OF-POINT-FIX-P-NORMALIZE-CONST)))
(ZCASH::NATP-OF-JUBJUB-POINT->U)
(ZCASH::JUBJUB-POINT->U-UPPER-BOUND
     (19 11 (:REWRITE DEFAULT-<-2))
     (16 11 (:REWRITE DEFAULT-<-1))
     (3 3
        (:REWRITE ECURVE::POINT-FINITE->X-OF-POINT-FIX-P-NORMALIZE-CONST))
     (2 2
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1
        (:REWRITE ECURVE::TWISTED-EDWARDS-OF-NFIX-P-NORMALIZE-CONST))
     (1 1
        (:REWRITE ECURVE::POINT-KIND-OF-POINT-FIX-P-NORMALIZE-CONST))
     (1 1
        (:REWRITE ECURVE::POINT-FINITE->Y-OF-POINT-FIX-P-NORMALIZE-CONST)))
(ZCASH::JUBJUB-POINT->V
 (1
  1
  (:REWRITE
   ECURVE::POINT-ON-TWISTED-EDWARDS-P-OF-TWISTED-EDWARDS-FIX-CURVE-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
      ECURVE::POINT-ON-TWISTED-EDWARDS-P-OF-POINT-FIX-POINT-NORMALIZE-CONST))
 (1 1
    (:REWRITE ECURVE::POINT-KIND-OF-POINT-FIX-P-NORMALIZE-CONST)))
(ZCASH::NATP-OF-JUBJUB-POINT->V)
(ZCASH::JUBJUB-POINT->V-UPPER-BOUND
     (19 11 (:REWRITE DEFAULT-<-2))
     (16 11 (:REWRITE DEFAULT-<-1))
     (3 3
        (:REWRITE ECURVE::POINT-FINITE->Y-OF-POINT-FIX-P-NORMALIZE-CONST))
     (2 2
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1
        (:REWRITE ECURVE::TWISTED-EDWARDS-OF-NFIX-P-NORMALIZE-CONST))
     (1 1
        (:REWRITE ECURVE::POINT-KIND-OF-POINT-FIX-P-NORMALIZE-CONST))
     (1 1
        (:REWRITE ECURVE::POINT-FINITE->X-OF-POINT-FIX-P-NORMALIZE-CONST)))
(ZCASH::JUBJUB-MUL)
(ZCASH::JUBJUB-POINTP-OF-JUBJUB-MUL
 (1
  1
  (:REWRITE
   ECURVE::TWISTED-EDWARDS-MUL-OF-TWISTED-EDWARDS-FIX-CURVE-NORMALIZE-CONST))
 (1
   1
   (:REWRITE ECURVE::TWISTED-EDWARDS-MUL-OF-POINT-FIX-POINT-NORMALIZE-CONST))
 (1 1
    (:REWRITE ECURVE::TWISTED-EDWARDS-MUL-OF-IFIX-SCALAR-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
   ECURVE::POINT-ON-TWISTED-EDWARDS-P-OF-TWISTED-EDWARDS-FIX-CURVE-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
     ECURVE::POINT-ON-TWISTED-EDWARDS-P-OF-POINT-FIX-POINT-NORMALIZE-CONST)))
(ZCASH::JUBJUB-ADD)
(ZCASH::JUBJUB-POINTP-OF-JUBJUB-ADD
 (2
  2
  (:REWRITE
   ECURVE::POINT-ON-TWISTED-EDWARDS-P-OF-TWISTED-EDWARDS-FIX-CURVE-NORMALIZE-CONST))
 (2
  2
  (:REWRITE
      ECURVE::POINT-ON-TWISTED-EDWARDS-P-OF-POINT-FIX-POINT-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
   ECURVE::TWISTED-EDWARDS-ADD-OF-TWISTED-EDWARDS-FIX-CURVE-NORMALIZE-CONST))
 (1
  1
  (:REWRITE ECURVE::TWISTED-EDWARDS-ADD-OF-POINT-FIX-POINT2-NORMALIZE-CONST))
 (1 1
    (:REWRITE
         ECURVE::TWISTED-EDWARDS-ADD-OF-POINT-FIX-POINT1-NORMALIZE-CONST)))
(ZCASH::STEP1 (50 50 (:REWRITE PFIELD::MUL-BECOMES-NEG))
              (49 49
                  (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
              (34 17
                  (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
              (34 17
                  (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
              (26 17
                  (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
              (24 8 (:DEFINITION NATP))
              (17 17
                  (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
              (17 17
                  (:REWRITE PFIELD::NEG-OF-MUL-WHEN-CONSTANT))
              (17 17 (:REWRITE PFIELD::ADD-OF-CONSTANTS))
              (17 17 (:REWRITE PFIELD::ADD-COMMUTATIVE))
              (13 13
                  (:REWRITE PFIELD::MUL-COMBINE-CONSTANTS))
              (12 10 (:REWRITE DEFAULT-<-2))
              (12 10 (:REWRITE DEFAULT-<-1))
              (10 10
                  (:REWRITE PFIELD::EQUAL-OF-MUL-CONSTANTS))
              (8 8 (:TYPE-PRESCRIPTION NATP))
              (5 5 (:REWRITE PFIELD::SUB-WHEN-CONSTANTS))
              (4 4
                 (:LINEAR ZCASH::JUBJUB-POINT->V-UPPER-BOUND))
              (4 4
                 (:LINEAR ZCASH::JUBJUB-POINT->U-UPPER-BOUND))
              (3 3
                 (:REWRITE PFIELD::EQUAL-OF-ADD-COMBINE-CONSTANTS)))
(ZCASH::STEP2
     (39 24 (:REWRITE DEFAULT-<-2))
     (34 34 (:REWRITE PFIELD::MUL-BECOMES-NEG))
     (33 24 (:REWRITE DEFAULT-<-1))
     (30 30
         (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
     (24 12
         (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
     (20 12
         (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
     (19 19 (:REWRITE PFIELD::ADD-OF-CONSTANTS))
     (18 18
         (:REWRITE PFIELD::MUL-COMBINE-CONSTANTS))
     (12 4 (:DEFINITION NATP))
     (11 11
         (:REWRITE PFIELD::EQUAL-OF-ADD-CANCEL-BIND-FREE))
     (10 5
         (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
     (5 5
        (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
     (5 5
        (:REWRITE PFIELD::NEG-OF-MUL-WHEN-CONSTANT))
     (4 4 (:TYPE-PRESCRIPTION NATP))
     (4 4
        (:REWRITE PFIELD::ADD-COMBINE-CONSTANTS))
     (2 2 (:REWRITE PFIELD::SUB-WHEN-CONSTANTS))
     (2 2
        (:REWRITE PFIELD::EQUAL-OF-ADD-COMBINE-CONSTANTS))
     (2 2
        (:LINEAR ZCASH::JUBJUB-POINT->V-UPPER-BOUND))
     (2 2
        (:LINEAR ZCASH::JUBJUB-POINT->U-UPPER-BOUND))
     (1 1
        (:REWRITE ECURVE::TWISTED-EDWARDS-OF-NFIX-P-NORMALIZE-CONST))
     (1 1
        (:REWRITE ECURVE::POINT-FINITE-OF-NFIX-Y-NORMALIZE-CONST))
     (1 1
        (:REWRITE ECURVE::POINT-FINITE-OF-NFIX-X-NORMALIZE-CONST)))
(ZCASH::RETURNS-LEMMA
     (147 147 (:REWRITE PFIELD::MUL-BECOMES-NEG))
     (125 125
          (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
     (66 66
         (:REWRITE PFIELD::MUL-COMBINE-CONSTANTS))
     (64 32
         (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
     (64 32
         (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
     (53 32
         (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
     (32 32
         (:TYPE-PRESCRIPTION PFIELD::NATP-OF-NEG))
     (32 32
         (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
     (32 32
         (:REWRITE PFIELD::NEG-OF-MUL-WHEN-CONSTANT))
     (32 32 (:REWRITE PFIELD::ADD-OF-CONSTANTS))
     (32 32 (:REWRITE PFIELD::ADD-COMMUTATIVE))
     (26 26
         (:REWRITE PFIELD::SUB-WHEN-CONSTANTS))
     (18 6 (:DEFINITION NATP))
     (16 11 (:REWRITE DEFAULT-<-2))
     (16 11 (:REWRITE DEFAULT-<-1))
     (7 7
        (:REWRITE PFIELD::EQUAL-OF-MUL-CONSTANTS))
     (6 6 (:TYPE-PRESCRIPTION NATP))
     (4 4
        (:REWRITE ECURVE::POINT-FINITE-OF-NFIX-Y-NORMALIZE-CONST))
     (4 4
        (:REWRITE ECURVE::POINT-FINITE-OF-NFIX-X-NORMALIZE-CONST))
     (3 3
        (:REWRITE PFIELD::EQUAL-OF-ADD-COMBINE-CONSTANTS))
     (1 1
        (:LINEAR ZCASH::JUBJUB-POINT->V-UPPER-BOUND))
     (1 1
        (:LINEAR ZCASH::JUBJUB-POINT->U-UPPER-BOUND)))
(ZCASH::JUBJUB-ABST (5 5 (:TYPE-PRESCRIPTION LAST)))
(ZCASH::MAYBE-JUBJUB-POINTP-OF-JUBJUB-ABST
     (3015 58 (:DEFINITION TAKE))
     (1456 208 (:DEFINITION LEN))
     (1427 116 (:REWRITE TAKE-OF-TOO-MANY))
     (1054 116 (:REWRITE TAKE-OF-LEN-FREE))
     (533 325 (:REWRITE DEFAULT-+-2))
     (424 424
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                    . 2))
     (424 424
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                    . 1))
     (424 280 (:REWRITE DEFAULT-CDR))
     (325 325 (:REWRITE DEFAULT-+-1))
     (316 237 (:REWRITE DEFAULT-<-2))
     (260 116 (:REWRITE TAKE-WHEN-ATOM))
     (250 237 (:REWRITE DEFAULT-<-1))
     (232 58 (:REWRITE ZP-OPEN))
     (216 72 (:DEFINITION NFIX))
     (216 65 (:REWRITE DEFAULT-CAR))
     (174 58 (:REWRITE FOLD-CONSTS-IN-+))
     (95 95 (:TYPE-PRESCRIPTION LAST))
     (85 85 (:REWRITE PFIELD::MUL-BECOMES-NEG))
     (76 40
         (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
     (72 72 (:TYPE-PRESCRIPTION NFIX))
     (68 68
         (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
     (64 32
         (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
     (63 7 (:DEFINITION LAST))
     (49 32
         (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
     (46 46
         (:TYPE-PRESCRIPTION PFIELD::NATP-OF-NEG))
     (46 10 (:REWRITE ECURVE::RETURNS-LEMMA))
     (38 38
         (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
     (32 32
         (:REWRITE PFIELD::NEG-OF-MUL-WHEN-CONSTANT))
     (32 32 (:REWRITE PFIELD::ADD-OF-CONSTANTS))
     (32 32 (:REWRITE PFIELD::ADD-COMMUTATIVE))
     (30 10 (:DEFINITION NATP))
     (19 19 (:REWRITE PFIELD::MUL-COMMUTATIVE-2))
     (19 19
         (:REWRITE PFIELD::MUL-COMBINE-CONSTANTS))
     (10 10 (:TYPE-PRESCRIPTION NATP))
     (9 9
        (:REWRITE PFIELD::EQUAL-OF-MUL-CONSTANTS))
     (8 8
        (:REWRITE ECURVE::POINT-FINITE-OF-NFIX-Y-NORMALIZE-CONST))
     (8 8
        (:REWRITE ECURVE::POINT-FINITE-OF-NFIX-X-NORMALIZE-CONST))
     (6 6
        (:LINEAR ZCASH::JUBJUB-POINT->V-UPPER-BOUND))
     (6 6
        (:LINEAR ZCASH::JUBJUB-POINT->U-UPPER-BOUND)))
(ZCASH::VERIFY-GUARDS-LEMMA)
(ZCASH::JUBJUB-ABST
     (46 1 (:DEFINITION TAKE))
     (38 38 (:REWRITE PFIELD::ADD-OF-CONSTANTS))
     (34 17
         (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
     (32 2 (:REWRITE TAKE-OF-TOO-MANY))
     (31 19 (:REWRITE DEFAULT-<-2))
     (30 19 (:REWRITE DEFAULT-<-1))
     (27 12 (:REWRITE LEN-WHEN-ATOM))
     (20 2 (:REWRITE TAKE-OF-LEN-FREE))
     (18 17
         (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
     (18 11 (:REWRITE DEFAULT-CDR))
     (15 15
         (:REWRITE PFIELD::EQUAL-OF-ADD-CANCEL-BIND-FREE))
     (14 14 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (14 6 (:REWRITE ECURVE::RETURNS-LEMMA))
     (12 6 (:REWRITE DEFAULT-+-2))
     (10 1 (:DEFINITION LAST))
     (9 9
        (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
     (9 9 (:REWRITE PFIELD::MUL-COMMUTATIVE))
     (9 9 (:REWRITE PFIELD::MUL-BECOMES-NEG))
     (8 8
        (:REWRITE PFIELD::EQUAL-OF-MUL-CONSTANTS))
     (8 2 (:REWRITE LAST-WHEN-ATOM-OF-CDR))
     (7 7
        (:REWRITE PFIELD::ADD-COMBINE-CONSTANTS))
     (7 2 (:REWRITE DEFAULT-CAR))
     (6 6 (:TYPE-PRESCRIPTION NATP))
     (6 6 (:REWRITE DEFAULT-+-1))
     (6 3
        (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
     (4 2 (:REWRITE TAKE-WHEN-ATOM))
     (4 2 (:REWRITE LAST-WHEN-ATOM))
     (3 3 (:REWRITE PFIELD::SUB-WHEN-CONSTANTS))
     (3 3
        (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
     (3 3
        (:REWRITE PFIELD::NEG-OF-MUL-WHEN-CONSTANT))
     (3 3
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 2))
     (3 3
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 1))
     (3 3 (:REWRITE CONSP-OF-CDDR-BY-LEN))
     (3 3
        (:LINEAR ZCASH::JUBJUB-POINT->V-UPPER-BOUND))
     (3 3
        (:LINEAR ZCASH::JUBJUB-POINT->U-UPPER-BOUND))
     (2 2 (:TYPE-PRESCRIPTION NFIX))
     (2 2 (:REWRITE PFIELD::MUL-COMMUTATIVE-2))
     (2 2
        (:REWRITE PFIELD::MUL-COMBINE-CONSTANTS))
     (2 1 (:REWRITE BIT-LISTP-WHEN-NOT-CONSP))
     (1 1 (:REWRITE SUBSETP-TRANS2))
     (1 1 (:REWRITE SUBSETP-TRANS)))
(ZCASH::JUBJUB-H)
(ZCASH::NATP-OF-JUBJUB-H)
(ZCASH::JUBJUB-R)
(ZCASH::NATP-OF-JUBJUB-R)
(ZCASH::PRIMEP-OF-JUBJUB-R)
(ZCASH::JUBJUB-R-POINTP)
(ZCASH::BOOLEANP-OF-JUBJUB-R-POINTP)
(ZCASH::JUBJUB-POINTP-WHEN-JUBJUB-R-POINTP)
(ZCASH::JUBJUB-RSTAR-POINTP)
(ZCASH::BOOLEANP-OF-JUBJUB-RSTAR-POINTP)
(ZCASH::JUBJUB-R-POINTP-WHEN-JUBJUB-RSTAR-POINTP)
