(BLAKE::WORDP)
(BLAKE::WORDP-FORWARD-TO-NATP)
(BLAKE::ALL-WORDP)
(BLAKE::ALL-WORDP-OF-CONS (20 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
                          (10 10 (:TYPE-PRESCRIPTION LEN))
                          (4 2 (:REWRITE DEFAULT-<-2))
                          (3 3 (:REWRITE DEFAULT-CDR))
                          (3 3 (:REWRITE DEFAULT-CAR))
                          (2 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
                          (2 2 (:REWRITE DEFAULT-<-1))
                          (2 2 (:REWRITE CONSP-WHEN-LEN-GREATER))
                          (2 2
                             (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP)))
(BLAKE::ALL-WORDP-OF-UPDATE-NTH
     (35 14 (:REWRITE DEFAULT-CDR))
     (32 13 (:REWRITE DEFAULT-CAR))
     (13 13 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (12 8 (:REWRITE DEFAULT-<-2))
     (12 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
     (9 8
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (9 1 (:LINEAR LEN-OF-CDR-LINEAR))
     (8 8 (:REWRITE DEFAULT-<-1))
     (7 7 (:REWRITE DEFAULT-+-2))
     (7 7 (:REWRITE DEFAULT-+-1))
     (5 5 (:REWRITE ZP-OPEN))
     (4 2 (:REWRITE INTEGERP-WHEN-POWER-OF-2P))
     (2 2 (:TYPE-PRESCRIPTION POWER-OF-2P)))
(BLAKE::WORDP-OF-NTH-WHEN-ALL-WORDP
     (36 36 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (34 12 (:REWRITE DEFAULT-CDR))
     (27 18 (:REWRITE DEFAULT-<-2))
     (23 7 (:REWRITE DEFAULT-CAR))
     (18 18 (:REWRITE DEFAULT-<-1))
     (17 17 (:REWRITE DEFAULT-+-2))
     (17 17 (:REWRITE DEFAULT-+-1))
     (15 9 (:REWRITE ZP-OPEN))
     (10 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
     (8 1 (:LINEAR LEN-OF-CDR-LINEAR))
     (6 2 (:REWRITE FOLD-CONSTS-IN-+))
     (4 2 (:REWRITE INTEGERP-WHEN-POWER-OF-2P))
     (2 2 (:TYPE-PRESCRIPTION POWER-OF-2P)))
(BLAKE::INTEGERP-OF-NTH-WHEN-ALL-WORDP)
(BLAKE::ACL2-NUMBERP-OF-NTH-WHEN-ALL-WORDP)
(BLAKE::RATIONALP-OF-NTH-WHEN-ALL-WORDP)
(BLAKE::ALL-WORDP-OF-APPEND
     (70 3 (:REWRITE CONSP-OF-APPEND))
     (66 54 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (51 26 (:REWRITE DEFAULT-<-2))
     (46 31
         (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (44 20 (:REWRITE DEFAULT-CAR))
     (39 15 (:REWRITE DEFAULT-CDR))
     (26 26 (:REWRITE DEFAULT-<-1))
     (26 26 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (20 4 (:REWRITE LEN-OF-CDR))
     (17 11 (:REWRITE DEFAULT-+-2))
     (16 8
         (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (14 11 (:REWRITE DEFAULT-+-1))
     (14 2 (:REWRITE COMMUTATIVITY-OF-+))
     (12 1 (:REWRITE COMMUTATIVITY-2-OF-+))
     (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (8 8 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (3 3
        (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(BLAKE::BLOCKP)
(BLAKE::BLOCKP-FORWARD-TO-TRUE-LISTP)
(BLAKE::BLOCKP-FORWARD-TO-EQUAL-OF-LEN)
(BLAKE::ACL2-NUMBERP-OF-NTH-WHEN-BLOCKP)
(BLAKE::INTEGERP-OF-NTH-WHEN-BLOCKP)
(BLAKE::RATIONALP-OF-NTH-WHEN-BLOCKP)
(BLAKE::WORDP-OF-NTH-WHEN-BLOCKP)
(BLAKE::BLOCKP-OF-UPDATE-NTH
     (6 4 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (4 1 (:DEFINITION TRUE-LISTP))
     (3 3
        (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
     (2 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (2 1 (:REWRITE INTEGERP-WHEN-POWER-OF-2P))
     (2 1 (:REWRITE DEFAULT-CDR))
     (1 1 (:TYPE-PRESCRIPTION POWER-OF-2P))
     (1 1 (:REWRITE DEFAULT-+-2))
     (1 1 (:REWRITE DEFAULT-+-1))
     (1 1
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP)))
(BLAKE::BLOCKP-OF-APPEND
     (13 1 (:DEFINITION TRUE-LISTP))
     (10 1 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (8 6 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (4 2 (:REWRITE DEFAULT-+-2))
     (4 2 (:REWRITE DEFAULT-+-1))
     (2 2
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (2 1 (:REWRITE DEFAULT-<-2))
     (1 1
        (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
     (1 1 (:REWRITE DEFAULT-CDR))
     (1 1 (:REWRITE DEFAULT-<-1))
     (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (1 1
        (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP)))
(BLAKE::ALL-BLOCKP)
(BLAKE::ALL-BLOCKP-OF-CONS
     (20 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (10 10 (:TYPE-PRESCRIPTION LEN))
     (4 2 (:REWRITE DEFAULT-<-2))
     (3 3 (:REWRITE DEFAULT-CDR))
     (3 3 (:REWRITE DEFAULT-CAR))
     (2 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (2 2 (:REWRITE DEFAULT-<-1))
     (2 2 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (2 2
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP)))
(BLAKE::BLOCKP-OF-NTH-WHEN-ALL-BLOCKP
     (17 17 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (15 9 (:REWRITE DEFAULT-CAR))
     (12 8 (:REWRITE DEFAULT-<-2))
     (12 7 (:REWRITE DEFAULT-CDR))
     (10 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
     (8 8 (:REWRITE DEFAULT-<-1))
     (8 1 (:LINEAR LEN-OF-CDR-LINEAR))
     (7 7 (:REWRITE DEFAULT-+-2))
     (7 7 (:REWRITE DEFAULT-+-1))
     (5 5 (:REWRITE ZP-OPEN))
     (4 2 (:REWRITE INTEGERP-WHEN-POWER-OF-2P))
     (2 2 (:TYPE-PRESCRIPTION POWER-OF-2P)))
(BLAKE::IV)
(BLAKE::SIGMA)
(BLAKE::LEN-OF-SIGMA)
(BLAKE::ITEMS-HAVE-LEN-OF-SIGMA)
(BLAKE::ALL-TRUE-LISTP-OF-SIGMA)
(BLAKE::LEN-OF-NTH-OF-SIGMA
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (2 2
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (2 1
        (:REWRITE ITEMS-HAVE-LEN-WHEN-NOT-CONSP))
     (2 1 (:REWRITE INTEGERP-WHEN-POWER-OF-2P))
     (1 1 (:TYPE-PRESCRIPTION BLAKE::SIGMA))
     (1 1 (:TYPE-PRESCRIPTION POWER-OF-2P))
     (1 1 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP)))
(BLAKE::ALL-NAT16)
(BLAKE::<-OF-NTH-WHEN-ALL-NAT16
     (79 27 (:REWRITE DEFAULT-<-1))
     (32 27 (:REWRITE DEFAULT-<-2))
     (28 4
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (21 15 (:REWRITE DEFAULT-CAR))
     (18 18 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (16 16 (:TYPE-PRESCRIPTION BLAKE::BLOCKP))
     (16 16
         (:TYPE-PRESCRIPTION BLAKE::ALL-WORDP))
     (16 8 (:REWRITE INTEGERP-WHEN-POWER-OF-2P))
     (14 14 (:TYPE-PRESCRIPTION POWER-OF-2P))
     (12 7 (:REWRITE DEFAULT-CDR))
     (12 6 (:REWRITE NATP-WHEN-POWER-OF-2P))
     (12 4
         (:REWRITE BLAKE::RATIONALP-OF-NTH-WHEN-BLOCKP))
     (12 4
         (:REWRITE BLAKE::RATIONALP-OF-NTH-WHEN-ALL-WORDP))
     (12 4
         (:REWRITE BLAKE::ACL2-NUMBERP-OF-NTH-WHEN-BLOCKP))
     (12 4
         (:REWRITE BLAKE::ACL2-NUMBERP-OF-NTH-WHEN-ALL-WORDP))
     (10 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
     (8 1 (:LINEAR LEN-OF-CDR-LINEAR))
     (7 7 (:REWRITE DEFAULT-+-2))
     (7 7 (:REWRITE DEFAULT-+-1))
     (5 5 (:REWRITE ZP-OPEN)))
(BLAKE::<=-OF-0-AND-NTH-WHEN-ALL-NAT16
     (79 27 (:REWRITE DEFAULT-<-1))
     (32 27 (:REWRITE DEFAULT-<-2))
     (28 4
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (21 15 (:REWRITE DEFAULT-CAR))
     (18 18 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (16 16 (:TYPE-PRESCRIPTION BLAKE::BLOCKP))
     (16 16
         (:TYPE-PRESCRIPTION BLAKE::ALL-WORDP))
     (16 8 (:REWRITE INTEGERP-WHEN-POWER-OF-2P))
     (14 14 (:TYPE-PRESCRIPTION POWER-OF-2P))
     (12 7 (:REWRITE DEFAULT-CDR))
     (12 6 (:REWRITE NATP-WHEN-POWER-OF-2P))
     (12 4
         (:REWRITE BLAKE::RATIONALP-OF-NTH-WHEN-BLOCKP))
     (12 4
         (:REWRITE BLAKE::RATIONALP-OF-NTH-WHEN-ALL-WORDP))
     (12 4
         (:REWRITE BLAKE::ACL2-NUMBERP-OF-NTH-WHEN-BLOCKP))
     (12 4
         (:REWRITE BLAKE::ACL2-NUMBERP-OF-NTH-WHEN-ALL-WORDP))
     (10 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
     (8 1 (:LINEAR LEN-OF-CDR-LINEAR))
     (7 7 (:REWRITE DEFAULT-+-2))
     (7 7 (:REWRITE DEFAULT-+-1))
     (5 5 (:REWRITE ZP-OPEN)))
(BLAKE::NATP-OF-NTH-WHEN-ALL-NAT16
     (32 26 (:REWRITE DEFAULT-<-2))
     (30 15 (:REWRITE INTEGERP-WHEN-POWER-OF-2P))
     (26 26 (:REWRITE DEFAULT-<-1))
     (26 18 (:REWRITE DEFAULT-CAR))
     (23 23 (:TYPE-PRESCRIPTION POWER-OF-2P))
     (19 19 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (16 9 (:REWRITE DEFAULT-CDR))
     (16 8 (:REWRITE NATP-WHEN-POWER-OF-2P))
     (13 5
         (:REWRITE BLAKE::INTEGERP-OF-NTH-WHEN-BLOCKP))
     (13 5
         (:REWRITE BLAKE::INTEGERP-OF-NTH-WHEN-ALL-WORDP))
     (10 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
     (8 8 (:TYPE-PRESCRIPTION BLAKE::BLOCKP))
     (8 8 (:TYPE-PRESCRIPTION BLAKE::ALL-WORDP))
     (8 8 (:REWRITE DEFAULT-+-2))
     (8 8 (:REWRITE DEFAULT-+-1))
     (8 1 (:LINEAR LEN-OF-CDR-LINEAR))
     (6 6 (:REWRITE ZP-OPEN)))
(BLAKE::INTEGERP-OF-NTH-WHEN-ALL-NAT16)
(BLAKE::ALL-ALL-NAT16)
(BLAKE::ALL-ALL-NAT16-OF-SIGMA)
(BLAKE::ALL-NAT16-OF-NTH-WHEN-ALL-ALL-NAT16
     (59 43 (:REWRITE DEFAULT-<-2))
     (43 43 (:REWRITE DEFAULT-<-1))
     (37 31 (:REWRITE DEFAULT-CAR))
     (29 29 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (26 13 (:REWRITE INTEGERP-WHEN-POWER-OF-2P))
     (24 24 (:TYPE-PRESCRIPTION POWER-OF-2P))
     (23 18 (:REWRITE DEFAULT-CDR))
     (22 11 (:REWRITE NATP-WHEN-POWER-OF-2P))
     (11 11 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (10 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
     (8 1 (:LINEAR LEN-OF-CDR-LINEAR))
     (7 7
        (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
     (7 7 (:REWRITE DEFAULT-+-2))
     (7 7 (:REWRITE DEFAULT-+-1))
     (5 5 (:REWRITE ZP-OPEN))
     (4 4
        (:REWRITE LEN-OF-NTH-WHEN-ITEMS-HAVE-LEN)))
(BLAKE::ROT-WORD)
(BLAKE::WORDP-OF-ROT-WORD
     (261 2 (:DEFINITION POSP))
     (192 16 (:REWRITE MOD-WHEN-MULTIPLE))
     (192 16
          (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
     (156 4 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (144 4 (:LINEAR MOD-BOUND-LINEAR-ARG2))
     (138 2
          (:REWRITE BVCAT-WHEN-LOWSIZE-IS-NOT-POSP))
     (134 3 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
     (131 3 (:REWRITE SLICE-OUT-OF-ORDER))
     (128 32 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
     (96 32 (:REWRITE COMMUTATIVITY-OF-*))
     (80 40 (:REWRITE INTEGERP-WHEN-POWER-OF-2P))
     (64 64 (:REWRITE DEFAULT-*-2))
     (64 64 (:REWRITE DEFAULT-*-1))
     (48 16 (:REWRITE MOD-WHEN-<))
     (43 25 (:REWRITE DEFAULT-<-2))
     (42 42 (:TYPE-PRESCRIPTION POWER-OF-2P))
     (32 25 (:REWRITE DEFAULT-<-1))
     (27 1 (:REWRITE BVCAT-OF-BVCHOP-TIGHTEN))
     (27 1
         (:REWRITE BVCAT-OF-BVCHOP-HIGH-TIGHTEN))
     (20 5 (:REWRITE DEFAULT-+-2))
     (16 16
         (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (16 16
         (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (16 16
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (16 16
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (16 16
         (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
     (11 5 (:REWRITE DEFAULT-+-1))
     (9 3
        (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
     (8 4
        (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP-WHEN-ALREADY))
     (6 4 (:REWRITE BVCAT-FIX-CONSTANT-ARG2))
     (6 3 (:REWRITE SLICE-WHEN-LOW-IS-NEGATIVE))
     (6 3
        (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
     (6 3
        (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
     (5 5 (:REWRITE BVCHOP-SUBST-CONSTANT))
     (5 2
        (:REWRITE BVCAT-WHEN-HIGHVAL-IS-NOT-AN-INTEGER))
     (4 4
        (:REWRITE BVCAT-WHEN-ARG2-IS-NOT-AN-INTEGER))
     (4 4 (:REWRITE BVCAT-FIX-CONSTANT-ARG4))
     (4 2 (:REWRITE NATP-WHEN-POWER-OF-2P))
     (4 2
        (:REWRITE BVCAT-WHEN-LOWVAL-IS-NOT-AN-INTEGER))
     (4 1 (:REWRITE DEFAULT-UNARY-MINUS))
     (3 3 (:TYPE-PRESCRIPTION POSP))
     (3 3 (:REWRITE SLICE-WHEN-BVCHOP-KNOWN))
     (3 3 (:REWRITE SLICE-TOO-HIGH-LEMMA))
     (3 3
        (:REWRITE SLICE-SUBST-IN-CONSTANT-ALT))
     (3 3 (:REWRITE SLICE-SUBST-IN-CONSTANT))
     (3 3
        (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
     (3 1
        (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER))
     (3 1 (:REWRITE SLICE-TOO-HIGH-IS-0))
     (2 2 (:TYPE-PRESCRIPTION SLICE))
     (2 2 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG1))
     (1 1 (:TYPE-PRESCRIPTION NATP-OF-BVCHOP))
     (1 1
        (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER-CHEAP))
     (1 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(BLAKE::WORDXOR)
(BLAKE::WORDP-OF-WORDXOR)
