(CRYPTO::SHA-256-BYTES-WRAPPER
     (27 9
         (:REWRITE BYTE-LISTP-WHEN-BYTE-LIST32P-REWRITE))
     (23 12 (:REWRITE DEFAULT-+-2))
     (18 18 (:TYPE-PRESCRIPTION BYTE-LIST32P))
     (18 18 (:REWRITE DEFAULT-CDR))
     (18 10 (:REWRITE DEFAULT-<-1))
     (18 2 (:DEFINITION MEMBER-EQUAL))
     (15 12
         (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
     (15 2
         (:REWRITE BYTEP-WHEN-MEMBER-EQUAL-OF-BYTE-LISTP))
     (14 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
     (12 12 (:REWRITE DEFAULT-+-1))
     (11 10 (:REWRITE DEFAULT-<-2))
     (10 10 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (8 8 (:REWRITE BYTE-LISTP-WHEN-NOT-CONSP))
     (4 4 (:REWRITE SUBSETP-MEMBER . 2))
     (4 4 (:REWRITE SUBSETP-MEMBER . 1))
     (3 3 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-CDR))
     (2 2
        (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
     (2 2 (:REWRITE DEFAULT-CAR))
     (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2)))
(CRYPTO::BYTE-LISTP-OF-SHA-256-BYTES-WRAPPER)
(CRYPTO::LEN-OF-SHA-256-BYTES-WRAPPER)
(CRYPTO::SHA-256-BYTES-WRAPPER-OF-BYTE-LIST-FIX-BYTES)
(CRYPTO::SHA-256-BYTES-WRAPPER-OF-BYTE-LIST-FIX-BYTES-NORMALIZE-CONST)
(CRYPTO::SHA-256-BYTES-WRAPPER-BYTE-LIST-EQUIV-CONGRUENCE-ON-BYTES)
