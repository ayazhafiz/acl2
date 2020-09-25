(SHA2::INTEGERP-WHEN-UNSIGNED-BYTE-P-64)
(SHA2::SHA-384
     (5 1 (:DEFINITION LEN))
     (2 2 (:REWRITE DEFAULT-CDR))
     (2 1 (:REWRITE DEFAULT-<-2))
     (2 1 (:REWRITE DEFAULT-+-2))
     (2 1 (:DEFINITION TRUE-LISTP))
     (1 1 (:REWRITE DEFAULT-<-1))
     (1 1 (:REWRITE DEFAULT-+-1))
     (1 1
        (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
     (1 1
        (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER)))
(SHA2::SHA-384-BYTES)
(SHA2::ALL-UNSIGNED-BYTE-P-OF-SHA-384-BYTES
     (190 5
          (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
     (40 20
         (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
     (26 26 (:REWRITE UNPACKBV-WHEN-ZP))
     (26 26
         (:REWRITE UNPACKBV-WHEN-NOT-INTEGERP))
     (15 5 (:REWRITE CONSP-OF-APPEND))
     (5 5 (:REWRITE CONSP-OF-UNPACKBV))
     (5 5
        (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER)))
(SHA2::ALL-INTEGERP-OF-SHA-384-BYTES
     (4 1
        (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
     (1 1
        (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER)))
(SHA2::LEN-OF-SHA-384-BYTES (10 5
                                (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
                            (6 6 (:REWRITE UNPACKBV-WHEN-ZP))
                            (6 6 (:REWRITE UNPACKBV-WHEN-NOT-INTEGERP))
                            (5 5 (:TYPE-PRESCRIPTION UNPACKBV)))
