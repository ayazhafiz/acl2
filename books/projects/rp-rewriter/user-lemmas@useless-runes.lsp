(RP::DONT-RW-SYNTAXP-AUX-CONS)
(RP::DONT-RW-SYNTAXP-CONS)
(RP::MAKE-FAST-ALIST-DEF)
(RP::LEN-CONS (10 5 (:REWRITE DEFAULT-+-2))
              (6 6 (:LINEAR LEN-WHEN-PREFIXP))
              (5 5 (:REWRITE DEFAULT-+-1))
              (3 3 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
              (3 3 (:REWRITE DEFAULT-CDR))
              (3 3 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
              (3 3 (:LINEAR BOUNDS-POSITION-EQUAL)))
(RP::ATOM-CONS)
(RP::CONSP-CONS)
(RP::EQUAL-TO-T)
(RP::BOOLEAN-LISTP-IS-BOOLEANP)
(RP::APPEND-OF-NIL (22 11
                       (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                   (11 11 (:TYPE-PRESCRIPTION TRUE-LISTP))
                   (11 11 (:TYPE-PRESCRIPTION BINARY-APPEND)))
(RP::FORCE-FAIL)
(RP::FORCE$-FAIL)
(RP::FORCE$-OF-T)
