(APT::CANONICAL-HINTS-SPECIFIER-P
 (248 4 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (116 4 (:DEFINITION MEMBER-EQUAL))
 (111 78 (:REWRITE DEFAULT-CDR))
 (95 5 (:DEFINITION TRUE-LISTP))
 (88 8 (:REWRITE SUBSETP-CAR-MEMBER))
 (87 87
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP
               . 2))
 (87 87
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP
               . 1))
 (87 87
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
               . 2))
 (87 87
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
               . 1))
 (60 60
     (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP))
 (60 60
     (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP))
 (60 10
     (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (51 50 (:REWRITE DEFAULT-CAR))
 (40 8 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (40 8 (:REWRITE MEMBER-WHEN-ATOM))
 (20 20 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (20 10 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (19 19
     (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (10 10 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (10 10
     (:REWRITE TRUE-LISTP-WHEN-THEOREM-SYMBOL-LISTP))
 (10 10
     (:REWRITE TRUE-LISTP-WHEN-TERMFN-LISTP))
 (10 10
     (:REWRITE TRUE-LISTP-WHEN-MACRO-SYMBOL-LISTP))
 (10 10
     (:REWRITE TRUE-LISTP-WHEN-LAMBDA-LISTP))
 (10 10
     (:REWRITE TRUE-LISTP-WHEN-FUNCTION-SYMBOL-LISTP))
 (10
    10
    (:REWRITE TRUE-LISTP-OF-CDR-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP))
 (10 10 (:REWRITE SET::IN-SET))
 (8 8 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (8 8 (:REWRITE SUBSETP-TRANS2))
 (8 8 (:REWRITE SUBSETP-TRANS))
 (8 8 (:REWRITE SUBSETP-MEMBER . 4))
 (8 8 (:REWRITE SUBSETP-MEMBER . 3))
 (8 8 (:REWRITE SUBSETP-MEMBER . 2))
 (8 8 (:REWRITE SUBSETP-MEMBER . 1))
 (8 8 (:REWRITE INTERSECTP-MEMBER . 3))
 (8 8 (:REWRITE INTERSECTP-MEMBER . 2))
 (4 4 (:TYPE-PRESCRIPTION MEMBER-EQUAL)))
(APT::BOOLEANP-OF-CANONICAL-HINTS-SPECIFIER-P)
(APT::HINTS-SPECIFIER-P)
(APT::BOOLEANP-OF-HINTS-SPECIFIER-P)
(KEYWORD-LISTP-FORWARD-TO-SYMBOL-LISTP
   (14 14
       (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP))
   (14 14
       (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP))
   (11 11 (:REWRITE DEFAULT-CAR))
   (8 8
      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP
                . 2))
   (8 8
      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP
                . 1))
   (8 8
      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                . 2))
   (8 8
      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                . 1))
   (4 4
      (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
   (4 4 (:REWRITE DEFAULT-CDR)))
(APT::CANONICALIZE-HINTS-SPECIFIER-P-MAKE-KEYWORD-VALUE-LIST-FROM-KEYS-AND-VALUE
   (346 12 (:DEFINITION MEMBER-EQUAL))
   (151 29 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
   (124 75 (:REWRITE DEFAULT-CDR))
   (110 110
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP
                  . 2))
   (110 110
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP
                  . 1))
   (110 110
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 2))
   (110 110
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 1))
   (110 22 (:REWRITE MEMBER-WHEN-ATOM))
   (67 24 (:REWRITE SUBSETP-MEMBER . 2))
   (58 54 (:REWRITE DEFAULT-CAR))
   (57 29 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
   (33 32 (:REWRITE SUBSETP-TRANS2))
   (24 24 (:REWRITE SUBSETP-MEMBER . 1))
   (23 23 (:REWRITE INTERSECTP-MEMBER . 3))
   (23 23 (:REWRITE INTERSECTP-MEMBER . 2))
   (22 22 (:REWRITE SUBSETP-MEMBER . 3))
   (18 18
       (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP))
   (18 18
       (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP))
   (10 10
       (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME)))
(APT::CANONICALIZE-HINTS-SPECIFIER)
(APT::RETURN-TYPE-OF-CANONICALIZE-HINTS-SPECIFIER
    (120 2 (:DEFINITION NO-DUPLICATESP-EQUAL))
    (58 2 (:DEFINITION MEMBER-EQUAL))
    (44 4 (:REWRITE SUBSETP-CAR-MEMBER))
    (30 2 (:DEFINITION KEYWORD-LISTP))
    (20 4 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
    (20 4 (:REWRITE MEMBER-WHEN-ATOM))
    (14 14
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP
                  . 2))
    (14 14
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP
                  . 1))
    (14 14
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 2))
    (14 14
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 1))
    (14 2 (:DEFINITION KEYWORDP))
    (8 8 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
    (8 8 (:REWRITE DEFAULT-CDR))
    (6 6 (:REWRITE DEFAULT-CAR))
    (5 5
       (:TYPE-PRESCRIPTION APT::CANONICALIZE-HINTS-SPECIFIER))
    (4 4
       (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
    (4 4
       (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP))
    (4 4
       (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP))
    (4 4 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
    (4 4 (:REWRITE SUBSETP-TRANS2))
    (4 4 (:REWRITE SUBSETP-TRANS))
    (4 4 (:REWRITE SUBSETP-MEMBER . 4))
    (4 4 (:REWRITE SUBSETP-MEMBER . 3))
    (4 4 (:REWRITE SUBSETP-MEMBER . 2))
    (4 4 (:REWRITE SUBSETP-MEMBER . 1))
    (4 4 (:REWRITE INTERSECTP-MEMBER . 3))
    (4 4 (:REWRITE INTERSECTP-MEMBER . 2))
    (2 2 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
    (2 2
       (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME)))
(APT::ENSURE-IS-HINTS-SPECIFIER
     (1 1
        (:TYPE-PRESCRIPTION APT::CANONICALIZE-HINTS-SPECIFIER)))
(APT::RETURN-TYPE-OF-ENSURE-IS-HINTS-SPECIFIER.ERP)
(APT::RETURN-TYPE-OF-ENSURE-IS-HINTS-SPECIFIER.VAL
    (180 3 (:DEFINITION NO-DUPLICATESP-EQUAL))
    (87 3 (:DEFINITION MEMBER-EQUAL))
    (66 6 (:REWRITE SUBSETP-CAR-MEMBER))
    (45 3 (:DEFINITION KEYWORD-LISTP))
    (30 6 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
    (30 6 (:REWRITE MEMBER-WHEN-ATOM))
    (27 27
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP
                  . 2))
    (27 27
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP
                  . 1))
    (27 27
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 2))
    (27 27
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 1))
    (26 2 (:DEFINITION CHARACTER-ALISTP))
    (21 3 (:DEFINITION KEYWORDP))
    (18 6
        (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
    (17 17 (:REWRITE DEFAULT-CAR))
    (16 16 (:REWRITE DEFAULT-CDR))
    (12 12 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
    (6 6
       (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
    (6 6
       (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP))
    (6 6
       (:REWRITE SYMBOLP-OF-CAR-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP))
    (6 6 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
    (6 6 (:REWRITE SUBSETP-TRANS2))
    (6 6 (:REWRITE SUBSETP-TRANS))
    (6 6 (:REWRITE SUBSETP-MEMBER . 4))
    (6 6 (:REWRITE SUBSETP-MEMBER . 3))
    (6 6 (:REWRITE SUBSETP-MEMBER . 2))
    (6 6 (:REWRITE SUBSETP-MEMBER . 1))
    (6 6 (:REWRITE INTERSECTP-MEMBER . 3))
    (6 6 (:REWRITE INTERSECTP-MEMBER . 2))
    (3 3 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
    (3 3
       (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
    (2 2
       (:REWRITE MSGP-WHEN-MEMBER-EQUAL-OF-MSG-LISTP)))
