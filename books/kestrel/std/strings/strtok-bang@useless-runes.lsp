(STR::STRTOK!-AUX (78 74 (:REWRITE DEFAULT-<-1))
                  (75 74 (:REWRITE DEFAULT-<-2))
                  (66 6 (:DEFINITION LEN))
                  (63 30 (:REWRITE DEFAULT-CDR))
                  (60 4 (:DEFINITION NTH))
                  (56 7 (:DEFINITION MEMBER-EQUAL))
                  (47 47
                      (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                  (44 38 (:REWRITE DEFAULT-+-2))
                  (42 6
                      (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
                  (39 24 (:REWRITE DEFAULT-CAR))
                  (38 38 (:REWRITE DEFAULT-+-1))
                  (38 27 (:REWRITE STR::CONSP-OF-EXPLODE))
                  (24 2 (:REWRITE EQLABLEP-NTH))
                  (19 1 (:REWRITE SUBSETP-OF-CONS))
                  (12 12 (:REWRITE SUBSETP-MEMBER . 2))
                  (12 12 (:REWRITE SUBSETP-MEMBER . 1))
                  (12 12 (:REWRITE DEFAULT-UNARY-MINUS))
                  (9 9
                     (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                  (9 6
                     (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
                  (6 6 (:REWRITE SUBSETP-MEMBER . 4))
                  (6 6 (:REWRITE SUBSETP-MEMBER . 3))
                  (6 6 (:REWRITE MEMBER-WHEN-ATOM))
                  (4 4 (:REWRITE SUBSETP-TRANS2))
                  (4 4 (:REWRITE SUBSETP-TRANS))
                  (4 1 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
                  (2 2 (:REWRITE REV-WHEN-NOT-CONSP))
                  (2 2 (:REWRITE FOLD-CONSTS-IN-+))
                  (2 1 (:REWRITE REVERSE-REMOVAL))
                  (1 1 (:TYPE-PRESCRIPTION EQLABLEP))
                  (1 1 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT)))
(STR::STRING-LISTP-OF-STRTOK!-AUX
     (3836 386
           (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
     (3762 421 (:DEFINITION MEMBER-EQUAL))
     (890 486 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (814 814 (:REWRITE SUBSETP-MEMBER . 2))
     (814 814 (:REWRITE SUBSETP-MEMBER . 1))
     (729 516 (:REWRITE DEFAULT-CAR))
     (647 415
          (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
     (582 582 (:REWRITE SUBSETP-TRANS2))
     (582 582 (:REWRITE SUBSETP-TRANS))
     (529 466 (:REWRITE DEFAULT-CDR))
     (486 486 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (476 56 (:REWRITE SUBSETP-CAR-MEMBER))
     (461 25 (:REWRITE SUBSETP-OF-CONS))
     (424 359 (:REWRITE DEFAULT-<-1))
     (365 359 (:REWRITE DEFAULT-<-2))
     (243 243 (:REWRITE SUBSETP-MEMBER . 4))
     (236 236 (:REWRITE MEMBER-WHEN-ATOM))
     (216 24
          (:REWRITE STR::MAKE-CHARACTER-LIST-WHEN-CHARACTER-LISTP))
     (158 156 (:REWRITE DEFAULT-+-2))
     (158 156 (:REWRITE DEFAULT-+-1))
     (144 24 (:DEFINITION CHARACTER-LISTP))
     (130 58 (:REWRITE REV-WHEN-NOT-CONSP))
     (120 120
          (:TYPE-PRESCRIPTION CHARACTER-LISTP))
     (91 91
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (65 65
         (:TYPE-PRESCRIPTION MAKE-CHARACTER-LIST))
     (62 31 (:REWRITE REVERSE-REMOVAL))
     (38 30 (:REWRITE DEFAULT-UNARY-MINUS))
     (24 24
         (:REWRITE STR::MAKE-CHARACTER-LIST-WHEN-ATOM))
     (7 7
        (:REWRITE STR::CONSP-OF-MAKE-CHARACTER-LIST)))
(STR::STREQV-IMPLIES-EQUAL-STRTOK!-AUX-1
     (3569 287
           (:REWRITE STR::MAKE-CHARACTER-LIST-WHEN-CHARACTER-LISTP))
     (2920 326 (:DEFINITION CHARACTER-LISTP))
     (2592 1234 (:REWRITE DEFAULT-CDR))
     (2504 356 (:DEFINITION MEMBER-EQUAL))
     (2406 1219 (:REWRITE DEFAULT-CAR))
     (2150 100 (:DEFINITION BINARY-APPEND))
     (1700 50 (:REWRITE REV-OF-CONS))
     (1490 1490
           (:TYPE-PRESCRIPTION CHARACTER-LISTP))
     (1210 50 (:REWRITE ASSOCIATIVITY-OF-APPEND))
     (1132 1098 (:REWRITE DEFAULT-<-2))
     (1132 1098 (:REWRITE DEFAULT-<-1))
     (1093 1055 (:REWRITE DEFAULT-+-2))
     (1077 377 (:REWRITE CONSP-OF-REV))
     (1063 1055 (:REWRITE DEFAULT-+-1))
     (1063 328 (:REWRITE REV-WHEN-NOT-CONSP))
     (970 50
          (:REWRITE STR::MAKE-CHARACTER-LIST-OF-CONS))
     (880 880
          (:TYPE-PRESCRIPTION MAKE-CHARACTER-LIST))
     (794 794
          (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
     (792 792 (:REWRITE SUBSETP-MEMBER . 4))
     (750 200 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (712 712 (:REWRITE MEMBER-WHEN-ATOM))
     (700 40 (:REWRITE CHARACTERP-NTH))
     (582 291 (:REWRITE REVERSE-REMOVAL))
     (555 531
          (:REWRITE STR::CONSP-OF-MAKE-CHARACTER-LIST))
     (390 30 (:DEFINITION LEN))
     (320 30 (:REWRITE CHAR-FIX-WHEN-CHARACTERP))
     (298 40 (:REWRITE SUBSETP-CAR-MEMBER))
     (273 237
          (:REWRITE STR::MAKE-CHARACTER-LIST-WHEN-ATOM))
     (198 18 (:REWRITE STR::EQUAL-OF-IMPLODES))
     (168 168 (:REWRITE SUBSETP-MEMBER . 2))
     (114 114 (:REWRITE SUBSETP-TRANS2))
     (114 114 (:REWRITE SUBSETP-TRANS))
     (100 100
          (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (100 30 (:REWRITE CHAR-FIX-DEFAULT))
     (88 34 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (78 78 (:REWRITE DEFAULT-UNARY-MINUS))
     (62 62
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (34 34 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (30 30
         (:REWRITE CHARACTER-LISTP-OF-EXPLODE)))
(STR::STRTOK! (88 8 (:DEFINITION LEN))
              (81 3 (:DEFINITION TRUE-LISTP))
              (53 6
                  (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
              (40 13 (:REWRITE DEFAULT-CDR))
              (38 6
                  (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
              (24 16 (:REWRITE STR::CONSP-OF-EXPLODE))
              (16 8 (:REWRITE DEFAULT-+-2))
              (12 12 (:TYPE-PRESCRIPTION STRING-LISTP))
              (9 3
                 (:REWRITE STRING-LISTP-OF-CDR-WHEN-STRING-LISTP))
              (8 8 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
              (8 8
                 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
              (8 8
                 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
              (8 8 (:REWRITE DEFAULT-+-1))
              (8 4
                 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
              (8 4 (:REWRITE SET::NONEMPTY-MEANS-SET))
              (4 4 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
              (4 4 (:REWRITE SET::IN-SET))
              (4 2 (:REWRITE DEFAULT-<-1))
              (3 2 (:REWRITE DEFAULT-<-2))
              (2 2
                 (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
              (2 2 (:REWRITE REV-WHEN-NOT-CONSP))
              (2 2 (:REWRITE DEFAULT-CAR))
              (2 1
                 (:REWRITE STR::STRING-LISTP-OF-STRTOK!-AUX)))
(STR::STRING-LISTP-OF-STRTOK!)
(STR::STREQV-IMPLIES-EQUAL-STRTOK!-1)
