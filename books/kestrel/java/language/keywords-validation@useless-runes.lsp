(JAVA::GRAMMAR-JKEYWORDP)
(JAVA::GRAMMAR-JKEYWORDP-SUFF)
(JAVA::BOOLEANP-OF-GRAMMAR-JKEYWORDP)
(JAVA::GRAMMAR-JKEYWORDP)
(JAVA::JKEYWORD-TREE
 (103 103
      (:REWRITE JAVA::ASCII=>STRING-OF-ASCII-LIST-FIX-ASCII-NORMALIZE-CONST))
 (102 102
      (:REWRITE ABNF::TREEP-WHEN-PARSE-TREEP))
 (102 102
      (:REWRITE ABNF::TREEP-WHEN-IN-TREE-SETP-BINDS-FREE-X))
 (102 102
      (:REWRITE ABNF::TREE-LISTP-WHEN-SUBSETP-EQUAL))
 (102 102
      (:REWRITE ABNF::TREE-LISTP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-LISTP))
 (102 102
      (:REWRITE ABNF::TREE-LIST-LISTP-WHEN-SUBSETP-EQUAL))
 (102 102 (:REWRITE SUBSETP-TRANS2))
 (102 102 (:REWRITE SUBSETP-TRANS))
 (102 102
      (:REWRITE JAVA::ABNF-TREEP-WHEN-ABNF-TREE-WITH-ROOT-P))
 (52 52 (:REWRITE SUBSETP-MEMBER . 4))
 (52 52 (:REWRITE SUBSETP-MEMBER . 3))
 (52 52 (:REWRITE SUBSETP-MEMBER . 2))
 (52 52 (:REWRITE SUBSETP-MEMBER . 1))
 (52 52 (:REWRITE INTERSECTP-MEMBER . 3))
 (52 52 (:REWRITE INTERSECTP-MEMBER . 2))
 (51 51
     (:REWRITE ABNF::TREE-LISTP-WHEN-NOT-CONSP))
 (51 51
     (:REWRITE ABNF::TREE-LIST-LISTP-WHEN-NOT-CONSP))
 (51 51
     (:REWRITE ABNF::TREE-LEAFTERM-OF-NAT-LIST-FIX-GET-NORMALIZE-CONST))
 (51 51
     (:REWRITE JAVA::ABNF-TREE-LISTP-WHEN-ABNF-TREE-LIST-WITH-ROOT-P))
 (3 1
    (:REWRITE JAVA::ASCII-LISTP-WHEN-NOT-CONSP))
 (1 1
    (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
              . 2))
 (1 1
    (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
              . 1)))
(JAVA::RETURN-TYPE-OF-JKEYWORD-TREE
 (52 52 (:REWRITE SUBSETP-MEMBER . 4))
 (52 52 (:REWRITE SUBSETP-MEMBER . 3))
 (52 52 (:REWRITE SUBSETP-MEMBER . 2))
 (52 52 (:REWRITE SUBSETP-MEMBER . 1))
 (52 52 (:REWRITE INTERSECTP-MEMBER . 3))
 (52 52 (:REWRITE INTERSECTP-MEMBER . 2))
 (3 1
    (:REWRITE JAVA::ASCII-LISTP-WHEN-NOT-CONSP))
 (2 2
    (:REWRITE JAVA::ASCII-LISTP-WHEN-SUBSETP-EQUAL))
 (2
  2
  (:REWRITE
   JAVA::ABNF-TREE-WITH-ROOT-P-WHEN-MEMBER-EQUAL-OF-ABNF-TREE-LIST-WITH-ROOT-P))
 (1 1
    (:REWRITE
         ABNF::TREE-NONLEAF-OF-TREE-LIST-LIST-FIX-BRANCHES-NORMALIZE-CONST))
 (1 1
    (:REWRITE
         ABNF::TREE-NONLEAF-OF-MAYBE-RULENAME-FIX-RULENAME?-NORMALIZE-CONST))
 (1 1
    (:REWRITE ABNF::TREE-LEAFTERM-OF-NAT-LIST-FIX-GET-NORMALIZE-CONST))
 (1 1
    (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
              . 2))
 (1 1
    (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
              . 1))
 (1
  1
  (:REWRITE
   ABNF::CONS-OF-TREE-LIST-LIST-FIX-Y-NORMALIZE-CONST-UNDER-TREE-LIST-LIST-EQUIV))
 (1
   1
   (:REWRITE
        ABNF::CONS-OF-TREE-LIST-FIX-Y-NORMALIZE-CONST-UNDER-TREE-LIST-EQUIV))
 (1
  1
  (:REWRITE
   ABNF::CONS-OF-TREE-LIST-FIX-X-NORMALIZE-CONST-UNDER-TREE-LIST-LIST-EQUIV))
 (1
   1
   (:REWRITE ABNF::CONS-OF-TREE-FIX-X-NORMALIZE-CONST-UNDER-TREE-LIST-EQUIV))
 (1 1
    (:REWRITE JAVA::ASCII=>STRING-OF-ASCII-LIST-FIX-ASCII-NORMALIZE-CONST))
 (1 1
    (:REWRITE
         JAVA::ABNF-TREE-WITH-ROOT-P-OF-STR-FIX-RULENAME-NORMALIZE-CONST)))
(JAVA::TREE->STRING-OF-KEYWORD-TREE
 (158 54
      (:REWRITE JAVA::ASCII-LISTP-WHEN-NOT-CONSP))
 (156 1 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (108 108
      (:REWRITE JAVA::ASCII-LISTP-WHEN-SUBSETP-EQUAL))
 (104 104 (:REWRITE SUBSETP-MEMBER . 4))
 (104 104 (:REWRITE SUBSETP-MEMBER . 3))
 (104 104 (:REWRITE SUBSETP-MEMBER . 2))
 (104 104 (:REWRITE SUBSETP-MEMBER . 1))
 (104 104 (:REWRITE INTERSECTP-MEMBER . 3))
 (104 104 (:REWRITE INTERSECTP-MEMBER . 2))
 (104 104
      (:REWRITE JAVA::ASCII=>STRING-OF-ASCII-LIST-FIX-ASCII-NORMALIZE-CONST))
 (53 53
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
               . 2))
 (53 53
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
               . 1))
 (6 1
    (:REWRITE ABNF::TREEP-WHEN-MAYBE-TREEP))
 (3 1
    (:REWRITE ABNF::MAYBE-TREEP-WHEN-TREEP))
 (2 2
    (:TYPE-PRESCRIPTION ABNF::MAYBE-TREEP))
 (2 2
    (:REWRITE ABNF::TREE-LEAFTERM-OF-NAT-LIST-FIX-GET-NORMALIZE-CONST))
 (2 2
    (:REWRITE ABNF::TREE->STRING-OF-TREE-FIX-TREE-NORMALIZE-CONST))
 (2
  2
  (:REWRITE
   ABNF::CONS-OF-TREE-LIST-LIST-FIX-Y-NORMALIZE-CONST-UNDER-TREE-LIST-LIST-EQUIV))
 (2
   2
   (:REWRITE
        ABNF::CONS-OF-TREE-LIST-FIX-Y-NORMALIZE-CONST-UNDER-TREE-LIST-EQUIV))
 (2
  2
  (:REWRITE
   ABNF::CONS-OF-TREE-LIST-FIX-X-NORMALIZE-CONST-UNDER-TREE-LIST-LIST-EQUIV))
 (2
   2
   (:REWRITE ABNF::CONS-OF-TREE-FIX-X-NORMALIZE-CONST-UNDER-TREE-LIST-EQUIV))
 (1 1
    (:REWRITE ABNF::TREEP-WHEN-PARSE-TREEP))
 (1 1
    (:REWRITE ABNF::TREEP-WHEN-IN-TREE-SETP-BINDS-FREE-X))
 (1 1
    (:REWRITE
         ABNF::TREE-NONLEAF-OF-TREE-LIST-LIST-FIX-BRANCHES-NORMALIZE-CONST))
 (1 1
    (:REWRITE
         ABNF::TREE-NONLEAF-OF-MAYBE-RULENAME-FIX-RULENAME?-NORMALIZE-CONST))
 (1 1
    (:REWRITE ABNF::TREE-LIST-LIST->STRING-WHEN-ATOM))
 (1 1
    (:REWRITE JAVA::ABNF-TREEP-WHEN-ABNF-TREE-WITH-ROOT-P)))
(JAVA::GRAMMAR-JKEYWORDP-WHEN-JKEYWORDP)
(JAVA::LEMMA
 (89917 2770
        (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (77461 4932
        (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (43583 35392 (:REWRITE DEFAULT-CDR))
 (36578 2190 (:DEFINITION INTEGER-LISTP))
 (35826 28931 (:REWRITE DEFAULT-CAR))
 (28931 28931 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (16542
     16542
     (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV))
 (13254
  13254
  (:REWRITE
     CDR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-TRUE-LIST-LIST-EQUIV))
 (10326 5990
        (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (9394 671
       (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (6271 6271
       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                 . 2))
 (6271 6271
       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                 . 1))
 (6271 6271 (:REWRITE CONSP-BY-LEN))
 (4697 671 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (3588 3588 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (3468 510
       (:REWRITE ABNF::TREEP-OF-CAR-WHEN-TREE-LISTP))
 (1959 687 (:REWRITE LEN-WHEN-ATOM))
 (1914 423
       (:REWRITE ABNF::MAYBE-RULENAMEP-WHEN-RULENAMEP))
 (1740 460 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (1538 1538
       (:REWRITE ABNF::TREE-LISTP-WHEN-SUBSETP-EQUAL))
 (1538 1538
       (:REWRITE ABNF::TREE-LISTP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-LISTP))
 (1439 1439 (:REWRITE CONSP-OF-CDDR-BY-LEN))
 (1364 1364
       (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (1364 1364
       (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (1364 1364 (:LINEAR LEN-WHEN-PREFIXP))
 (1342 1342
       (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (1342 671
       (:REWRITE ABNF::SETP-WHEN-TREE-SETP))
 (1342 671
       (:REWRITE ABNF::SETP-WHEN-RULENAME-SETP))
 (1342 671 (:REWRITE SET::SETP-WHEN-NAT-SETP))
 (1342 671
       (:REWRITE SET::SETP-WHEN-INTEGER-SETP))
 (1342 671 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (1236 1236
       (:REWRITE ABNF::TREEP-WHEN-MEMBER-EQUAL-OF-TREE-LISTP))
 (1082 219
       (:REWRITE ABNF::RULENAMEP-WHEN-MAYBE-RULENAMEP))
 (1020 306
       (:REWRITE ABNF::TREE-LISTP-OF-CAR-WHEN-TREE-LIST-LISTP))
 (1020 102
       (:REWRITE NAT-LIST-FIX-WHEN-NAT-LISTP))
 (942 942
      (:REWRITE ABNF::TREE-LIST-LISTP-WHEN-SUBSETP-EQUAL))
 (918 102
      (:REWRITE
           ABNF::TREE-MATCH-ELEMENT-P-OF-CAR-WHEN-TREE-LIST-MATCH-ELEMENT-P))
 (778
  778
  (:REWRITE
    ABNF::NATS-MATCH-SENSITIVE-CHARS-P-OF-NAT-LIST-FIX-NATS-NORMALIZE-CONST))
 (778
  778
  (:REWRITE
   ABNF::NATS-MATCH-SENSITIVE-CHARS-P-OF-MAKE-CHARACTER-LIST-CHARS-NORMALIZE-CONST))
 (769 769
      (:REWRITE JAVA::ABNF-TREE-LISTP-WHEN-ABNF-TREE-LIST-WITH-ROOT-P))
 (756 756 (:REWRITE CONSP-OF-CDDDR-BY-LEN))
 (682 682 (:LINEAR INDEX-OF-<-LEN))
 (671 671
      (:TYPE-PRESCRIPTION ABNF::TREE-SETP))
 (671 671
      (:TYPE-PRESCRIPTION ABNF::RULENAME-SETP))
 (671 671 (:TYPE-PRESCRIPTION SET::NAT-SETP))
 (671 671
      (:TYPE-PRESCRIPTION SET::INTEGER-SETP))
 (671 671
      (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (671 671
      (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (671 671
      (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (671 671
      (:REWRITE JAVA::TRUE-LISTP-WHEN-ABNF-TREE-LIST-WITH-ROOT-P))
 (671 671 (:REWRITE SET::IN-SET))
 (669 669
      (:REWRITE ABNF::TREEP-WHEN-PARSE-TREEP))
 (669 669
      (:REWRITE ABNF::TREEP-WHEN-IN-TREE-SETP-BINDS-FREE-X))
 (669 669
      (:REWRITE JAVA::ABNF-TREEP-WHEN-ABNF-TREE-WITH-ROOT-P))
 (640 640
      (:TYPE-PRESCRIPTION ABNF::RULENAMEP))
 (580 580 (:REWRITE DEFAULT-<-2))
 (580 580 (:REWRITE DEFAULT-<-1))
 (580 580
      (:REWRITE CDR-OF-NAT-LIST-FIX-X-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV))
 (580 580
      (:REWRITE CAR-OF-NAT-LIST-FIX-X-NORMALIZE-CONST-UNDER-NAT-EQUIV))
 (580 580
      (:REWRITE CAR-OF-INTEGER-LIST-FIX-X-NORMALIZE-CONST-UNDER-INT-EQUIV))
 (578
     578
     (:REWRITE ABNF::NAT-MATCH-SENSITIVE-CHAR-P-OF-NFIX-NAT-NORMALIZE-CONST))
 (578
     578
     (:REWRITE
          ABNF::NAT-MATCH-SENSITIVE-CHAR-P-OF-CHAR-FIX-CHAR-NORMALIZE-CONST))
 (512 512
      (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-SUBSETP-EQUAL))
 (460 460
      (:REWRITE NAT-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (319 319
      (:REWRITE ABNF::TREE-KIND$INLINE-OF-TREE-FIX-X-NORMALIZE-CONST))
 (278 256
      (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-NOT-CONSP))
 (278 256
      (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-ATOM))
 (219 219
      (:REWRITE ABNF::RULENAMEP-WHEN-IN-RULENAME-SETP-BINDS-FREE-X))
 (206
  206
  (:REWRITE
   ABNF::TREE-MATCH-ELEMENT-P-WHEN-MEMBER-EQUAL-OF-TREE-LIST-MATCH-ELEMENT-P))
 (206 206
      (:REWRITE ABNF::TREE->STRING-OF-TREE-FIX-TREE-NORMALIZE-CONST))
 (204 204
      (:TYPE-PRESCRIPTION ABNF::TREE-LIST-MATCH-ELEMENT-P))
 (204 204
      (:REWRITE ABNF::TREE-LIST-MATCH-ELEMENT-P-WHEN-SUBSETP-EQUAL))
 (204
  204
  (:REWRITE
   ABNF::TREE-LIST-LIST-MATCH-CONCATENATION-P-OF-TREE-LIST-LIST-FIX-TREESS-NORMALIZE-CONST))
 (204
  204
  (:REWRITE
   ABNF::TREE-LIST-LIST-MATCH-CONCATENATION-P-OF-RULELIST-FIX-RULES-NORMALIZE-CONST))
 (204
  204
  (:REWRITE
   ABNF::TREE-LIST-LIST-MATCH-CONCATENATION-P-OF-CONCATENATION-FIX-CONCATENATION-NORMALIZE-CONST))
 (203
  203
  (:REWRITE
   ABNF::TREE-LIST-LIST-TERMINATEDP-OF-TREE-LIST-LIST-FIX-TREESS-NORMALIZE-CONST))
 (202 202
      (:REWRITE CAR-OF-BOOLEAN-LIST-FIX-X-NORMALIZE-CONST-UNDER-IFF))
 (108
     108
     (:REWRITE
          ABNF::TREE-TERMINATEDP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-TERMINATEDP))
 (105
  105
  (:REWRITE
   ABNF::TREE-LIST-LIST-MATCH-ALTERNATION-P-OF-TREE-LIST-LIST-FIX-TREESS-NORMALIZE-CONST))
 (105
  105
  (:REWRITE
   ABNF::TREE-LIST-LIST-MATCH-ALTERNATION-P-OF-RULELIST-FIX-RULES-NORMALIZE-CONST))
 (105
  105
  (:REWRITE
   ABNF::TREE-LIST-LIST-MATCH-ALTERNATION-P-OF-ALTERNATION-FIX-ALTERNATION-NORMALIZE-CONST))
 (103 103
      (:REWRITE ABNF::TREE-MATCH-ELEMENT-P-OF-TREE-FIX-TREE-NORMALIZE-CONST))
 (103 103
      (:REWRITE
           ABNF::TREE-MATCH-ELEMENT-P-OF-RULELIST-FIX-RULES-NORMALIZE-CONST))
 (103
     103
     (:REWRITE
          ABNF::TREE-MATCH-ELEMENT-P-OF-ELEMENT-FIX-ELEMENT-NORMALIZE-CONST))
 (102
     102
     (:REWRITE ABNF::TREE-MATCH-CHAR-VAL-P-OF-TREE-FIX-TREE-NORMALIZE-CONST))
 (102
  102
  (:REWRITE
       ABNF::TREE-MATCH-CHAR-VAL-P-OF-CHAR-VAL-FIX-CHAR-VAL-NORMALIZE-CONST))
 (102
  102
  (:REWRITE
   ABNF::TREE-LIST-MATCH-REPETITION-P-OF-TREE-LIST-FIX-TREES-NORMALIZE-CONST))
 (102
  102
  (:REWRITE
   ABNF::TREE-LIST-MATCH-REPETITION-P-OF-RULELIST-FIX-RULES-NORMALIZE-CONST))
 (102
  102
  (:REWRITE
   ABNF::TREE-LIST-MATCH-REPETITION-P-OF-REPETITION-FIX-REPETITION-NORMALIZE-CONST))
 (102 102
      (:REWRITE ABNF::TREE-LIST-MATCH-ELEMENT-P-WHEN-NOT-CONSP))
 (102
  102
  (:REWRITE
     ABNF::TREE-LIST-MATCH-ELEMENT-P-OF-TREE-LIST-FIX-TREES-NORMALIZE-CONST))
 (102
  102
  (:REWRITE
      ABNF::TREE-LIST-MATCH-ELEMENT-P-OF-RULELIST-FIX-RULES-NORMALIZE-CONST))
 (102
  102
  (:REWRITE
     ABNF::TREE-LIST-MATCH-ELEMENT-P-OF-ELEMENT-FIX-ELEMENT-NORMALIZE-CONST))
 (102
    102
    (:REWRITE ABNF::TREE-LEAFTERM->GET$INLINE-OF-TREE-FIX-X-NORMALIZE-CONST))
 (102
  102
  (:REWRITE
   ABNF::CDR-OF-TREE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-TREE-LIST-LIST-EQUIV))
 (102
  102
  (:REWRITE
    ABNF::CAR-OF-TREE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-TREE-LIST-EQUIV))
 (102
    102
    (:REWRITE ABNF::CAR-OF-TREE-LIST-FIX-X-NORMALIZE-CONST-UNDER-TREE-EQUIV))
 (56 56
     (:REWRITE
          ABNF::TREE-NONLEAF->BRANCHES$INLINE-OF-TREE-FIX-X-NORMALIZE-CONST))
 (54 54
     (:REWRITE ABNF::TREE-TERMINATEDP-OF-TREE-FIX-TREE-NORMALIZE-CONST))
 (54 54
     (:REWRITE ABNF::MAYBE-RULENAME-FIX-WHEN-NONE))
 (52
    52
    (:REWRITE
         CDR-OF-BOOLEAN-LIST-FIX-X-NORMALIZE-CONST-UNDER-BOOLEAN-LIST-EQUIV))
 (24 4
     (:REWRITE ABNF::TREE-LIST-LIST-FIX-UNDER-IFF))
 (16 16
     (:TYPE-PRESCRIPTION ABNF::TREE-LIST-LIST-FIX$INLINE))
 (8 4
    (:REWRITE ABNF::TREE-LIST-LISTP-OF-CDR-WHEN-TREE-LIST-LISTP))
 (6
  6
  (:REWRITE
   ABNF::NATS-MATCH-INSENSITIVE-CHARS-P-OF-NAT-LIST-FIX-NATS-NORMALIZE-CONST))
 (6
  6
  (:REWRITE
   ABNF::NATS-MATCH-INSENSITIVE-CHARS-P-OF-MAKE-CHARACTER-LIST-CHARS-NORMALIZE-CONST))
 (3 3
    (:REWRITE
         ABNF::TREE-NONLEAF->RULENAME?$INLINE-OF-TREE-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE ABNF::TREE-LEAFRULE->GET$INLINE-OF-TREE-FIX-X-NORMALIZE-CONST))
 (2
   2
   (:REWRITE ABNF::NAT-MATCH-INSENSITIVE-CHAR-P-OF-NFIX-NAT-NORMALIZE-CONST))
 (2
  2
  (:REWRITE
       ABNF::NAT-MATCH-INSENSITIVE-CHAR-P-OF-CHAR-FIX-CHAR-NORMALIZE-CONST)))
(JAVA::JKEYWORDP-WHEN-GRAMMAR-JKEYWORDP
 (6
  6
  (:REWRITE
   JAVA::ABNF-TREE-WITH-ROOT-P-WHEN-MEMBER-EQUAL-OF-ABNF-TREE-LIST-WITH-ROOT-P))
 (3 3
    (:REWRITE ABNF::TREE->STRING-OF-TREE-FIX-TREE-NORMALIZE-CONST))
 (3 3
    (:REWRITE
         JAVA::ABNF-TREE-WITH-ROOT-P-OF-STR-FIX-RULENAME-NORMALIZE-CONST)))
(JAVA::JKEYWORDP-IS-GRAMMAR-JKEYWORDP)
