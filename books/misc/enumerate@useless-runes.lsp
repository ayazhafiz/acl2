(ENUMERATE! (10 10 (:REWRITE DEFAULT-+-2))
            (10 10 (:REWRITE DEFAULT-+-1))
            (6 6 (:REWRITE DEFAULT-<-2))
            (6 6 (:REWRITE DEFAULT-<-1))
            (2 2 (:REWRITE DEFAULT-UNARY-MINUS)))
(ENUMERATE (14 14 (:REWRITE DEFAULT-<-2))
           (14 14 (:REWRITE DEFAULT-<-1))
           (6 2 (:REWRITE COMMUTATIVITY-OF-+))
           (4 4 (:REWRITE DEFAULT-+-2))
           (4 4 (:REWRITE DEFAULT-+-1)))
(ENUMERATE-EXPANDER (14 14 (:REWRITE DEFAULT-+-2))
                    (14 14 (:REWRITE DEFAULT-+-1))
                    (11 11 (:REWRITE DEFAULT-<-2))
                    (11 11 (:REWRITE DEFAULT-<-1))
                    (9 3 (:REWRITE FOLD-CONSTS-IN-+)))
