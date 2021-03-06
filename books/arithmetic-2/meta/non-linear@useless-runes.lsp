(*-PRESERVES-<=-1 (5 5 (:REWRITE DEFAULT-<-2))
                  (5 5 (:REWRITE DEFAULT-<-1))
                  (2 2 (:REWRITE DEFAULT-*-2))
                  (2 2 (:REWRITE DEFAULT-*-1))
                  (1 1 (:REWRITE HELPER-6)))
(*-PRESERVES-<=-2 (5 5 (:REWRITE DEFAULT-<-2))
                  (5 5 (:REWRITE DEFAULT-<-1))
                  (4 4 (:REWRITE DEFAULT-*-2))
                  (4 4 (:REWRITE DEFAULT-*-1))
                  (1 1 (:REWRITE HELPER-6A)))
(*-PRESERVES-<-1 (5 5 (:REWRITE DEFAULT-<-2))
                 (5 5 (:REWRITE DEFAULT-<-1))
                 (2 2 (:REWRITE DEFAULT-*-2))
                 (2 2 (:REWRITE DEFAULT-*-1))
                 (2 2 (:LINEAR *-PRESERVES-<=-2))
                 (2 2 (:LINEAR *-PRESERVES-<=-1)))
(*-PRESERVES-<-2 (6 6 (:REWRITE DEFAULT-<-2))
                 (6 6 (:REWRITE DEFAULT-<-1))
                 (5 5 (:REWRITE DEFAULT-*-2))
                 (5 5 (:REWRITE DEFAULT-*-1))
                 (4 4 (:LINEAR *-PRESERVES-<=-1)))
(*-PRESERVES-<=-FOR-NONNEGATIVES (6 6 (:REWRITE DEFAULT-*-2))
                                 (6 6 (:REWRITE DEFAULT-*-1))
                                 (4 4 (:LINEAR *-PRESERVES-<-2))
                                 (4 4 (:LINEAR *-PRESERVES-<-1)))
(*-PRESERVES-<-FOR-NONNEGATIVES (10 10 (:REWRITE DEFAULT-*-2))
                                (10 10 (:REWRITE DEFAULT-*-1))
                                (8 8
                                   (:LINEAR *-PRESERVES-<=-FOR-NONNEGATIVES))
                                (2 2 (:LINEAR *-PRESERVES-<=-2))
                                (2 2 (:LINEAR *-PRESERVES-<=-1)))
(*-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-1
     (7 7 (:REWRITE DEFAULT-*-2))
     (7 7 (:REWRITE DEFAULT-*-1))
     (4 4
        (:LINEAR *-PRESERVES-<=-FOR-NONNEGATIVES))
     (2 2 (:LINEAR *-PRESERVES-<=-2))
     (2 2 (:LINEAR *-PRESERVES-<-1)))
(*-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-2
     (9 9 (:REWRITE DEFAULT-*-2))
     (9 9 (:REWRITE DEFAULT-*-1))
     (4 4
        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-1))
     (4 4
        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES))
     (4 4 (:LINEAR *-PRESERVES-<-2))
     (2 2 (:LINEAR *-PRESERVES-<=-1)))
(*-WEAKLY-MONOTONIC (29 29
                        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                    (28 19 (:REWRITE DEFAULT-<-1))
                    (25 19 (:REWRITE DEFAULT-<-2))
                    (24 14 (:REWRITE DEFAULT-*-2))
                    (18 14 (:REWRITE DEFAULT-*-1))
                    (15 6
                        (:LINEAR *-PRESERVES-<=-FOR-NONNEGATIVES))
                    (6 6
                       (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-2))
                    (6 6
                       (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-1))
                    (6 6
                       (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES))
                    (4 4 (:REWRITE <-*-LEFT-CANCEL)))
(*-STRONGLY-MONOTONIC
     (34 23 (:REWRITE DEFAULT-<-1))
     (33 33
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (31 23 (:REWRITE DEFAULT-<-2))
     (24 14 (:REWRITE DEFAULT-*-2))
     (18 14 (:REWRITE DEFAULT-*-1))
     (15 6
         (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES))
     (6 6 (:LINEAR *-WEAKLY-MONOTONIC . 2))
     (6 6 (:LINEAR *-WEAKLY-MONOTONIC . 1))
     (6 6
        (:LINEAR *-PRESERVES-<=-FOR-NONNEGATIVES))
     (6 6
        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-2))
     (6 6
        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-1)))
(*-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
     (30 30
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (28 20 (:REWRITE DEFAULT-<-2))
     (28 20 (:REWRITE DEFAULT-<-1))
     (24 14 (:REWRITE DEFAULT-*-2))
     (18 14 (:REWRITE DEFAULT-*-1))
     (6 6 (:LINEAR *-WEAKLY-MONOTONIC . 2))
     (6 6 (:LINEAR *-WEAKLY-MONOTONIC . 1))
     (6 6 (:LINEAR *-STRONGLY-MONOTONIC . 2))
     (6 6 (:LINEAR *-STRONGLY-MONOTONIC . 1))
     (6 6
        (:LINEAR *-PRESERVES-<=-FOR-NONNEGATIVES))
     (6 6
        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-2))
     (6 6
        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-1))
     (6 6
        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES)))
(*-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
     (30 30
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (28 20 (:REWRITE DEFAULT-<-2))
     (28 20 (:REWRITE DEFAULT-<-1))
     (24 14 (:REWRITE DEFAULT-*-2))
     (18 14 (:REWRITE DEFAULT-*-1))
     (6 6
        (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                 . 2))
     (6 6
        (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                 . 1))
     (6 6 (:LINEAR *-WEAKLY-MONOTONIC . 2))
     (6 6 (:LINEAR *-WEAKLY-MONOTONIC . 1))
     (6 6 (:LINEAR *-STRONGLY-MONOTONIC . 2))
     (6 6 (:LINEAR *-STRONGLY-MONOTONIC . 1))
     (6 6
        (:LINEAR *-PRESERVES-<=-FOR-NONNEGATIVES))
     (6 6
        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-2))
     (6 6
        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-1))
     (6 6
        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES)))
(/-WEAKLY-MONOTONIC (8 8 (:REWRITE DEFAULT-<-2))
                    (8 8 (:REWRITE DEFAULT-<-1))
                    (4 4 (:REWRITE DEFAULT-*-2))
                    (4 4 (:REWRITE DEFAULT-*-1))
                    (2 2 (:REWRITE DEFAULT-UNARY-/)))
(/-STRONGLY-MONOTONIC (12 12 (:REWRITE DEFAULT-<-2))
                      (12 12 (:REWRITE DEFAULT-<-1))
                      (4 4 (:REWRITE DEFAULT-*-2))
                      (4 4 (:REWRITE DEFAULT-*-1))
                      (2 2 (:REWRITE DEFAULT-UNARY-/))
                      (2 2 (:LINEAR /-WEAKLY-MONOTONIC)))
(X*Y>1-POSITIVE)
(X*Y>1-POSITIVE-STRONGER
     (9 9 (:REWRITE DEFAULT-<-2))
     (9 9 (:REWRITE DEFAULT-<-1))
     (6 2 (:REWRITE X*Y>1-POSITIVE))
     (3 1 (:LINEAR X*Y>1-POSITIVE))
     (2 2 (:REWRITE DEFAULT-*-2))
     (2 2 (:REWRITE DEFAULT-*-1))
     (2 2
        (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                 . 2))
     (2 2
        (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                 . 1))
     (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 2))
     (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 1))
     (2 2
        (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                 . 2))
     (2 2
        (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                 . 1))
     (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 2))
     (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 1))
     (2 2
        (:LINEAR *-PRESERVES-<=-FOR-NONNEGATIVES))
     (2 2
        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-2))
     (2 2
        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-1))
     (2 2
        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES)))
(X*Y>=1-POSITIVE)
(X*Y>1-NEGATIVE)
(X*Y>=1-NEGATIVE)
(RATIO-THEORY-OF-1-A (15 15 (:REWRITE DEFAULT-<-2))
                     (15 15 (:REWRITE DEFAULT-<-1))
                     (9 9 (:REWRITE DEFAULT-*-2))
                     (9 9 (:REWRITE DEFAULT-*-1))
                     (6 2 (:LINEAR X*Y>=1-POSITIVE))
                     (6 2 (:LINEAR X*Y>1-POSITIVE))
                     (4 4
                        (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 2))
                     (4 4
                        (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 1))
                     (4 4 (:LINEAR *-WEAKLY-MONOTONIC . 1))
                     (4 4
                        (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 2))
                     (4 4
                        (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 1))
                     (4 4 (:LINEAR *-STRONGLY-MONOTONIC . 1))
                     (4 4
                        (:LINEAR *-PRESERVES-<=-FOR-NONNEGATIVES))
                     (4 4
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-2))
                     (4 4
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-1))
                     (4 4
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES))
                     (3 1 (:REWRITE X*Y>1-POSITIVE))
                     (2 2 (:REWRITE DEFAULT-UNARY-/)))
(RATIO-THEORY-OF-1-B (14 14 (:REWRITE DEFAULT-<-2))
                     (14 14 (:REWRITE DEFAULT-<-1))
                     (12 12 (:REWRITE DEFAULT-*-2))
                     (12 12 (:REWRITE DEFAULT-*-1))
                     (6 6 (:REWRITE DEFAULT-UNARY-/))
                     (6 2 (:LINEAR X*Y>=1-POSITIVE))
                     (6 2 (:LINEAR X*Y>1-POSITIVE))
                     (4 4
                        (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 2))
                     (4 4
                        (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 1))
                     (4 4 (:LINEAR *-WEAKLY-MONOTONIC . 1))
                     (4 4
                        (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 2))
                     (4 4
                        (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 1))
                     (4 4 (:LINEAR *-STRONGLY-MONOTONIC . 1))
                     (4 4
                        (:LINEAR *-PRESERVES-<=-FOR-NONNEGATIVES))
                     (4 4
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-2))
                     (4 4
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-1))
                     (4 4
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES))
                     (3 1 (:REWRITE X*Y>=1-POSITIVE)))
(RATIO-THEORY-OF-1-C (57 57 (:REWRITE DEFAULT-*-2))
                     (57 57 (:REWRITE DEFAULT-*-1))
                     (33 33 (:REWRITE DEFAULT-<-2))
                     (33 33 (:REWRITE DEFAULT-<-1))
                     (30 5 (:LINEAR X*Y>=1-POSITIVE))
                     (30 5 (:LINEAR X*Y>1-POSITIVE))
                     (20 8 (:LINEAR RATIO-THEORY-OF-1-B))
                     (14 14 (:REWRITE DEFAULT-UNARY-/))
                     (11 1 (:REWRITE NORMALIZE-<-/-TO-*-2))
                     (10 10
                         (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                  . 2))
                     (10 10
                         (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                  . 1))
                     (10 10
                         (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                  . 2))
                     (10 10
                         (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                  . 1))
                     (10 10
                         (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-1))
                     (10 10
                         (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES))
                     (6 6 (:LINEAR /-STRONGLY-MONOTONIC))
                     (3 1 (:REWRITE X*Y>=1-POSITIVE)))
(RATIO-THEORY-OF-1-D (127 127 (:REWRITE DEFAULT-*-2))
                     (127 127 (:REWRITE DEFAULT-*-1))
                     (60 10 (:LINEAR X*Y>=1-POSITIVE))
                     (60 10 (:LINEAR X*Y>1-POSITIVE))
                     (50 50 (:REWRITE DEFAULT-<-2))
                     (50 50 (:REWRITE DEFAULT-<-1))
                     (44 44 (:REWRITE DEFAULT-UNARY-/))
                     (22 2 (:REWRITE NORMALIZE-<-/-TO-*-2))
                     (20 20
                         (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                  . 2))
                     (20 20
                         (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                  . 1))
                     (20 20 (:LINEAR *-WEAKLY-MONOTONIC . 2))
                     (20 20 (:LINEAR *-WEAKLY-MONOTONIC . 1))
                     (20 20
                         (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                  . 2))
                     (20 20
                         (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                  . 1))
                     (20 20
                         (:LINEAR *-PRESERVES-<=-FOR-NONNEGATIVES))
                     (20 20
                         (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-2))
                     (20 20
                         (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-1))
                     (12 12 (:LINEAR /-WEAKLY-MONOTONIC))
                     (3 1 (:REWRITE X*Y>1-POSITIVE)))
(RATIO-THEORY-OF-1-E (14 14 (:REWRITE DEFAULT-<-2))
                     (14 14 (:REWRITE DEFAULT-<-1))
                     (10 6 (:LINEAR RATIO-THEORY-OF-1-C))
                     (9 9 (:REWRITE DEFAULT-*-2))
                     (9 9 (:REWRITE DEFAULT-*-1))
                     (7 3 (:LINEAR X*Y>=1-POSITIVE))
                     (7 3 (:LINEAR X*Y>1-POSITIVE))
                     (6 6 (:LINEAR RATIO-THEORY-OF-1-D))
                     (6 6 (:LINEAR RATIO-THEORY-OF-1-B))
                     (6 6 (:LINEAR RATIO-THEORY-OF-1-A))
                     (6 6
                        (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 1))
                     (6 6 (:LINEAR *-WEAKLY-MONOTONIC . 2))
                     (6 6 (:LINEAR *-WEAKLY-MONOTONIC . 1))
                     (6 6
                        (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 1))
                     (6 6 (:LINEAR *-STRONGLY-MONOTONIC . 2))
                     (6 6 (:LINEAR *-STRONGLY-MONOTONIC . 1))
                     (6 6
                        (:LINEAR *-PRESERVES-<=-FOR-NONNEGATIVES))
                     (6 6
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-2))
                     (6 6
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-1))
                     (6 6
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES))
                     (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
                     (2 2 (:REWRITE DEFAULT-UNARY-/)))
(RATIO-THEORY-OF-1-F (11 11 (:REWRITE DEFAULT-<-2))
                     (11 11 (:REWRITE DEFAULT-<-1))
                     (4 4 (:REWRITE DEFAULT-*-2))
                     (4 4 (:REWRITE DEFAULT-*-1))
                     (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
                     (2 2 (:REWRITE DEFAULT-UNARY-/)))
(RATIO-THEORY-OF-1-G (8 2 (:LINEAR RATIO-THEORY-OF-1-E))
                     (4 4 (:REWRITE DEFAULT-<-2))
                     (4 4 (:REWRITE DEFAULT-<-1))
                     (3 3 (:REWRITE DEFAULT-*-2))
                     (3 3 (:REWRITE DEFAULT-*-1))
                     (3 1 (:LINEAR X*Y>=1-POSITIVE))
                     (3 1 (:LINEAR X*Y>1-POSITIVE))
                     (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-F))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-D))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-C))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-B))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-A))
                     (2 2
                        (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 1)))
(RATIO-THEORY-OF-1-H (8 2 (:LINEAR RATIO-THEORY-OF-1-F))
                     (4 4 (:REWRITE DEFAULT-<-2))
                     (4 4 (:REWRITE DEFAULT-<-1))
                     (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
                     (3 3 (:REWRITE DEFAULT-*-2))
                     (3 3 (:REWRITE DEFAULT-*-1))
                     (3 1 (:LINEAR X*Y>=1-POSITIVE))
                     (3 1 (:LINEAR X*Y>1-POSITIVE))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-E))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-D))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-C))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-B))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-A))
                     (1 1 (:REWRITE DEFAULT-UNARY-/)))
(RATIO-THEORY-OF-1-I (44 44 (:REWRITE DEFAULT-<-2))
                     (44 44 (:REWRITE DEFAULT-<-1))
                     (30 10 (:LINEAR RATIO-THEORY-OF-1-B))
                     (24 24 (:REWRITE DEFAULT-*-2))
                     (24 24 (:REWRITE DEFAULT-*-1))
                     (18 10 (:LINEAR RATIO-THEORY-OF-1-F))
                     (18 10 (:LINEAR RATIO-THEORY-OF-1-E))
                     (18 10 (:LINEAR RATIO-THEORY-OF-1-D))
                     (13 13 (:REWRITE DEFAULT-UNARY-/))
                     (11 5 (:LINEAR X*Y>=1-POSITIVE))
                     (11 5 (:LINEAR X*Y>1-POSITIVE))
                     (10 10
                         (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                  . 2))
                     (10 10
                         (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                  . 1))
                     (10 10 (:LINEAR *-WEAKLY-MONOTONIC . 1))
                     (10 10
                         (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                  . 2))
                     (10 10
                         (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                  . 1))
                     (10 10 (:LINEAR *-STRONGLY-MONOTONIC . 1))
                     (10 10
                         (:LINEAR *-PRESERVES-<=-FOR-NONNEGATIVES))
                     (10 10
                         (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-2))
                     (10 10
                         (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-1))
                     (10 10
                         (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES))
                     (9 3 (:REWRITE <-0-MINUS))
                     (8 5 (:LINEAR RATIO-THEORY-OF-1-G))
                     (7 7 (:REWRITE DEFAULT-UNARY-MINUS))
                     (5 5 (:LINEAR RATIO-THEORY-OF-1-H)))
(RATIO-THEORY-OF-1-J (16 16 (:REWRITE DEFAULT-<-2))
                     (16 16 (:REWRITE DEFAULT-<-1))
                     (6 6 (:REWRITE DEFAULT-*-2))
                     (6 6 (:REWRITE DEFAULT-*-1))
                     (6 2 (:LINEAR RATIO-THEORY-OF-1-F))
                     (6 2 (:LINEAR RATIO-THEORY-OF-1-E))
                     (6 2 (:LINEAR RATIO-THEORY-OF-1-B))
                     (6 2 (:LINEAR RATIO-THEORY-OF-1-A))
                     (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
                     (4 4 (:REWRITE DEFAULT-UNARY-/))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-D))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-C))
                     (2 2
                        (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 2))
                     (2 2
                        (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 1))
                     (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 1))
                     (2 2
                        (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 2))
                     (2 2
                        (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 1))
                     (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 2))
                     (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 1))
                     (2 2
                        (:LINEAR *-PRESERVES-<=-FOR-NONNEGATIVES))
                     (2 2
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-2))
                     (2 2
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-1))
                     (2 2
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES))
                     (1 1 (:LINEAR X*Y>=1-POSITIVE))
                     (1 1 (:LINEAR X*Y>1-POSITIVE))
                     (1 1 (:LINEAR RATIO-THEORY-OF-1-H))
                     (1 1 (:LINEAR RATIO-THEORY-OF-1-G)))
(RATIO-THEORY-OF-1-K (10 10 (:REWRITE DEFAULT-*-2))
                     (10 10 (:REWRITE DEFAULT-*-1))
                     (10 4 (:LINEAR RATIO-THEORY-OF-1-I))
                     (8 8 (:REWRITE DEFAULT-UNARY-/))
                     (8 8 (:REWRITE DEFAULT-<-2))
                     (8 8 (:REWRITE DEFAULT-<-1))
                     (8 4 (:LINEAR RATIO-THEORY-OF-1-D))
                     (8 4 (:LINEAR RATIO-THEORY-OF-1-B))
                     (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
                     (4 4 (:LINEAR RATIO-THEORY-OF-1-J))
                     (4 4 (:LINEAR RATIO-THEORY-OF-1-F))
                     (4 4 (:LINEAR RATIO-THEORY-OF-1-E))
                     (4 4 (:LINEAR /-STRONGLY-MONOTONIC))
                     (4 4
                        (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 2))
                     (4 4
                        (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 2))
                     (4 4
                        (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 1))
                     (4 4 (:LINEAR *-STRONGLY-MONOTONIC . 1))
                     (4 2 (:LINEAR X*Y>=1-POSITIVE))
                     (4 2 (:LINEAR X*Y>1-POSITIVE))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-H))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-G))
                     (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 1))
                     (2 2
                        (:LINEAR *-PRESERVES-<=-FOR-NONNEGATIVES))
                     (2 2
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-2))
                     (2 2
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-1))
                     (2 2
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES)))
(RATIO-THEORY-OF-1-L (18 18 (:REWRITE DEFAULT-<-2))
                     (18 18 (:REWRITE DEFAULT-<-1))
                     (8 2 (:LINEAR RATIO-THEORY-OF-1-J))
                     (7 7 (:REWRITE DEFAULT-UNARY-MINUS))
                     (6 6 (:REWRITE DEFAULT-UNARY-/))
                     (6 2 (:LINEAR RATIO-THEORY-OF-1-F))
                     (6 2 (:LINEAR RATIO-THEORY-OF-1-E))
                     (6 2 (:LINEAR RATIO-THEORY-OF-1-D))
                     (6 2 (:LINEAR RATIO-THEORY-OF-1-C))
                     (6 2 (:LINEAR RATIO-THEORY-OF-1-B))
                     (6 2 (:LINEAR RATIO-THEORY-OF-1-A))
                     (4 4 (:REWRITE DEFAULT-*-2))
                     (4 4 (:REWRITE DEFAULT-*-1))
                     (4 4 (:LINEAR /-WEAKLY-MONOTONIC))
                     (4 2 (:LINEAR *-STRONGLY-MONOTONIC . 1))
                     (3 1 (:LINEAR X*Y>=1-POSITIVE))
                     (3 1 (:LINEAR X*Y>1-POSITIVE))
                     (3 1 (:LINEAR RATIO-THEORY-OF-1-G))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-I))
                     (2 2
                        (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 2))
                     (2 2
                        (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 1))
                     (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 2))
                     (2 2 (:LINEAR *-WEAKLY-MONOTONIC . 1))
                     (2 2
                        (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 2))
                     (2 2 (:LINEAR *-STRONGLY-MONOTONIC . 2))
                     (2 2
                        (:LINEAR *-PRESERVES-<=-FOR-NONNEGATIVES))
                     (2 2
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-2))
                     (2 2
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-1))
                     (2 2
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES))
                     (1 1 (:LINEAR RATIO-THEORY-OF-1-H)))
(RATIO-THEORY-OF-1-M (3 3 (:REWRITE DEFAULT-*-2))
                     (3 3 (:REWRITE DEFAULT-*-1))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-J))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-I))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-F))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-E))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-D))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-C))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-B))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-A))
                     (2 2
                        (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 1))
                     (1 1 (:LINEAR X*Y>=1-POSITIVE))
                     (1 1 (:LINEAR X*Y>1-POSITIVE))
                     (1 1 (:LINEAR RATIO-THEORY-OF-1-L))
                     (1 1 (:LINEAR RATIO-THEORY-OF-1-K))
                     (1 1 (:LINEAR RATIO-THEORY-OF-1-H))
                     (1 1 (:LINEAR RATIO-THEORY-OF-1-G)))
(RATIO-THEORY-OF-1-N (3 3 (:REWRITE DEFAULT-*-2))
                     (3 3 (:REWRITE DEFAULT-*-1))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-J))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-I))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-F))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-E))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-D))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-C))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-B))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-A))
                     (1 1 (:REWRITE DEFAULT-UNARY-/))
                     (1 1 (:LINEAR X*Y>=1-POSITIVE))
                     (1 1 (:LINEAR X*Y>1-POSITIVE))
                     (1 1 (:LINEAR RATIO-THEORY-OF-1-L))
                     (1 1 (:LINEAR RATIO-THEORY-OF-1-K))
                     (1 1 (:LINEAR RATIO-THEORY-OF-1-H))
                     (1 1 (:LINEAR RATIO-THEORY-OF-1-G)))
(RATIO-THEORY-OF-1-O (18 18 (:REWRITE DEFAULT-<-2))
                     (18 18 (:REWRITE DEFAULT-<-1))
                     (10 10 (:REWRITE DEFAULT-*-2))
                     (10 10 (:REWRITE DEFAULT-*-1))
                     (8 4 (:LINEAR RATIO-THEORY-OF-1-F))
                     (8 4 (:LINEAR RATIO-THEORY-OF-1-E))
                     (8 4 (:LINEAR RATIO-THEORY-OF-1-B))
                     (8 4 (:LINEAR RATIO-THEORY-OF-1-A))
                     (4 4 (:LINEAR RATIO-THEORY-OF-1-J))
                     (4 4 (:LINEAR RATIO-THEORY-OF-1-I))
                     (4 4 (:LINEAR RATIO-THEORY-OF-1-D))
                     (4 4 (:LINEAR RATIO-THEORY-OF-1-C))
                     (4 4
                        (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 1))
                     (4 4 (:LINEAR *-WEAKLY-MONOTONIC . 2))
                     (4 4 (:LINEAR *-WEAKLY-MONOTONIC . 1))
                     (4 4
                        (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 1))
                     (4 4 (:LINEAR *-STRONGLY-MONOTONIC . 2))
                     (4 4 (:LINEAR *-STRONGLY-MONOTONIC . 1))
                     (4 4
                        (:LINEAR *-PRESERVES-<=-FOR-NONNEGATIVES))
                     (4 4
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-2))
                     (4 4
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-1))
                     (4 4
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES))
                     (4 2 (:LINEAR RATIO-THEORY-OF-1-N))
                     (4 2 (:LINEAR RATIO-THEORY-OF-1-K))
                     (3 3 (:REWRITE DEFAULT-UNARY-/))
                     (2 2 (:LINEAR X*Y>=1-POSITIVE))
                     (2 2 (:LINEAR X*Y>1-POSITIVE))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-L))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-H))
                     (2 2 (:LINEAR RATIO-THEORY-OF-1-G))
                     (1 1 (:REWRITE X*Y>1-POSITIVE)))
(RATIO-THEORY-OF-1-P (30 30 (:REWRITE DEFAULT-<-2))
                     (30 30 (:REWRITE DEFAULT-<-1))
                     (24 24 (:REWRITE DEFAULT-*-2))
                     (24 24 (:REWRITE DEFAULT-*-1))
                     (16 8 (:LINEAR RATIO-THEORY-OF-1-F))
                     (16 8 (:LINEAR RATIO-THEORY-OF-1-E))
                     (16 8 (:LINEAR RATIO-THEORY-OF-1-B))
                     (16 8 (:LINEAR RATIO-THEORY-OF-1-A))
                     (13 13 (:REWRITE DEFAULT-UNARY-/))
                     (12 4 (:LINEAR RATIO-THEORY-OF-1-N))
                     (8 8 (:LINEAR RATIO-THEORY-OF-1-J))
                     (8 8 (:LINEAR RATIO-THEORY-OF-1-I))
                     (8 8 (:LINEAR RATIO-THEORY-OF-1-D))
                     (8 8 (:LINEAR RATIO-THEORY-OF-1-C))
                     (8 8
                        (:LINEAR *-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 1))
                     (8 8 (:LINEAR *-WEAKLY-MONOTONIC . 2))
                     (8 8 (:LINEAR *-WEAKLY-MONOTONIC . 1))
                     (8 8
                        (:LINEAR *-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER
                                 . 1))
                     (8 8 (:LINEAR *-STRONGLY-MONOTONIC . 2))
                     (8 8 (:LINEAR *-STRONGLY-MONOTONIC . 1))
                     (8 8
                        (:LINEAR *-PRESERVES-<=-FOR-NONNEGATIVES))
                     (8 8
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-2))
                     (8 8
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES-STRONGER-1))
                     (8 8
                        (:LINEAR *-PRESERVES-<-FOR-NONNEGATIVES))
                     (8 4 (:LINEAR RATIO-THEORY-OF-1-K))
                     (4 4 (:LINEAR X*Y>=1-POSITIVE))
                     (4 4 (:LINEAR X*Y>1-POSITIVE))
                     (4 4 (:LINEAR RATIO-THEORY-OF-1-L))
                     (4 4 (:LINEAR RATIO-THEORY-OF-1-H))
                     (4 4 (:LINEAR RATIO-THEORY-OF-1-G))
                     (1 1 (:REWRITE X*Y>=1-POSITIVE)))
