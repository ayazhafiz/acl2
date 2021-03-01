## a6d46ba59b99e5fb7c6d7f8827b929e761df5b8e

As of this commit, we are now able to prove the following:

```
ACL2 !>(genM '(rev2 len) 6)

Testing 24 conjectures...
10/24...
20/24...

====================

Given the theory (REV2 LEN),
we generated 24 conjectures of bigsize 6 (left=3,right<=3).
We were able to prove 11 conjectures, namely:
((IMPLIES (AND (TRUE-LISTP A)
               (TRUE-LISTP (REV2 A))
               (TRUE-LISTP (LEN A)))
          (EQUAL (REV2 (REV2 A)) (REV2 (LEN A))))
 (IMPLIES (AND (TRUE-LISTP A)
               (TRUE-LISTP (REV2 A)))
          (EQUAL (REV2 (REV2 A)) A))
 (IMPLIES (AND (TRUE-LISTP (LEN A))
               (TRUE-LISTP A)
               (TRUE-LISTP (REV2 A)))
          (EQUAL (REV2 (LEN A)) (REV2 (REV2 A))))
 (IMPLIES (AND (TRUE-LISTP (LEN A))
               (TRUE-LISTP A))
          (EQUAL (REV2 (LEN A)) (LEN (REV2 A))))
 (IMPLIES (TRUE-LISTP (LEN A))
          (EQUAL (REV2 (LEN A)) (LEN (LEN A))))
 (IMPLIES (AND (TRUE-LISTP (LEN A))
               (TRUE-LISTP A))
          (EQUAL (REV2 (LEN A)) (REV2 A)))
 (IMPLIES (TRUE-LISTP (LEN A))
          (EQUAL (REV2 (LEN A)) (LEN A)))
 (IMPLIES (TRUE-LISTP (LEN A))
          (EQUAL (REV2 (LEN A)) A))
 (IMPLIES (AND (TRUE-LISTP A)
               (TRUE-LISTP (LEN A)))
          (EQUAL (LEN (REV2 A)) (REV2 (LEN A))))
 (IMPLIES (TRUE-LISTP A)
          (EQUAL (LEN (REV2 A)) (LEN A)))
 (IMPLIES (TRUE-LISTP (LEN A))
          (EQUAL (LEN (LEN A)) (REV2 (LEN A)))))
```

where `rev2` is defined as

```
(defun rev2 (x)
  (declare (xargs :guard (true-listp x) :VERIFY-GUARDS NIL))
  (if (consp x)
      (append (rev2 (cdr x)) (list (car x)))
      nil))
```

Probably the most interesting/useful theorems are

```
(IMPLIES (AND (TRUE-LISTP A)
              (TRUE-LISTP (REV2 A)))
         (EQUAL (REV2 (REV2 A)) A))

(IMPLIES (TRUE-LISTP A)
         (EQUAL (LEN (REV2 A)) (LEN A)))
```

On the other hand, trying to do this with the theory `'(reverse len)` will
genrate an analogous theorem:

```
(IMPLIES (AND (IF (TRUE-LISTP A)
                  (TRUE-LISTP A)
                  (STRINGP A)))
         (EQUAL (LEN (REVERSE A)) (LEN A)))
```

but fail to prove it, likely because the default theory that we have loaded in
does not have enough supplementary conjectures to immediately prove the
conjecture as true. That is,

```
(defthm my-len-of-rev (IMPLIES (AND (IF (TRUE-LISTP A)
                                        (TRUE-LISTP A)
                                        (STRINGP A)))
                               (EQUAL (LEN (REVERSE A)) (LEN A)))
  :hints (("Goal"
           :in-theory (set-difference-theories
                       (current-theory :here)
                       nil)
           )))
```

fails in the present environment but in an environment with a larger theory,
like on http://new.proofpad.org we have

```
(defthm my-len-of-rev (IMPLIES (AND (IF (TRUE-LISTP A)
                  (TRUE-LISTP A)
                  (STRINGP A)))
                     (EQUAL (LEN (REVERSE A)) (LEN A)))
  :hints (("Goal"
           :in-theory (set-difference-theories
                             (current-theory :here)
                             '(len-of-rev))
)))
```

succeeds immediately. So, the presumption is that we just need the discovery of
more and larger theorems before we can discover things like this more
organically.
