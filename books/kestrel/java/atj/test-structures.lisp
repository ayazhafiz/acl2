; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "../language/primitive-values")

(include-book "types")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-test-structures
  :parents (atj-implementation)
  :short "Structures that store user-specified ATJ tests."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum atj-test-value
  :short "Values used for inputs and outputs in user-specified ATJ tests."
  :long
  (xdoc::topstring
   (xdoc::p
    "The Java methods generated by ATJ manipulate three kinds of values:")
   (xdoc::ol
    (xdoc::li
     "Objects of the AIJ classes that represent ACL2 values,
      e.g. @('Acl2Integer').
      These correspond to the @(':acl2') ATJ "
     (xdoc::seetopic "atj-types" "types")
     ", e.g. @(':ainteger').")
    (xdoc::li
     "Java primitive values,
      which correspond to the ATJ @(':jprim') types.
      These values are used only in the shallow embedding with guards.")
    (xdoc::li
     "Java primitive arrays,
      which correspond to the ATJ @(':jprimarr') types.
      These arrays are only used in the shallow embedding with guards."))
   (xdoc::p
    "Thus, when generating tests for the generated Java methods,
     the input and output values of the tests may be
     of these three different kinds.
     So we introduce a type for these three kinds of values,
     with each of the last two kinds having six sub-kinds each.
     The @(':acl2') values may be anything,
     while the @('j...') values are restricted to (our model of)
     Java primitive values and Java primitive arrays,
     excluding @('float') and @('double') values and arrays,
     because we only have an abstract model of those for now
     and thus ATJ does not support
     the generation of tests involving @('float') and @('double')."))
  (:acl2 ((get acl2::any)))
  (:jboolean ((get boolean-value)))
  (:jchar ((get char-value)))
  (:jbyte ((get byte-value)))
  (:jshort ((get short-value)))
  (:jint ((get int-value)))
  (:jlong ((get long-value)))
  (:jboolean[] ((get boolean-array)))
  (:jchar[] ((get char-array)))
  (:jbyte[] ((get byte-array)))
  (:jshort[] ((get short-array)))
  (:jint[] ((get int-array)))
  (:jlong[] ((get long-array))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-test-value-to-type ((test-value atj-test-value-p))
  :returns (type atj-typep)
  :short "ATJ type of an ATJ test value."
  (atj-test-value-case
   test-value
   :acl2 (atj-type-of-value test-value.get)
   :jboolean (atj-type-jprim (primitive-type-boolean))
   :jchar (atj-type-jprim (primitive-type-char))
   :jbyte (atj-type-jprim (primitive-type-byte))
   :jshort (atj-type-jprim (primitive-type-short))
   :jint (atj-type-jprim (primitive-type-int))
   :jlong (atj-type-jprim (primitive-type-long))
   :jboolean[] (atj-type-jprimarr (primitive-type-boolean))
   :jchar[] (atj-type-jprimarr (primitive-type-char))
   :jbyte[] (atj-type-jprimarr (primitive-type-byte))
   :jshort[] (atj-type-jprimarr (primitive-type-short))
   :jint[] (atj-type-jprimarr (primitive-type-int))
   :jlong[] (atj-type-jprimarr (primitive-type-long)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist atj-test-value-list
  :short "True lists of ATJ test values."
  :elt-type atj-test-value
  :true-listp t
  :elementp-of-nil nil
  :pred atj-test-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-test-values-to-types ((test-values atj-test-value-listp))
  :returns (types atj-type-listp)
  :short "Lift @(tsee atj-test-value-to-type) to lists."
  (cond ((endp test-values) nil)
        (t (cons (atj-test-value-to-type (car test-values))
                 (atj-test-values-to-types (cdr test-values)))))
  :hooks (:fix)
  ///

  (defret len-of-atj-test-values-to-types
    (equal (len types) (len test-values))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-test-value-acl2-list ((values true-listp))
  :returns (test-values atj-test-value-listp)
  :short "Lift @(tsee atj-test-value-acl2) to lists."
  (cond ((endp values) nil)
        (t (cons (atj-test-value-acl2 (car values))
                 (atj-test-value-acl2-list (cdr values))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-test-value-of-type (value (type atj-typep))
  :returns (test-value atj-test-value-p)
  :short "Construct a test value with a given ATJ type."
  (atj-type-case
   type
   :jprim (primitive-type-case
           type.get
           :boolean (if (boolean-value-p value)
                        (atj-test-value-jboolean value)
                      (prog2$ (raise "Internal error: ~
                                        value ~x0 does not match type ~x1."
                                     value type)
                              (ec-call (atj-test-value-fix :irrelevant))))
           :char (if (char-value-p value)
                     (atj-test-value-jchar value)
                   (prog2$ (raise "Internal error: ~
                                     value ~x0 does not match type ~x1."
                                  value type)
                           (ec-call (atj-test-value-fix :irrelevant))))
           :byte (if (byte-value-p value)
                     (atj-test-value-jbyte value)
                   (prog2$ (raise "Internal error: ~
                                     value ~x0 does not match type ~x1."
                                  value type)
                           (ec-call (atj-test-value-fix :irrelevant))))
           :short (if (short-value-p value)
                      (atj-test-value-jshort value)
                    (prog2$ (raise "Internal error: ~
                                      value ~x0 does not match type ~x1."
                                   value type)
                            (ec-call (atj-test-value-fix :irrelevant))))
           :int (if (int-value-p value)
                    (atj-test-value-jint value)
                  (prog2$ (raise "Internal error: ~
                                    value ~x0 does not match type ~x1."
                                 value type)
                          (ec-call (atj-test-value-fix :irrelevant))))
           :long (if (long-value-p value)
                     (atj-test-value-jlong value)
                   (prog2$ (raise "Internal error: ~
                                     value ~x0 does not match type ~x1."
                                  value type)
                           (ec-call (atj-test-value-fix :irrelevant))))
           :float (prog2$ (raise "Internal error: ~
                                    value ~x0 cannot match type ~x1."
                                 value type)
                          (ec-call (atj-test-value-fix :irrelevant)))
           :double (prog2$ (raise "Internal error: ~
                                     value ~x0 cannot match type ~x1."
                                  value type)
                           (ec-call (atj-test-value-fix :irrelevant))))
   :jprimarr (primitive-type-case
              type.comp
              :boolean (if (boolean-array-p value)
                           (atj-test-value-jboolean[] value)
                         (prog2$ (raise "Internal error: ~
                                           value ~x0 does not match type ~x1."
                                        value type)
                                 (ec-call (atj-test-value-fix :irrelevant))))
              :char (if (char-array-p value)
                        (atj-test-value-jchar[] value)
                      (prog2$ (raise "Internal error: ~
                                        value ~x0 does not match type ~x1."
                                     value type)
                              (ec-call (atj-test-value-fix :irrelevant))))
              :byte (if (byte-array-p value)
                        (atj-test-value-jbyte[] value)
                      (prog2$ (raise "Internal error: ~
                                        value ~x0 does not match type ~x1."
                                     value type)
                              (ec-call (atj-test-value-fix :irrelevant))))
              :short (if (short-array-p value)
                         (atj-test-value-jshort[] value)
                       (prog2$ (raise "Internal error: ~
                                         value ~x0 does not match type ~x1."
                                      value type)
                               (ec-call (atj-test-value-fix :irrelevant))))
              :int (if (int-array-p value)
                       (atj-test-value-jint[] value)
                     (prog2$ (raise "Internal error: ~
                                       value ~x0 does not match type ~x1."
                                    value type)
                             (ec-call (atj-test-value-fix :irrelevant))))
              :long (if (long-array-p value)
                        (atj-test-value-jlong[] value)
                      (prog2$ (raise "Internal error: ~
                                        value ~x0 does not match type ~x1."
                                     value type)
                              (ec-call (atj-test-value-fix :irrelevant))))
              :float (prog2$ (raise "Internal error: ~
                                       value ~x0 cannot match type ~x1."
                                    value type)
                             (ec-call (atj-test-value-fix :irrelevant)))
              :double (prog2$ (raise "Internal error: ~
                                         value ~x0 cannot match type ~x1."
                                     value type)
                              (ec-call (atj-test-value-fix :irrelevant))))
   :acl2 (atj-test-value-acl2 value))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-test-values-of-types ((values true-listp)
                                  (types atj-type-listp))
  :guard (= (len values) (len types))
  :returns (test-values atj-test-value-listp)
  :short "Lift @(tsee atj-test-value-of-type) to lists."
  (cond ((endp values) nil)
        (t (cons (atj-test-value-of-type (car values) (car types))
                 (atj-test-values-of-types (cdr values) (cdr types)))))
  :hooks (:fix)
  ///

  (defret len-of-atj-test-values-of-types
    (equal (len test-values)
           (len values))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod atj-test
  :short "Processed user-specified ATJ tests."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each test specified by the @(':tests') input
     must have the form @('(namej termj)'),
     where @('termj') must translate to @('(fn in1 in2 ...)'),
     as explained in the documentation.
     As the @(':tests') input is processed,
     the information about each test is stored
     into an aggregate of this type.
     This aggregate stores
     @('namej'),
     @('fn'),
     the list of inputs derived from @('in1'), @('in2'), etc.,
     and results of the ground call @('(fn in1 in2 ...)').
     The latter list is a singleton for single-valued functions,
     while it consists of two or more values for multi-valued functions."))
  ((name string)
   (function symbol)
   (inputs atj-test-value-list)
   (outputs atj-test-value-list))
  :pred atj-testp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist atj-test-list
  :short "True lists of processed user-specified ATJ tests."
  :elt-type atj-test
  :true-listp t
  :elementp-of-nil nil
  :pred atj-test-listp)
