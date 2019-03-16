; Ethereum Library -- Bytes
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/utilities/fixbytes/defbytelist" :dir :system)
(include-book "kestrel/utilities/unsigned-byte-list-fixing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc bytes
  :parents (basics)
  :short "Bytes."
  :long
  (xdoc::toppstring
   "[YP:B] describes @($\\mathbb{O}$) as the set of 8-bit bytes.
    Unless otherwise stated, in the documentation of our Ethereum model,
    the unqualified `byte' denotes an 8-bit byte."))

(fty::defbyte byte
  :size 8
  :pred bytep
  :parents (bytes)
  :short "Fixtype of bytes.")

(defsection byte-fix-ext
  :extension byte-fix

  (defrule natp-of-byte-fix
    (natp (byte-fix x))
    :rule-classes :type-prescription
    :enable byte-fix)

  (defrule byte-fix-upper-bound
    (< (byte-fix x) 256)
    :rule-classes :linear
    :enable (byte-fix bytep))

  (defruled byte-fix-rewrite-unsigned-byte-fix
    (equal (byte-fix x)
           (unsigned-byte-fix 8 x))
    :enable (byte-fix bytep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc byte-arrays
  :parents (basics)
  :short "Byte arrays."
  :long
  (xdoc::toppstring
   "[YP:3] mentions the set @($\\mathbb{B}$) of byte arrays,
    and [YP:(178)] defines it as consisting of all finite sequences of bytes.
    We use true lists of @(see bytes)
    to model byte arrays in our Ethereum model."))

(fty::defbytelist byte-list
  :elt-type byte
  :pred byte-listp
  :parents (byte-arrays)
  :short "Fixtype of byte arrays.")

(defsection byte-listp-ext
  :extension byte-listp

  (defrule nat-listp-when-byte-listp
    (implies (byte-listp bytes)
             (nat-listp bytes))))

(defsection byte-list-fix-ext
  :extension byte-list-fix

  (defrule car-of-byte-list-fix
    (implies (consp x)
             (equal (car (byte-list-fix x))
                    (byte-fix (car x)))))

  (defrule cdr-of-byte-list-fix
    (equal (cdr (byte-list-fix x))
           (byte-list-fix (cdr x))))

  (defruled byte-list-fix-rewrite-unsigned-byte-list-fix
    (equal (byte-list-fix x)
           (unsigned-byte-list-fix 8 x))
    :enable (byte-fix-rewrite-unsigned-byte-fix
             unsigned-byte-list-fix)))
