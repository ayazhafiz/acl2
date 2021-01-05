; Elliptic Curve Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "short-weierstrass")
(include-book "short-weierstrass-validation")

(include-book "secp256k1-domain-parameters")
(include-book "secp256k1-interface")
(include-book "secp256k1-types")

(include-book "secp256k1")
(include-book "secp256k1-attachment")

(include-book "points-fty")

(include-book "bls12-377-domain-parameters")

(include-book "prime-field-squares")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc elliptic-curves
  :parents (crypto::cryptography)
  :short "Elliptic curve cryptography.")

(xdoc::order-subtopics elliptic-curves
  (points
   short-weierstrass
   secp256k1-domain-parameters
   secp256k1-types
   secp256k1
   secp256k1-interface
   secp256k1-attachment
   bls12-377-domain-parameters
   prime-field-squares))
