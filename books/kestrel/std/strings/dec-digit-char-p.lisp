; Standard Strings Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STR")

(include-book "std/strings/charset" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(str::defcharset dec-digit
  (and (standard-char-p x)
       (digit-char-p x)
       t)
  :parents (character-kinds)
  :short "Recognize ASCII decimal digits."
  :long
  (xdoc::topstring
   (xdoc::p
    "The built-in @(tsee digit-char-p)
     has a guard requiring characters that are standard.
     In contrast, this recognizer has guard @('t').")))
