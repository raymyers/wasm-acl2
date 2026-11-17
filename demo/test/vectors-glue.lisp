;;;; demo/test/vectors-glue.lisp: entry points of the W3 vector runner. The
;;;; checks are the ACL2 test books' own CHECK-VECTORS (t3-numerics-3.0) and
;;;; CHECK-SIMD (t3-simd-3.0), extracted by name; this file only turns their
;;;; multiple values into a list for JS. Each test bundle has one of them.
(defpackage "DEMO" (:use "COMMON-LISP"))
(in-package "DEMO")
(defun check-vectors (vs) (multiple-value-list (w3t::check-vectors vs 0 nil)))
(defun check-simd (vs) (multiple-value-list (w3t::check-simd vs 0 nil 0 nil)))
