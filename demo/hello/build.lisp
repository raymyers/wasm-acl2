;; Compile demo/hello/hello.lisp to $OUT with the jscl-xc image.
(let ((out (sb-posix:getenv "OUT")) (in (sb-posix:getenv "IN")))
  (let ((*package* (find-package "JSCL-XC")))
    (jscl-xc::compile-application (list in) out)))
