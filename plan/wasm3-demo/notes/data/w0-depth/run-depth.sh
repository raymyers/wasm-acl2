#!/bin/sh
# W0 item 4: deepest recursion in ACL2 on decode, instantiate and invoke of
# mem1.wat (1 page). From the repo root inside `nix develop`, after
# `make -C translate check-3.0` (certifies gen/wasm-3.0 and t7-lib-3.0).
set -e
D=$(cd "$(dirname "$0")" && pwd)
W=$(mktemp -d)
wat2wasm $D/mem1.wat -o $W/mem1.wasm
cd translate/tests/spec
$ACL2 <<LISP 2>&1 | grep -A4 'W0-\|rror\|debugger'
(ld "t7-lib-3.0.acl2")
(in-package "W3T")
(include-book "t7-lib-3.0")
:q
(load "$D/../w0-slice/extract-slice.lisp")
(load "$D/instrument.lisp")
(in-package "CL-USER")
(defparameter cl-user::*bytes*
  (with-open-file (in "$W/mem1.wasm" :element-type '(unsigned-byte 8))
    (loop for b = (read-byte in nil) while b collect b)))
(defun cl-user::run-all ()
  (let* ((p (w3t::gram/bmodule cl-user::*bytes*)) (m (car p)))
    (w0::report "decode") (w0::reset-counts)
    (multiple-value-bind (st s inst) (w3t::instantiate m (list w3t::*s0* nil nil nil))
      (format t "~&W0-DEPTH instantiate status ~S~%" st)
      (w0::report "instantiate") (w0::reset-counts)
      (multiple-value-bind (r e) (w3t::do-action (list :invoke nil (w3t::str-bytes "f") nil) (list s inst nil nil))
        (declare (ignore e))
        (format t "~&W0-DEPTH invoke f => ~S~%" r)
        (w0::report "invoke")))))
(let ((t0 (get-internal-real-time)))
  (multiple-value-bind (st s inst) (w3t::instantiate (car (w3t::gram/bmodule cl-user::*bytes*)) (list w3t::*s0* nil nil nil))
    (format t "~&W0-DEPTH uninstrumented: status ~S, invoke => ~S, ~,2F s~%" st
            (w3t::do-action (list :invoke nil (w3t::str-bytes "f") nil) (list s inst nil nil))
            (/ (- (get-internal-real-time) t0) internal-time-units-per-second))))
(w0::instrument-books "../../gen/wasm-3.0/wasm3.lisp")
(w0::reset-counts)
(let ((t0 (get-internal-real-time)))
  (cl-user::run-all)
  (format t "~&W0-DEPTH instrumented run ~,2F s~%" (/ (- (get-internal-real-time) t0) internal-time-units-per-second)))
LISP
rm -r "$W"
