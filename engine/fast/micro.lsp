; E7: microbenchmark of the parts of one machine step (1,000,000 calls each).
; From engine/fast inside nix develop: acl2 < micro.lsp | grep MICRO
(ld "cert.acl2")
(include-book "../machine/machine")
(in-package "WE")
:q
(defparameter *redex* '((:const (:i32) 7) (:const (:i32) 2) (:binop (:i32) (:sub))))
(defparameter *z* '(:|%;%| nil nil))
(defmacro bench (name form)
  `(let ((t0 (get-internal-real-time)))
     (dotimes (i 1000000) ,form)
     (format t "~&MICRO ~a: ~,3f us per call~%" ,name
             (/ (- (get-internal-real-time) t0) (/ internal-time-units-per-second 1000000.0) 1000000))))
(bench "$binop_ i32 sub" (w3t::$binop_ '(:i32) '(:sub) 7 2))
(bench "rule binop-val" (w3t::step_pure/r-binop-val *redex*))
(bench "apply-rule binop-val" (we::apply-rule 'w3t::step_pure/r-binop-val *z* *redex*))
(bench "try-rules binop" (we::try-rules (we::rules-for '(:op :binop)) *z* *redex*))
(defparameter *ms* (we::ms nil nil '((:const (:i32) 2) (:const (:i32) 7)) '((:binop (:i32) (:sub))) nil :run))
(bench "machine-step binop" (we::machine-step *ms*))
(defparameter *ms2* (we::ms nil nil nil '((:const (:i32) 2) (:binop (:i32) (:sub))) nil :run))
(bench "machine-step value push" (we::machine-step *ms2*))
(defparameter *ms3* (we::ms nil '(:%rec (:locals (:const (:i32) 5)) (:module)) nil '((:local.get 0)) nil :run))
(bench "machine-step local.get" (we::machine-step *ms3*))
