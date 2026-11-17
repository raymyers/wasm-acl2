; E0 item 3: statistical profiles (SBCL sb-sprof) of the generated 3.0
; semantics: the counting loop and the nested-block loop (the two the plan
; names), plus the memory loop at 16 pages and the call chain at depth 50,
; whose step costs grow with memory size and call depth. From engine/bench
; inside `nix develop ../..`:
;   acl2 < profile.lsp > ../../plan/wasm-engine/notes/data/e0-baseline/profile-raw.out
;   python3 -I ../../plan/wasm-engine/notes/data/e0-baseline/classify.py \
;     ../../plan/wasm-engine/notes/data/e0-baseline/profile-raw.out
(ld "bench.lsp")
(in-package "W3T")
:q
(require :sb-sprof)
; a graph report (callers and callees of every function), cpu mode
(defun prof (file n)
  (sb-sprof:reset)
  (format t "~&PROFILE-BEGIN ~a ~a~%" file n)
  (sb-sprof:with-profiling (:max-samples 400000 :sample-interval 0.001 :mode :cpu :report nil)
    (w3t::bench1 file "run" (list (w3t::i32 n)) acl2::*the-live-state*))
  (sb-sprof:report :type :graph :stream *standard-output*)
  (format t "~&PROFILE-END ~a~%" file))
; bytes consed and GC time of the same run without the profiler
(defun alloc (file n)
  (sb-ext:gc :full t)
  (let ((b0 (sb-ext:get-bytes-consed)) (g0 sb-ext:*gc-run-time*)
        (t0 (get-internal-run-time)))
    (w3t::bench1 file "run" (list (w3t::i32 n)) acl2::*the-live-state*)
    (format t "~&ALLOC ~a ~a: bytes ~a gc-ms ~a run-ms ~a~%" file n
            (- (sb-ext:get-bytes-consed) b0)
            (round (* 1000 (- sb-ext:*gc-run-time* g0)) internal-time-units-per-second)
            (round (* 1000 (- (get-internal-run-time) t0)) internal-time-units-per-second))))
(alloc "wasm/count-1.wasm" 20000)
(alloc "wasm/nested-1.wasm" 5000)
(alloc "wasm/memloop-16.wasm" 2000)
(alloc "wasm/calls-1.wasm" 50)
(prof "wasm/count-1.wasm" 20000)
(prof "wasm/nested-1.wasm" 5000)
(prof "wasm/memloop-16.wasm" 2000)
(prof "wasm/calls-1.wasm" 50)
(acl2::exit-lisp 0)
