; E0 item 3: where the __bzero time of the profile comes from. Runs the
; counting loop with SBCL's nursery (bytes-consed-between-gcs) at ACL2's
; setting and at smaller sizes; prints GC count, GC time and run time.
;   acl2 < gc-probe.lsp > ../../plan/wasm-engine/notes/data/e0-baseline/gc-probe.out
(ld "bench.lsp")
(in-package "W3T")
:q
(defvar *gcs* 0)
(push (lambda () (incf *gcs*)) sb-ext:*after-gc-hooks*)
(defun gcrun (nursery)
  (when nursery (setf (sb-ext:bytes-consed-between-gcs) nursery))
  (sb-ext:gc :full t)
  (let ((g0 sb-ext:*gc-run-time*) (t0 (get-internal-real-time)) (n0 *gcs*) n)
    (w3t::bench1 "wasm/count-1.wasm" "run" (list (w3t::i32 20000)) acl2::*the-live-state*)
    (setq n (- *gcs* n0))
    (format t "~&GCPROBE nursery ~a: gcs ~a gc-ms ~a real-ms ~a~%"
            (sb-ext:bytes-consed-between-gcs) n
            (round (* 1000 (- sb-ext:*gc-run-time* g0)) internal-time-units-per-second)
            (round (* 1000 (- (get-internal-real-time) t0)) internal-time-units-per-second))))
(gcrun nil)
(gcrun (* 256 1024 1024))
(gcrun (* 64 1024 1024))
(gcrun (* 16 1024 1024))
(acl2::exit-lisp 0)
