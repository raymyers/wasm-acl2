; E1 item 5: where the generated decoder spends its time, on a synthetic
; module (scale/m-1600.wasm, 164 KB). sb-sprof cpu mode, flat report.
; From engine/mupdf inside `nix develop ../..`:
;   acl2 < profile-decode.lsp > ../../plan/wasm-engine/notes/data/e1-mupdf/profile-decode.out
(ld "../../translate/gen/wasm-3.0/portcullis.acl2")
(include-book "../../translate/gen/wasm-3.0/wasm3")
(in-package "W3T")
(program)
(set-state-ok t)
(defun read-bytes-loop (channel acc state)
  (mv-let (b state) (read-byte$ channel state)
    (if (null b) (mv (reverse acc) state) (read-bytes-loop channel (cons b acc) state))))
(defun read-bytes (file state)
  (mv-let (channel state) (open-input-channel file :byte state)
    (if (null channel) (mv nil state)
      (mv-let (bs state) (read-bytes-loop channel nil state)
        (let ((state (close-input-channel channel state))) (mv bs state))))))
(mv-let (bs state) (read-bytes "scale/m-1600.wasm" state)
  (let ((state (f-put-global 'bytes bs state))) (mv nil (acl2::len bs) state)))
:q
(require :sb-sprof)
(sb-sprof:with-profiling (:max-samples 400000 :sample-interval 0.001 :mode :cpu :report nil)
  (w3t::gram/bmodule (acl2::f-get-global 'w3t::bytes acl2::*the-live-state*)))
(sb-sprof:report :type :flat :max 40 :stream *standard-output*)
(sb-sprof:report :type :graph :max 30 :stream *standard-output*)
(acl2::exit-lisp 0)
