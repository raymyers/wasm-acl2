; notes/V4-exits.md §6: (ref.null_addr) (throw_ref). The specification steps
; to TRAP (Step_read/throw_ref-null); the machine of commit f8c3d9f tested the
; head :REF.NULL, which no value has, and ended :STUCK.
; Run in engine/machine: acl2 < ../../plan/wasm-engine/notes/data/v4-exits/throw-null-bug.lsp
(include-book "machine")
(in-package "WE")
(defun run-config (c)
  (declare (xargs :mode :program))
  (let* ((s (ms-of-config c)) (r (machine-run 10 s)))
    (list :spec-step (w3t::step c) :machine-status (ms-status r)
          :machine-abs (machine-abs r))))
(run-config (list :|%;%| (list :|%;%| nil nil) '((:ref.null_addr) (:throw_ref))))
(run-config (list :|%;%| (list :|%;%| nil nil) '((:ref.null_addr) (:ref.null_addr) (:throw_ref) (:nop))))
(run-config (list :|%;%| (list :|%;%| nil nil) '((:label_%{%}% 0 nil ((:ref.null_addr) (:throw_ref))))))
