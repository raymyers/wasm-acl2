; notes/V3-contexts.md §6: a HANDLER_ term whose catch clauses are not a true
; list. The specification does not step; the machine must not either.
; From engine/machine (nix develop ../..):
;   acl2 < ../../plan/wasm-engine/notes/data/v3-contexts/handler-bug.lsp
(ld "cert.acl2")
(include-book "ok")
(in-package "WE")
(let* ((c '(:|%;%| (:|%;%| st fr) ((:handler_%{%}% 0 5 ((:nop))))))
       (s (ms-of-config c)))
  (list :machine-ok (machine-ok s)
        :spec-step (w3t::step c)
        :after-1-step (machine-run 1 s)
        :clock-of-step-2 (machine-clock (machine-run 1 s))
        :after-2-steps (machine-run 2 s)))
