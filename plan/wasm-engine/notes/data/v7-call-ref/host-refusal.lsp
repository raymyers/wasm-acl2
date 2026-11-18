; V7: a call_ref of a host function on the two machines. The fast machine
; stops :unsupported with every other field as it was; the list machine
; applies a host rule (the hook is constrained, so its step is not run here).
; From engine/fast, inside nix develop:  acl2 < ../../plan/wasm-engine/notes/data/v7-call-ref/host-refusal.lsp
(ld "cert.acl2")
(include-book "fast")
(in-package "WE")
(defconst *st*
  (ms '(:%rec (:tags) (:globals) (:mems (:%rec (:type) (:bytes))) (:tables)
              (:funcs (:%rec (:type) (:module) (:code :_hostfunc "print"))
                      (:%rec (:type) (:module) (:code :func 0 nil nil)))
              (:datas) (:elems) (:structs) (:arrays) (:exns))
      '(:%rec (:locals) (:module)) '((:ref.func_addr 0)) '((:call_ref 0)) nil :run))
(let* ((fm (fm-load-ms *st* fm)) (fm (fast-step fm)))
  (prog2$ (cw "HOST-REFUSAL host ref: status ~x0, the rest unchanged ~x1~%" (fm-status fm)
              (equal (fm->ms fm) (ms-with-status :unsupported *st*)))
          fm))
(let* ((fm (fm-load-ms (ms (ms-store *st*) (ms-frame *st*) '((:ref.func_addr 1)) (ms-is *st*) nil :run) fm))
       (fm (fast-step fm)))
  (prog2$ (cw "HOST-REFUSAL wasm ref (function 1): host-ref-p ~x0, status ~x1~%"
              (host-ref-p '(:ref.func_addr 1) (fm-store fm)) (fm-status fm))
          fm))
