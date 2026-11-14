; Run the translator: from translate/,  acl2 < il2acl2/run.lsp
; Writes gen/{package.lsp,portcullis.*,cert.acl2,wasm1.lisp}. Exits 1 on error.
(set-ld-error-action (quote (:exit 1)) state)
(ld "package.lsp")
(include-book "il2acl2/emit")
(in-package "IL2ACL2")
(mv-let (erp state)
  (gen-phase1 "il/wasm-1.0.il.sexp" "il2acl2-config.lsp" "gen/" state)
  (if erp
      (prog2$ (cw "~%il2acl2 phase 1 FAILED:~%~@0~%" erp) (mv (good-bye 1) nil state))
    (mv nil :phase1-ok state)))
(ld "gen/package.lsp")
(in-package "W1T")
(mv-let (erp state)
  (il2acl2::gen-phase2 "gen/" state)
  (if erp
      (prog2$ (cw "~%il2acl2 phase 2 FAILED:~%~@0~%" erp) (mv (good-bye 1) nil state))
    (mv nil :phase2-ok state)))
(good-bye 0)
