; Run the translator for one spec version: from translate/,
;   { echo '(assign il2acl2-target (quote (:version "1.0" :pkg "W1T" ...)))'; cat il2acl2/run.lsp; } | acl2
; (`make gen SPEC=<v>` does this; see emit.lisp for the target's fields).
; Writes <outdir>{package.lsp,portcullis.*,cert.acl2,<book>.lisp}. Exits 1 on error.
(set-ld-error-action (quote (:exit 1)) state)
(ld "package.lsp")
(include-book "il2acl2/emit")
(in-package "IL2ACL2")
(mv-let (erp state)
  (gen-phase1 (@ acl2::il2acl2-target) state)
  (if erp
      (prog2$ (cw "~%il2acl2 phase 1 FAILED:~%~@0~%" erp) (mv (good-bye 1) nil state))
    (mv nil :phase1-ok state)))
(ld (concatenate 'string (tgt :outdir (@ acl2::il2acl2-target)) "package.lsp"))
(acl2::set-current-package (tgt :pkg (@ acl2::il2acl2-target)) state)
(mv-let (erp state)
  (il2acl2::gen-phase2 state)
  (if erp
      (prog2$ (cw "~%il2acl2 phase 2 FAILED:~%~@0~%" erp) (mv (good-bye 1) nil state))
    (mv nil :phase2-ok state)))
(good-bye 0)
