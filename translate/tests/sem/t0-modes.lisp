; wasm3 prep P2 (W8): the generated functions are admitted in the modes
; recorded in gen/wasm-1.0/modes.lsp (logic + guards / logic / program).
; %TRY-LOGIC and %TRY-GUARDS fall back silently; this book makes a change
; visible. After an intended change, run `make modes` and commit the result.
(in-package "W1T")
(include-book "../../gen/wasm-1.0/wasm1")
(include-book "modes-lib")

(make-event
 (mv-let (actual state) (acl2::%modes-manifest "../../gen/wasm-1.0/" "wasm1" state)
   (mv-let (expected state) (acl2::%modes-read-file "../../gen/wasm-1.0/modes.lsp" state)
     (let ((d (acl2::%modes-diff (acl2::%modes-flat (car expected)) (acl2::%modes-flat actual))))
       (if d
           (mv (msg "Generated functions whose mode differs from gen/wasm-1.0/modes.lsp, ~
                     as (name recorded certified); run `make modes` if intended:~|~x0" d)
               nil state)
         (mv nil '(value-triple :modes-match-manifest) state))))))
