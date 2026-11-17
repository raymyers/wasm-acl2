; wasm3 M9: the generated 3.0 functions are admitted in the modes
; recorded in tests/sem-3.0/modes-3.0.lsp (logic + guards / logic / program).
; %TRY-LOGIC and %TRY-GUARDS fall back silently; this book makes a change
; visible. After an intended change, run `make modes SPEC=3.0` and commit it.
; The time limits of config :logic make the result depend on the machine.
(in-package "W3T")
(include-book "../../gen/wasm-3.0/wasm3")
(include-book "../sem/modes-lib")

(make-event
 (mv-let (actual state) (acl2::%modes-manifest "../../gen/wasm-3.0/" "wasm3" state)
   (mv-let (expected state) (acl2::%modes-read-file "modes-3.0.lsp" state)
     (let ((d (acl2::%modes-diff (acl2::%modes-flat (car expected)) (acl2::%modes-flat actual))))
       (if d
           (mv (msg "Generated functions whose mode differs from tests/sem-3.0/modes-3.0.lsp, ~
                     as (name recorded certified); run `make modes SPEC=3.0` if intended:~|~x0" d)
               nil state)
         (mv nil '(value-triple :modes-match-manifest) state))))))
