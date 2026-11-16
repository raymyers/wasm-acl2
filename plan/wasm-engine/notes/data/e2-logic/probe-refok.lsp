; E2 probe: why REF_OK / REF_OK/SPLIT fall back to program mode.
; Run from translate/tests/sem-3.0/ on books where the type group is in logic mode
; and the rules are still inline (the E2 measures without the rule functions).
; Result: admitted, 55.88 s of proof, 37,894,051 prover steps (limits: 20 s, 2,000,000).
(ld "cert.acl2")
(in-package "ACL2")
(include-book "../../gen/wasm-3.0/wasm3")
(set-current-package "W3T" state)
(acl2::set-gag-mode acl2::nil)
(acl2::time$ (acl2::with-prover-time-limit 120
(acl2::verify-termination
 (ref_ok (acl2::declare (acl2::xargs :ruler-extenders :all
   :hints (("Goal" :in-theory (acl2::union-theories (acl2::theory 'acl2::ground-zero)
       '(%om-o< %om-o-p %om3-o< %om3-o-p (:type-prescription %size))))))))
 (ref_ok/split (acl2::declare (acl2::xargs :ruler-extenders :all))))))
