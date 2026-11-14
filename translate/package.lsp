; Packages for the SpecTec -> ACL2 translation (plan/wasm1-translation).
; Deliberately independent of kestrel/wasm/portcullis and the WASM package.
(in-package "ACL2")

; The translator itself.
(defpkg "IL2ACL2" *acl2-exports*)
