; Packages for the SpecTec -> ACL2 translation (plan/wasm1-translation).
; Deliberately independent of kestrel/wasm/portcullis and the WASM package.
(in-package "ACL2")

; The translator itself.
(defpkg "IL2ACL2" *acl2-exports*)

; The hand-written runtime (rt/), shared by every spec version (wasm3 prep,
; P2-layout option A). Each generated package (W1T, W2T, W3T) imports the
; names rt/ defines.
(defpkg "WRT" *acl2-exports*)
