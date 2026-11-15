; One spec-test-3 script in a fresh session (run-all.sh prepends
; (assign t7-name "NAME")). Run from tests/spec/ after certifying
; t7-lib-3.0. Each command is its own form (see t7-lib-3.0.lisp).
(ld "t7-lib-3.0.acl2")
(in-package "W3T")
(include-book "t7-lib-3.0")
(t7-setup (@ acl2::t7-name) state)
(ld (@ t7-forms) :ld-error-action :continue)
(cw "T7-DONE ~s0~%" (@ acl2::t7-name))
(acl2::good-bye 0)
