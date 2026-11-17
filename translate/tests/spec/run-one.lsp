; One spec-test-1 script in a fresh session (run-all.sh prepends
; (assign t7-name "NAME")). Run from tests/spec/ after certifying t7-lib.
(ld "cert.acl2")
(in-package "W1T")
(include-book "t7-lib")
(run-one-script (@ acl2::t7-name) state)
(acl2::good-bye 0)
