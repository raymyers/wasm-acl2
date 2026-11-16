#!/bin/sh
# W4 item 4: the invokes of timing.js in ACL2 (the certified
# tests/spec/t7-lib-3.0 book: parse-file, instantiate, do-action), each
# timed with time$ (one warm-up run, then 3 runs; real time as ACL2 prints
# it). Run inside nix develop, from the repo root:
#   sh plan/wasm3-demo/notes/data/w4/timing-acl2.sh
cd translate/tests/spec || exit 1
acl2 <<'EOF' 2>&1 | grep -E "W4-ACL2|realtime|took|rror"
(include-book "t7-lib-3.0")
(in-package "W3T")
(defun w4-do (a e)
  (declare (xargs :mode :program))
  (mv-let (r e2) (do-action a e) (declare (ignore e2)) r))
(defun w4-run (file fn args state)
  (declare (xargs :mode :program :stobjs state))
  (mv-let (m state) (parse-file file state)
    (mv-let (st s inst) (instantiate m (list *s0* nil nil nil))
      (declare (ignore st))
      (let ((e (list s inst nil nil)) (a (list :invoke nil (str-bytes fn) args)))
        (prog2$ (w4-do a e)
          (prog2$ (cw "W4-ACL2 ~s0 ~s1 (3 runs follow)~%" file fn)
            (prog2$ (time$ (w4-do a e))
              (prog2$ (time$ (w4-do a e))
                (prog2$ (time$ (w4-do a e))
                  (mv (w4-do a e) state))))))))))
(w4-run "fac.0.wasm" "fac-iter" '((:i64 25)) state)
(w4-run "fac.0.wasm" "fac-rec" '((:i64 25)) state)
(w4-run "call_indirect.0.wasm" "fac-i64" '((:i64 25)) state)
(w4-run "memory_redundancy.0.wasm" "test_redundant_load" nil state)
(w4-run "br_table.0.wasm" "large" '((:i32 100)) state)
EOF
