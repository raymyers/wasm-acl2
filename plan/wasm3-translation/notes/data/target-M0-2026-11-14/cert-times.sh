#!/bin/sh
# Per-book certification time of gen/wasm-3.0 (the CERTIFY-BOOK summary of
# each .cert.out), after `make check-3.0`. From translate/.
for f in gen/wasm-3.0/*.lisp; do b=$(basename $f .lisp)
  t=$(grep -A2 "Form:  (CERTIFY-BOOK \"$b\"" gen/wasm-3.0/$b.cert.out | grep -o "Time: *[0-9.]*" | grep -o "[0-9.]*$")
  echo "$b $t"; done
