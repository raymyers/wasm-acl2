#!/bin/sh
# Decode and validate each m-N.wasm with ../decode.lsp (one ACL2 session each).
cd "$(dirname "$0")/.."
for n in 100 400 1600 6400; do
  echo "== m-$n.wasm $(wc -c < scale/m-$n.wasm) bytes"
  (echo "(assign wasm-file \"scale/m-$n.wasm\")"; cat decode.lsp) \
    | nix develop ../.. -c sh -c "SBCL_USER_ARGS='--control-stack-size 4000' acl2" 2>&1 | grep -A1 "E1-DECODE" | grep -v "^--"
done
