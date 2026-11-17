#!/bin/sh
# Runs the typing cases on the generated code. From translate/ inside
# `nix develop ..`:   sh ../plan/wasm3-translation/notes/data/typing-M6-2026-11-14/run.sh
# 3.0 does not certify yet (wasm3 M0, M1), so its books are loaded from a
# scratch copy with proofs skipped (set-ld-skip-proofsp): definitions are
# accepted without termination proofs, execution is unchanged. Only the
# parts up to 2_3-validation_instructions are loaded; they need no missing
# builtin. About 30 s. 2.0 uses gen/wasm-2.0 as certified by `make check-2.0`.
set -e
D=$(cd "$(dirname "$0")" && pwd)
make gen SPEC=3.0 > /dev/null
rm -rf .probe/m6 && mkdir -p .probe/m6/gen/wasm-3.0
cp gen/wasm-3.0/*.lisp gen/wasm-3.0/*.lsp gen/wasm-3.0/*.acl2 .probe/m6/gen/wasm-3.0/
cp package.lsp .probe/m6/ && ln -s ../../rt .probe/m6/rt
(cd .probe/m6/gen/wasm-3.0 && acl2 < $D/cases-3.0.lsp) | grep -A1 "CASE "
(cd .probe/m6/gen/wasm-3.0 && acl2 < $D/cases-3.0-types.lsp) | grep -A1 "CASE "
(cd gen/wasm-2.0 && acl2 < $D/cases-2.0.lsp) | grep -A1 "CASE "
