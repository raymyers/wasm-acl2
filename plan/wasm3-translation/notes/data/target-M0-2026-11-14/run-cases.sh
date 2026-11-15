#!/bin/sh
# wasm3 M0: the M6 typing cases on the CERTIFIED in-tree 3.0 books (no
# scratch copy, no skipped proofs), plus a memoization timing case. From
# translate/ inside `nix develop ..`, after `make check-3.0` (or cert.pl of
# gen/wasm-3.0/wasm3):  sh ../plan/wasm3-translation/notes/data/target-M0-2026-11-14/run-cases.sh
set -e
D=$(cd "$(dirname "$0")" && pwd)
M6=$D/../typing-M6-2026-11-14
for c in cases-3.0 cases-3.0-types; do
  # the M6 case files load a scratch copy with proofs skipped; here the
  # first three lines are replaced by an include of the certified book
  { echo '(ld "portcullis.acl2")'; echo '(include-book "2_3-validation_instructions")';
    sed '1,3d' $M6/$c.lsp; } > $D/.$c.lsp
  (cd gen/wasm-3.0 && acl2 < $D/.$c.lsp) | grep -A1 "CASE "
  rm -f $D/.$c.lsp
done
(cd gen/wasm-3.0 && acl2 < $D/memo-case.lsp) | grep -A3 "CASE \|took"
