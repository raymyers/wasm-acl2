#!/bin/sh
# wasm3 M0b cross-check: convert every script that wast2json CAN read a
# second time, through the reference interpreter (.bin.wast) and the same
# gen-spec-tests.mjs, and compare the command lists after norm.mjs (file
# names, text-only assert_malformed, v128 lane labels -> bytes, typed vs
# untyped nulls, `either`). From the repo root:
#   sh plan/wasm3-translation/notes/data/spec-test-3-M0b-2026-11-14/xcheck.sh OUT_DIR
set -e
D=$(cd "$(dirname "$0")" && pwd)
OUT=$1; mkdir -p $OUT/work $OUT/conv
W=$(nix build .#wasm-ref-interp --no-link --print-out-paths)/bin/wasm
REF=$(nix build .#wasm3-spec-tests --no-link --print-out-paths)
SRC=$(nix eval --raw --impure --expr '(builtins.getFlake (toString ./.)).inputs.wasm-spec.outPath')/spectec/test-interpreter/spec-test-3
for b in $(sed -n 's/^ "\(.*\)"$/\1/p' $REF/index.lsp); do
  grep -qx "$b" $REF/REFINTERP && continue
  mkdir -p $OUT/work/$b
  $W -d $SRC/$(echo $b | sed 's|--|/|').wast -o $OUT/work/$b/$b.bin.wast > /dev/null 2>&1 || echo "reference interpreter failed: $b"
done
node translate/tests/oracle/gen-spec-tests.mjs $OUT/work $OUT/conv spec-test-3
same=0; n=0; : > $OUT/differ.txt
for l in $OUT/conv/*.lsp; do b=$(basename $l .lsp); [ $b = index ] && continue; n=$((n+1))
  if [ "$(node $D/norm.mjs $l)" = "$(node $D/norm.mjs $REF/$b.lsp)" ]; then same=$((same+1))
  else echo "== $b" >> $OUT/differ.txt; diff <(node $D/norm.mjs $l) <(node $D/norm.mjs $REF/$b.lsp) | head -4 | cut -c1-240 >> $OUT/differ.txt || true; fi
done
echo "cross-check: $same of $n scripts give the same commands (differences: $OUT/differ.txt)"
