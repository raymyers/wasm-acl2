#!/bin/sh
# For each module of tests/spec/results/decode-V/MISSES, what the reference
# interpreter's decoder says (wasm -u -d: decode without validation). From
# translate/:  sh ../plan/wasm3-translation/notes/data/decode-M2-2026-11-14/misses-ref-interp.sh V
v=$1; data=tests/spec/data$( [ "$v" = 1.0 ] || echo "-$v" )
W=$(nix build ..#wasm-ref-interp --no-link --print-out-paths)/bin/wasm
while read k n f; do
  if $W -u -d $data/$f > /dev/null 2>&1; then r=decodes
  else r="rejects: $($W -u -d $data/$f 2>&1 | sed 's/^[^:]*:[^:]*: //' | head -1)"; fi
  echo "$k $n $f | ref-interp $r"
done < tests/spec/results/decode-$v/MISSES
