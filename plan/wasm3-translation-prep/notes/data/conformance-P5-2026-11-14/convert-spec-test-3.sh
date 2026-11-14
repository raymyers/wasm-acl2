#!/bin/sh
# wast2json (wabt 1.0.41, all features) over every .wast of spec-test-3 at the
# pinned spec rev. Usage, from the repo root inside `nix develop`:
#   sh plan/wasm3-translation-prep/notes/data/conformance-P5-2026-11-14/convert-spec-test-3.sh OUTDIR
# Prints per-directory counts; OUTDIR/failed.txt lists the scripts that fail.
set -e
SRC=$(nix eval --raw --impure --expr '(builtins.getFlake (toString ./.)).inputs.wasm-spec.outPath' 2>/dev/null)
out=$1; mkdir -p "$out"; cd "$out"; : > failed.txt
T=$SRC/spectec/test-interpreter/spec-test-3
for d in . bulk-memory exceptions gc memory64 multi-memory relaxed-simd simd; do
  ok=0; bad=0
  for f in $T/$d/*.wast; do
    b=$(echo "$d--$(basename $f .wast)" | sed 's/^\.--//'); mkdir -p "$b"
    if (cd "$b" && wast2json --enable-all "$f" -o "$b.json" > err.txt 2>&1); then ok=$((ok+1))
    else bad=$((bad+1)); echo "$b: $(grep -m1 error "$b/err.txt" | sed 's|.*spec-test-3/||' | cut -c1-120)" >> failed.txt; fi
  done
  echo "$d: converted $ok, failed $bad"
done
echo "modules: $(find . -name '*.wasm' | wc -l)"
