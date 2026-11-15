#!/bin/sh
# W0 items 2 and 3: extract (throwaway extractor), compile with JSCL, load in
# node and in headless Chromium/Firefox, for the slice (rt/ + 0_*, 1_*) and
# for all books, with and without clause-chain flattening.
# From the repo root, inside `nix develop`, after `make -C translate gen SPEC=3.0`.
# Writes demo/build/w0/* and prints the measurements (saved as measure.out).
set -e
D=plan/wasm3-demo/notes/data/w0-slice
B=demo/build/w0
mkdir -p $B
install -m 644 "$JSCL_HOME/dist/jscl.js" $B/jscl.js
echo "== commit $(git rev-parse --short HEAD), jscl $(basename $(dirname $(dirname $JSCL_HOME)) | cut -d- -f2-)"
run() { # name root prefixes flatten
  name=$1
  ROOT=$2 PREFIXES=$3 FLATTEN=$4 sh $D/run-extract.sh $B/$name.lisp > $B/$name.extract.log 2>&1
  if grep -q "debugger invoked" $B/$name.extract.log; then echo "extract FAILED"; exit 1; fi
  echo "== $name (root $2, books $3, flatten $4)"
  sed -n '/; events by kind/,/clause chains/p' $B/$name.extract.log
  echo "lisp bytes $(wc -c < $B/$name.lisp)"
  node $D/depth.js $B/$name.lisp 3
  sh $D/run-compile.sh $B/$name.js $D/pkgs.lisp $B/$name.lisp | grep 'W0-COMPILE\|is undefined' | sed 's/WARNING: The function/undefined:/' | sort
  echo "js bytes $(wc -c < $B/$name.js)"
  for s in default 2000; do
    if [ $s = default ]; then f=; else f=--stack-size=$s; fi
    echo "node stack $s:"
    node $f $D/load.js $B $B/$name.js W3T::\$MIN '[3,5]' 2>&1 | grep 'W0-\|RangeError' || true
  done
  node $D/browser-load.mjs $B $name.js 2>&1 | grep W0- || true
}
run slice 1_4-syntax_modules '("0_" "1_")' nil
run full wasm3 '("")' nil
run flat wasm3 '("")' t
