#!/bin/sh
# L0 (plan/wasm-engine E12): build the renderer for DECK, render every slide
# on the engine, compare with V8, and write the viewer.
#   sh run.sh [DECK.txt] [OUTDIR]      (inside nix develop; defaults: deck.txt build)
# ENGINE=list runs the list machine, whose runs are inside theorem T1
# (plan2.md V5); the default is the fast machine through ENGINE-RUN, whose
# runs are inside theorem T3 (plan2.md V8).
# OUTDIR/view/index.html shows the engine's slides; the script fails unless
# every slide is identical to V8's.
set -e
here=$(cd "$(dirname "$0")" && pwd); deck=${1:-$here/deck.txt}; out=${2:-$here/build}
sh "$here/build.sh" "$deck" "$out"
out=$(cd "$out" && pwd); mkdir -p "$out/engine"
sh "$here/../../plan/wasm-engine/notes/data/e1-mupdf/census.sh" "$out/sent.wasm" > "$out/census.txt"
cd "$here" && { [ "$ENGINE" = list ] && echo "(assign engine :list)"; echo "(assign wasm-file \"$out/sent.wasm\")"; echo "(assign out-dir \"$out/engine\")"; cat render.lsp; } \
  | acl2 > "$out/engine/render.out" 2>&1
grep -a "ENGINE-" -A1 "$out/engine/render.out" | grep -v "^--"
node "$here/check.mjs" "$out/sent.wasm" "$out/engine" "$out/view" | tee "$out/check.out"
n=$(grep -c " SAME " "$out/check.out"); total=$(grep -c "^SLIDE" "$out/check.out")
[ "$n" = "$total" ] && [ "$n" -gt 0 ] || { echo "slides: $n of $total identical to V8"; exit 1; }
echo "slides: all $n identical to V8; viewer: $out/view/index.html"
