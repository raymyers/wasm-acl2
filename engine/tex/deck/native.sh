#!/bin/sh
# Build deck.tex with an ordinary TeX (latex, then dvipdfmx) for quick
# iteration: a second or two instead of minutes on the engine.
#   sh native.sh     -> ../build/deck/native.pdf   (inside nix develop, for node)
# The article class stands in for the format tex.wasm starts from.
set -e
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../../.." && pwd)
out=$here/../build/deck; mkdir -p "$out"
tl="nix shell --inputs-from $root nixpkgs#texliveMedium -c"
node "$here/figdims.mjs" "$root/latex-slides/figs" figs/ > "$here/figdims.tex"
cd "$out"
TEXINPUTS=$here:$out: $tl latex -interaction=nonstopmode -jobname=native \
  '\documentclass{article}\usepackage{color}\input{deck.tex}' > native.out 2>&1 || true
grep -n -A3 '^!' native.log | head -40 || true
cd "$here"   # figs/ is here
$tl dvipdfmx -q -o "$out/native.pdf" "$out/native.dvi"
echo "-> $out/native.pdf"
