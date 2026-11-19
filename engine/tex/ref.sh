#!/bin/sh
# The DVI comparison (plan/wasm-engine/plan2.md V8): typeset INPUT.tex with
# tex.wasm on V8 (node) and TikZJax's own host functions, and compare the
# DVI byte for byte with the one the engine wrote.
#   sh ref.sh INPUT.tex ENGINE.dvi [DIR ...]     (inside nix develop, for node)
# DIR: directories of files INPUT.tex reads (the engine's TEXPATH).
# Needs build/dl and build/fs (sh fetch.sh). Exit status 0: identical.
set -e
here=$(cd "$(dirname "$0")" && pwd)
in=$1; dvi=$2; shift 2
ref=$here/build/ref-$(basename "$in" .tex).dvi
node "$here/v8ref.cjs" "$here/build/dl/ref/library.js" "$here/build/dl" "$here/build/fs" "$in" "$ref" "$@"
echo "engine $(shasum -a 256 < "$dvi" | cut -d' ' -f1) $(wc -c < "$dvi" | tr -d ' ') bytes  $dvi"
echo "V8     $(shasum -a 256 < "$ref" | cut -d' ' -f1) $(wc -c < "$ref" | tr -d ' ') bytes  $ref"
if cmp -s "$dvi" "$ref"; then echo "DVI: identical, byte for byte"; else echo "DVI: DIFFERENT"; exit 1; fi
