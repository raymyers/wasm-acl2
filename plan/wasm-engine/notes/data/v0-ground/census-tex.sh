#!/bin/sh
# V0 item 1: the rule census of a TeX run (engine/tex, fast machine and the
# driver's host step), instantiation included.
#   sh census-tex.sh [INPUT.tex] > census-tex.out   (inside nix develop, from the repository root)
# Needs engine/tex/build/dl and build/fs (sh engine/tex/fetch.sh). The DVI goes
# to a temporary directory.
set -e
root=$(pwd); here=$root/plan/wasm-engine/notes/data/v0-ground
tmp=$(mktemp -d)
[ -n "$1" ] && export TEXINPUT=$(cd "$(dirname "$1")" && pwd)/$(basename "$1") TEXPATH=$(cd "$(dirname "$1")" && pwd)
TEXCENSUS=$here/census.lisp TEXOUT=$tmp/out sh "$root/engine/tex/run.sh" \
  | grep -a "^CENSUS\|^main: \|^instantiate: \|^TOTAL\|^WROTE\|^DRIVER\|^HOST calls"
