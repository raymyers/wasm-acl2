#!/bin/sh
# Run texrun.lisp with the engine's fast machine loaded (inside nix develop).
#   sh run.sh                  typeset input.tex in this process -> build/out.dvi
#   TEXMODE=build sh run.sh    save build/acl2-wasm-tex, an executable ACL2
#                              image that starts at TeX's main
# Needs build/dl and build/fs (sh fetch.sh) and the engine books certified
# (make -C engine certify BOOKS=fast/fast).
set -e
here=$(cd "$(dirname "$0")" && pwd)
export TEXHOST=$here/build TEXDL=$here/build/dl
export TEXINPUT=${TEXINPUT:-$here/input.tex}
[ -f "$TEXDL/tex.wasm" ] || { echo "run sh fetch.sh first"; exit 1; }
wat2wasm "$here/helper.wat" -o "$TEXHOST/helper.wasm"
cd "$here/../fast"
{ echo '(ld "cert.acl2")'; echo '(include-book "fast")'; echo '(value :q)'
  echo "(load \"$here/texrun.lisp\")"; } | acl2
