#!/bin/sh
# Typeset a file with tex.wasm on the engine, from the saved image.
#   sh tex.sh INPUT.tex OUTBASE     (inside nix develop)
# writes OUTBASE.dvi, OUTBASE.log, OUTBASE.aux. Build the image first:
#   TEXMODE=build sh run.sh
set -e
here=$(cd "$(dirname "$0")" && pwd)
[ -f "$here/build/tex.core" ] || { echo "run TEXMODE=build sh run.sh first"; exit 1; }
acl2=$(command -v acl2)
sbcl=$(sed -n 's/^exec "\([^"]*\)".*/\1/p' "$acl2")
eval "$(grep '^export SBCL_HOME' "$acl2")"
TEXINPUT=$(cd "$(dirname "$1")" && pwd)/$(basename "$1") TEXOUT=$2 \
  exec "$sbcl" --tls-limit 16384 --dynamic-space-size 32000 --control-stack-size 64 --disable-ldb \
  --core "$here/build/tex.core" --end-runtime-options
