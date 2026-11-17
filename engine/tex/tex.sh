#!/bin/sh
# Typeset a file with tex.wasm on the engine, from the saved image.
#   sh tex.sh INPUT.tex OUTBASE
# writes OUTBASE.dvi, OUTBASE.log, OUTBASE.aux, with the driver's detail on
# the terminal. Build the image first:  TEXMODE=build sh run.sh
# (build/acl2-wasm-tex FILE.tex is the short form: quiet, output in the
# current directory.)
# TEXSNAP=FILE: when TeX is about to read a line "%%% snapshot" of INPUT.tex,
# save an image there and stop. TEXCORE=FILE then starts from that image:
# INPUT.tex must be the same up to that line, and can differ after it.
set -e
here=$(cd "$(dirname "$0")" && pwd)
core=${TEXCORE:-$here/build/acl2-wasm-tex}
[ -x "$core" ] || { echo "no $core: run TEXMODE=build sh run.sh first"; exit 1; }
TEXINPUT=$(cd "$(dirname "$1")" && pwd)/$(basename "$1") TEXOUT=$2 exec "$core"
