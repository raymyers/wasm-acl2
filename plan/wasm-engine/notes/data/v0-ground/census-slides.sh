#!/bin/sh
# V0 item 1: the rule census of the slides (engine/slides, fast machine).
#   sh census-slides.sh > census-slides.out     (inside nix develop, from the repository root)
# Needs engine/slides/build/sent.wasm (make -C engine slides).
set -e
root=$(pwd); here=$root/plan/wasm-engine/notes/data/v0-ground
tmp=$(mktemp -d)
cd "$root/engine/slides"
{ echo "(assign wasm-file \"$root/engine/slides/build/sent.wasm\")"; echo "(assign out-dir \"$tmp\")"
  sed '$d' render.lsp
  echo '(acl2::value :q)'; echo "(common-lisp:load \"$here/census.lisp\")"; echo '(acl2::lp)'
  echo '(render-deck (@ acl2::wasm-file) (@ acl2::out-dir) fm state)'
  echo '(acl2::value :q)'; echo '(acl2::census-report)'; } | acl2 | grep -a "^ENGINE-\|^CENSUS"
