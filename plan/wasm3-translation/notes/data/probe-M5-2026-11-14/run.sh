#!/bin/sh
# Regenerates the files of this directory. Run from translate/ inside
# `nix develop ..`:   sh ../plan/wasm3-translation/notes/data/probe-M5-2026-11-14/run.sh
# Made at: f5d4bbb plus the commit of notes/M5-mode-table.md.
set -e
D=$(cd "$(dirname "$0")" && pwd)
T=$(mktemp -d)
CORE='X.* 6.* 7.*'            # the D3 scope of 3.0

probe() {                     # version, excluded files, config, output name
  make probe SPEC=$1 EXCLUDE="$2" PROBE_CONFIG=$3 > /dev/null
  cp .probe/$1/report.txt $D/$4.txt
  cp .probe/$1/rules.txt $D/$4-rules.txt
}

# Final state (the checked-in configs).
probe 1.0 '' config/wasm-1.0.lsp report-1.0
probe 2.0 '' config/wasm-2.0.lsp report-2.0
probe 3.0 "$CORE" config/wasm-3.0.lsp report-3.0-core

# Experiment B: no :witness entry, so every premise that relies on a single
# witness is reported as a failing rule ("witness choice").
for v in 1.0 2.0 3.0; do
  perl -0pe 's/ \(:witness .*?:reason "[^"]*"\)\n//s' config/wasm-$v.lsp > $T/nowit-$v.lsp
done
probe 1.0 '' $T/nowit-1.0.lsp exp-B-1.0
probe 2.0 '' $T/nowit-2.0.lsp exp-B-2.0
probe 3.0 "$CORE" $T/nowit-3.0.lsp exp-B-3.0-core

# Experiment A: the witness rule switched off for the 3.0 type group (all 19
# members accepted as witness sources), i.e. demotion to a fixpoint alone.
# The group then ends :multi with no failing rule, Heaptype_sub/trans included.
G='"Heaptype_ok" "Reftype_ok" "Valtype_ok" "Typeuse_ok" "Resulttype_ok" "Fieldtype_ok" "Storagetype_ok" "Comptype_ok" "Subtype_ok2" "Rectype_ok2" "Deftype_ok" "Comptype_sub" "Deftype_sub" "Heaptype_sub" "Reftype_sub" "Valtype_sub" "Resulttype_sub" "Storagetype_sub" "Fieldtype_sub"'
G="$G" perl -0pe 's/(:witness "[^"]*"\n  :rels \()/$1$ENV{G} /' config/wasm-3.0.lsp > $T/expA-3.0.lsp
probe 3.0 "$CORE" $T/expA-3.0.lsp exp-A-3.0-core

# Calls of each R/SPLIT in the generated code (the defun itself not counted).
make gen SPEC=3.0 > /dev/null
{ for v in 1.0 3.0; do
    cat gen/wasm-$v/*.lisp > $T/all.lisp
    echo "WASM $v: output variant, calls in gen/wasm-$v/"
    for s in $(grep -o "(DEFUN [^ ]*/SPLIT " $T/all.lisp | awk '{print $2}' | sort -u); do
      echo "  $s $(grep -o "($s " $T/all.lisp | wc -l | tr -d ' ')"
    done
  done; } > $D/split-calls.txt
rm -rf $T
