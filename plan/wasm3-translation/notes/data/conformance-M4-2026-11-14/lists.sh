#!/bin/sh
# Per-script failure classes and the aborted commands of a spec-test-3 run
# (after `make spec SPEC=3.0`). From translate/tests/spec:
#   sh ../../../plan/wasm3-translation/notes/data/conformance-M4-2026-11-14/lists.sh results-3.0 OUTDIR
R=$1; O=$2
for f in $R/*.out; do n=$(basename $f .out); grep -a "T7-FAILKIND" $f | sed "s/^.*T7-FAILKIND /$n /"; done |
  awk '{c[$1" "$2" "$3]++} END {for (k in c) print c[k], k}' | sort -rn > $O/FAILKINDS-per-script.txt
for f in $R/*.out; do
  awk -v n=$(basename $f .out) '{ sub(/^.*!>+/, "") }
    /^T7-TRY/ { if (open) print n, last; open = ($2 != ":REGISTER"); last=$0 }
    /^T7-CMD/ { open=0 }  /^T7-DONE/ { if (open) print n, last; open=0 }' $f
done | sort | uniq -c > $O/ABORTED.txt
