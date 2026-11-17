#!/bin/sh
# Decode every module of the converted spec-test-<major> scripts with the
# generated parser (wasm3 M2, M3). From translate/, after
# `make spec-data SPEC=V` and the certification of gen/wasm-V:
#   sh tests/spec/decode/run-decode.sh ACL2 V JOBS TIMEOUT
# Writes tests/spec/results/decode-V/: one NAME.out per script, TOTALS (per
# command kind), MISSES (every module not as expected: kind, script, file),
# PER-SCRIPT, CRASHED (modules whose decoding exhausted a Lisp resource, see
# decode-one.lsp; also in MISSES) and NOT-FINISHED (scripts whose session
# did not reach the end).
acl2=$1; v=$2; jobs=${3:-8}; timeout=${4:-1800}
major=${v%%.*}
data=tests/spec/data$( [ "$v" = 1.0 ] || echo "-$v" )/
out=tests/spec/results/decode-$v
rm -rf $out && mkdir -p $out
sed -n 's/^ "\(.*\)"$/\1/p' $data/index.lsp > $out/NAMES
export acl2 timeout data out v major
xargs -P "$jobs" -I{} sh -c '
  { echo "(assign d3-name \"{}\")"; echo "(assign d3-data \"$data\")";
    echo "(ld \"gen/wasm-$v/portcullis.acl2\")"; echo "(in-package \"W${major}T\")";
    echo "(include-book \"gen/wasm-$v/wasm$major\")"; cat tests/spec/decode/decode-one.lsp; } |
    timeout "$timeout" "$acl2" > "$out/{}.out" 2>&1
  echo "D3-EXIT $?" >> "$out/{}.out"' < $out/NAMES
# one line per module: D3 KIND SHOULD PARSED FILE, with PARSED = CRASH for a
# D3-TRY that no D3 line follows
results() {
  grep -a "D3-TRY :\|D3 :" "$1" | sed "s/^.*D3-TRY :/D3-TRY :/; s/^.*D3 :/D3 :/" |
    awk '$1 == "D3-TRY" { if (pend != "") print pend; pend = "D3 " $2 " " $3 " CRASH " $4; next }
         { pend = ""; print }  END { if (pend != "") print pend }'
}
for f in $out/*.out; do results $f; done > $out/ALL
awk '{ k=$2; tot[k]++; if ($4=="T") p[k]++; if ($4=="CRASH") c[k]++; else if (($3=="T") == ($4=="T")) ok[k]++ }
  END { for (k in tot) printf "%s total %d parsed %d as-expected %d crashed %d\n", k, tot[k], p[k]+0, ok[k]+0, c[k]+0 }' $out/ALL | sort > $out/TOTALS
for f in $out/*.out; do n=$(basename $f .out)
  results $f | awk -v n=$n '$4 == "CRASH" || ($3=="T") != ($4=="T") { print $2, n, $5, ($4 == "CRASH" ? "CRASH" : "") }'
done > $out/MISSES
grep "CRASH$" $out/MISSES > $out/CRASHED
awk '{ c[$2" "$1]++ } END { for (k in c) print k, c[k] }' $out/MISSES | sort > $out/PER-SCRIPT
grep -L "D3-DONE" $out/*.out | sed 's|.*/||; s|\.out$||' > $out/NOT-FINISHED
cat $out/TOTALS
echo "modules not as expected: $(wc -l < $out/MISSES | tr -d ' ') (crashed: $(wc -l < $out/CRASHED | tr -d ' ')); scripts not finished: $(wc -l < $out/NOT-FINISHED | tr -d ' ')"
