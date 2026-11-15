#!/bin/sh
# Decode every module of the converted spec-test-<major> scripts with the
# generated parser (wasm3 M2). From translate/, after `make spec-data SPEC=V`
# and the certification of gen/wasm-V:
#   sh tests/spec/decode/run-decode.sh ACL2 V JOBS TIMEOUT
# Writes tests/spec/results/decode-V/: one NAME.out per script, TOTALS (per
# command kind), PER-SCRIPT (scripts with a module not as expected) and
# MISSES (every module not as expected: kind, file).
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
cat $out/*.out | grep -a "D3 :" | sed "s/^.*D3 :/D3 :/" | awk '{ k=$2; tot[k]++; if ($4=="T") p[k]++; if (($3=="T") == ($4=="T")) ok[k]++ }
  END { for (k in tot) printf "%s total %d parsed %d as-expected %d\n", k, tot[k], p[k]+0, ok[k]+0 }' | sort > $out/TOTALS
for f in $out/*.out; do n=$(basename $f .out)
  grep -a "D3 :" $f | sed "s/^.*D3 :/D3 :/" | awk -v n=$n '($3=="T") != ($4=="T") { print $2, n, $5 }'
done > $out/MISSES
awk '{ c[$2" "$1]++ } END { for (k in c) print k, c[k] }' $out/MISSES | sort > $out/PER-SCRIPT
grep -L "D3-EXIT 0" $out/*.out | sed 's|.*/||; s|\.out$||' > $out/NOT-FINISHED
cat $out/TOTALS
echo "modules not as expected: $(wc -l < $out/MISSES | tr -d ' '); scripts not finished: $(wc -l < $out/NOT-FINISHED | tr -d ' ')"
