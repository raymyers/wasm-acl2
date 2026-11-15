#!/usr/bin/env bash
# W7 item 4: compare two spec result directories script by script: the
# sequence of T7-CMD lines must be identical. Scripts whose run timed out
# (T7-EXIT 124) or did not end with T7-EXIT 0 in either directory are listed
# separately (rerun once with a doubled TIMEOUT, plan W7 item 4). T7-EXIT
# follows the ACL2 prompt on its line, so its grep is not anchored.
# Usage: bash compare-spec.sh BEFORE_DIR AFTER_DIR
B=$1; A=$2
same=0; diff=0; odd=""
for f in $(cat "$B/NAMES"); do
  eb=$(grep -o 'T7-EXIT [0-9]*' "$B/$f.out" 2>/dev/null | tail -1); ea=$(grep -o 'T7-EXIT [0-9]*' "$A/$f.out" 2>/dev/null | tail -1)
  if [ "$eb" != "T7-EXIT 0" ] || [ "$ea" != "T7-EXIT 0" ]; then odd="$odd $f(${eb#T7-EXIT }/${ea#T7-EXIT })"; fi
  if cmp -s <(grep '^T7-CMD' "$B/$f.out") <(grep '^T7-CMD' "$A/$f.out") 2>/dev/null; then
    same=$((same+1))
  else
    diff=$((diff+1)); echo "W7-SPEC DIFFERS $f: $(grep -c '^T7-CMD' "$B/$f.out") vs $(grep -c '^T7-CMD' "$A/$f.out") T7-CMD lines"
  fi
done
echo "W7-SPEC identical T7-CMD sequences: $same; differing: $diff"
echo "W7-SPEC not exit 0 in before/after:${odd:- none}"
echo "W7-SPEC T7-CMD lines: before $(cat $B/*.out | grep -c '^T7-CMD'), after $(cat $A/*.out | grep -c '^T7-CMD')"
