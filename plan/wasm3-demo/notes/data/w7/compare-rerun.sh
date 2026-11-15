#!/usr/bin/env bash
# W7 item 4: the reruns with a doubled TIMEOUT (rerun-all.sh), before
# against after, per script. Both complete: the T7-CMD sequences must be
# identical. One or both cut by the timeout: the shorter sequence must be a
# prefix of the longer one (they stop at different commands under load).
# Usage: bash compare-rerun.sh BEFORE_RERUN_DIR AFTER_RERUN_DIR
B=$1; A=$2
for f in "$B"/*.out; do
  n=$(basename "$f" .out)
  eb=$(grep -o 'T7-EXIT [0-9]*' "$f" | tail -1); ea=$(grep -o 'T7-EXIT [0-9]*' "$A/$n.out" | tail -1)
  grep '^T7-CMD' "$f" > /tmp/w7-b.$$; grep '^T7-CMD' "$A/$n.out" > /tmp/w7-a.$$
  lb=$(wc -l < /tmp/w7-b.$$ | tr -d ' '); la=$(wc -l < /tmp/w7-a.$$ | tr -d ' ')
  m=$(( lb < la ? lb : la ))
  if cmp -s /tmp/w7-b.$$ /tmp/w7-a.$$; then v="identical"
  elif cmp -s <(head -n $m /tmp/w7-b.$$) <(head -n $m /tmp/w7-a.$$); then v="same on the first $m lines (prefix)"
  else v="DIFFER"; fi
  echo "W7-RERUN $n: before ${eb#T7-EXIT } ($lb lines), after ${ea#T7-EXIT } ($la lines): $v"
  rm -f /tmp/w7-b.$$ /tmp/w7-a.$$
done
