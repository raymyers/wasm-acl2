#!/bin/sh
# Summarize results/*.out of run-all.sh: per script, commands passed / run
# (from the T7-CMD lines, so a crashed or timed-out script still counts the
# commands it finished), its state (done / timeout / crashed), and totals.
# Skipped kinds (exhaustion, text-format malformed) are not counted.
dir=${1:-results}
for n in $(cat "$dir/NAMES"); do
  f="$dir/$n.out"
  awk -v n="$n" '
    { sub(/^.*!>/, "") }                      # drop an ACL2 prompt before the line
    /^T7-CMD / { k=$2; if (k ~ /SKIPPED/) next; tot[k]++; all++; if ($3=="T") { ok[k]++; pass++ } }
    /^T7-DONE / { done=1 }
    /^T7-EXIT / { code=$2 }
    END {
      st = done ? "done" : (code==124 ? "timeout" : "crashed")
      printf "%s %d %d %s", n, pass, all, st
      for (k in tot) printf " %s=%d/%d", k, ok[k], tot[k]
      printf "\n"
    }' "$f"
done | sort > "$dir/SUMMARY"
awk '{ p+=$2; t+=$3; s[$4]++ } END {
  printf "T7 spec-test-1: %d of %d commands pass; scripts: %d done, %d timeout, %d crashed\n",
    p, t, s["done"], s["timeout"], s["crashed"] }' "$dir/SUMMARY" | tee "$dir/TOTAL"
