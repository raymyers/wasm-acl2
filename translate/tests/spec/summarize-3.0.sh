#!/bin/sh
# Summarize results-3.0/*.out (run-all-3.0.sh): per script, commands passed /
# counted, its state (done / timeout / crashed), and per kind. A T7-TRY with
# no T7-CMD before the next T7-TRY (or the end) is a command that aborted:
# kind CRASH, failed. Skipped kinds (*-SKIPPED) are listed but not counted.
# TOTAL also gives assert_return + assert_trap for the scripts outside gc/.
dir=${1:-results-3.0}
for n in $(cat "$dir/NAMES"); do
  f="$dir/$n.out"
  awk -v n="$n" '
    { sub(/^.*!>+/, "") }
    /^T7-TRY / { if (open) { tot["CRASH"]++; all++ } open = ($2 != ":REGISTER") }  # register prints no T7-CMD
    /^T7-CMD / { open=0; k=$2; if (k ~ /SKIPPED/) { skip++; next } tot[k]++; all++; if ($3=="T") { ok[k]++; pass++ } }
    /^T7-DONE / { if (open) { tot["CRASH"]++; all++; open=0 } done=1 }
    /^T7-EXIT / { code=$2 }
    END {
      st = done ? "done" : (code==124 ? "timeout" : "crashed")
      printf "%s %d %d %s skipped=%d", n, pass, all, st, skip
      for (k in tot) printf " %s=%d/%d", k, ok[k], tot[k]
      printf "\n"
    }' "$f"
done | sort > "$dir/SUMMARY"
awk '{ p+=$2; t+=$3; s[$4]++
       for (i = 6; i <= NF; i++) { split($i, a, "[=/]"); k=a[1]; kp[k]+=a[2]; kt[k]+=a[3]
         if ($1 !~ /^gc--/ && (k == ":ASSERT_RETURN" || k == ":ASSERT_TRAP")) { np+=a[2]; nt+=a[3] } } }
  END {
    printf "T7 spec-test-3: %d of %d commands pass; scripts: %d done, %d timeout, %d crashed\n",
      p, t, s["done"], s["timeout"], s["crashed"]
    for (k in kt) printf "  %s %d/%d\n", k, kp[k], kt[k]
    printf "assert_return + assert_trap outside gc/: %d of %d\n", np, nt
  }' "$dir/SUMMARY" | tee "$dir/TOTAL"
# failures by kind and class (T7-FAILKIND lines), outside gc/ and in gc/
for f in $(cat "$dir/NAMES"); do
  case $f in gc--*) g=gc;; *) g=other;; esac
  grep -a "T7-FAILKIND" "$dir/$f.out" | sed "s/^.*T7-FAILKIND /$g /"
done | sort | uniq -c | sort -rn > "$dir/FAILKINDS"
