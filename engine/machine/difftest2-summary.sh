#!/bin/sh
# Summary of a differential test 2 run (difftest2-all.sh): OUTDIR/SUMMARY.
# A command's class is counted from its D2-CMD line; its group (S0 to S3,
# S4 = outside D5) when ACL2 printed it on the same line.
cd "$1"
{ echo "scripts $(wc -l < NAMES | tr -d ' ')  finished $(grep -al 'D2-DONE [a-z]' *.out | wc -l | tr -d ' ')"
  for c in same differ unsupported spec-fuel not-invoke; do
    echo "$c $(grep -aho "D2-CMD :[A-Z_]* :[A-Z-]*" *.out | grep -c " :$(echo $c | tr a-z A-Z)$" || true)"; done
  echo "commands per class and group (S4 = outside D5; no group = printed on another line):"
  grep -aho "D2-CMD :[A-Z_]* :[A-Z-]*\( S[0-9]\)*" *.out | awk '{print $3, ($4 ? $4 : "?")}' | sort | uniq -c
  echo "scripts with a difference: $(grep -al 'D2-DIFF' *.out | sed 's/.out$//' | tr '\n' ' ')"
  echo "scripts where the driver itself failed (ACL2 Error before the first command): $(for f in *.out; do awk '/D2-CMD|T7-TRY/{exit} /ACL2 Error/{print FILENAME; exit}' $f; done | sed 's/.out$//' | tr '\n' ' ')"
  echo "scripts not finished (D2-EXIT 137 or 124 is the time limit): $(for f in $(grep -aL 'D2-DONE [a-z]' *.out); do echo "${f%.out}($(grep -ao 'D2-EXIT [0-9]*' $f | cut -d' ' -f2))"; done | tr '\n' ' ')"
} > SUMMARY
cat SUMMARY
