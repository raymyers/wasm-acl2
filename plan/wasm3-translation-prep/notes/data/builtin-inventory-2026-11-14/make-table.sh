#!/bin/sh
# Rebuild the inventory table of P3-builtin-inventory.md (from translate/):
#   acl2 < <this dir>/clauseless.lsp > clauseless.out   (lists clause-less defs per IL)
#   make probe SPEC=3.0 EXCLUDE='X.* 6.* 7.*'           (for the "missing in rt/" line)
#   sh <this dir>/make-table.sh clauseless.out .probe/3.0/report.txt
# Category and oracle columns follow the rules written in the note.
cl=$1; report=$2
missing=" $(grep -A1 '^Builtins (clause' "$report" | tail -1 | sed 's/^  missing in rt\/: //') "
grep -E "^FILE|^[a-zA-Z_0-9]+ \(|^[a-zA-Z_0-9]+ NIL" "$cl" |
awk '/^FILE/ {f=$2} f ~ /3.0/ && !/^FILE/ {print $1}' | while read n; do
  case "$n" in
    ND|R_*) c=choice; o="V8 relaxed-SIMD behaviour (D4 fixes the choice)";;
    hostcall) c=host; o="none: the conformance driver's host module";;
    *) c=numeric
       case "$n" in
         inv_concat_|inv_concatn_) o="none needed: list function, checked by concat(inv(x)) = x";;
         ceilz) o="none: rational ceiling, tested by definition";;
         s33_to_u32) o="binary decoder (wabt/V8 accept the block type)";;
         *bytes_|ibits_|fbits_|inv_*bits_|inv_*bytes_) o="V8 memory store/load round trips";;
         irelaxed_*|frelaxed_*|relaxed_trunc__) o="V8 relaxed SIMD";;
         lanes_|inv_lanes_|ibitselect_|iavgr_|iq15mulr_sat_|narrow__|trunc_sat__|irev_|iandnot_|fpmin_|fpmax_) o="V8 SIMD / scalar ops (Node)";;
         *) o="V8 (existing 1.0 numeric vectors)";;
       esac;;
  esac
  if [ "$c" = numeric ]; then
    case "$missing" in *" $n "*) s="missing";; *) s="in rt/ (1.0, by name)";; esac
  else s="n/a"; fi
  echo "| \`\$$n\` | $c | $s | $o |"
done
