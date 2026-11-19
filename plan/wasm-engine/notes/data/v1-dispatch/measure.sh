#!/bin/sh
# Measurements for notes/V1-dispatch.md, read from the certification output
# of the three books. Run at the repository root after `make -C engine check`:
#   sh plan/wasm-engine/notes/data/v1-dispatch/measure.sh > plan/wasm-engine/notes/data/v1-dispatch/measure.txt
R=engine/rules
steps() {  # steps BOOK THEOREM: prover steps of one defthm
  awk -v t="$2" '
    index($0, "Form:  ( DEFTHM " t " ...)") || $0 == "Form:  ( DEFTHM " t {p=1}
    p && /^Prover steps counted:/ {print $4; exit}' $R/$1.cert.out
}
echo "== generator lines"
for b in shape dispatch arity; do
  for k in SHAPE LENGTH FC MATCH REDEX ARITY; do
    n=$(grep -c "^$k " $R/$b.cert.out); [ "$n" != 0 ] && echo "$b $k $n"
  done
  echo "$b lemmas that did not prove (but the recorded match functions): $(grep -c '^SHAPE-FAILED\|^LENGTH-FAILED\|^FC-FAILED\|^REDEX-FAILED\|^ARITY-NONE' $R/$b.cert.out)"
  echo "$b MATCH-FAILED $(grep -c '^MATCH-FAILED' $R/$b.cert.out)"
done
echo "== census lines"
grep -h -A1 "CENSUS " $R/shape.cert.out $R/dispatch.cert.out $R/arity.cert.out | grep -v "Form:\|^ REDEX-CENSUS\|^--\|^ *:\|Rules:\|^WE !>>\$\|^(MAKE-EVENT\|^Summary\|^$" | sed 's/^WE !>>//' 
echo "== prover steps"
for t in STEP/PREFIX7-BECOMES-FIRST-NONVAL REDEX-SHAPE-P-OF-APPEND-OF-VALS-AND-INSTR \
         STEP_PURE/R-TRAP-INSTRS-FAILS-WHEN-FIRST-INSTR-NOT-TRAP \
         STEP_READ/SPLIT/R-THROW_REF-INSTRS-FAILS-WHEN-NO-THROW_REF; do
  echo "shape $t $(steps shape $t)"; done
for t in STEP_PURE-OF-REDEX-NOP STEP_PURE-OF-REDEX-BINOP STEP_READ/SPLIT-OF-REDEX-LOCAL.GET \
         STEP-OWN-OF-REDEX-CALL_REF \
         STEP_PURE-OF-REDEX-WITHOUT-RULE STEP_READ/SPLIT-OF-REDEX-WITHOUT-RULE STEP-OWN-OF-REDEX-WITHOUT-RULE \
         TRY-RULES-OF-PURE-RULES TRY-RULES-OF-READ-RULES TRY-RULES-OF-OWN-RULES TRY-RULES-OF-RULES-FOR \
         STEP_PURE-OF-VALS-INSTR-REST STEP_READ/SPLIT-OF-VALS-INSTR-REST STEP-OWN-OF-VALS-INSTR-REST \
         STEP_PURE-OF-VALS-INSTR-WITHOUT-RULE STEP_READ/SPLIT-OF-VALS-INSTR-WITHOUT-RULE \
         STEP/R-PURE-OF-VALS-INSTR-REST STEP/R-READ-OF-VALS-INSTR-REST \
         STEP/R-PURE-OF-VALS-NOP-REST STEP/R-READ-OF-VALS-NOP-REST \
         STEP/R-PURE-OF-VALS-BINOP-REST STEP/R-READ-OF-VALS-BINOP-REST \
         STEP/R-PURE-OF-VALS-LOCAL.GET-REST STEP/R-READ-OF-VALS-LOCAL.GET-REST; do
  echo "dispatch $t $(steps dispatch $t)"; done
for t in STEP_READ/SPLIT/R-BLOCK-ARITY STEP_READ/SPLIT/R-LOOP-ARITY STEP_READ/SPLIT/R-TRY_TABLE-ARITY \
         STEP/R-THROW-ARITY STEP/R-CALL_REF-NULL-ARITY STEP/R-CALL_REF-FUNC-ARITY \
         STEP/R-CALL_REF-HOSTFUNC-RES-ARITY STEP/R-CALL_REF-HOSTFUNC-DIV-ARITY; do
  echo "arity $t $(steps arity $t)"; done
echo "== certification time, seconds (cert.pl, real)"
for b in shape dispatch arity; do
  echo "$b $(grep -h 'Time:.*seconds' $R/$b.cert.out | tail -1)"
done
echo "== demo rules (V0 census) without an arity lemma"
for r in $(awk 'NR>1 && $1 ~ /\/R-/ {print $1}' plan/wasm-engine/notes/data/v0-ground/census-table.txt); do
  grep -q "^ARITY W3T::$r\$" $R/arity.cert.out || grep -q "^$r-ARITY\|DEFTHM $r-ARITY" $R/arity.cert.out || echo "  $r"
done
echo "== heads with a rule that REDEX-ARITY does not support"
grep -h "^SHAPE W3T::" $R/shape.cert.out | sed 's/^SHAPE //' | sort > /tmp/v1-shape.$$
grep -h "^ARITY W3T::" $R/arity.cert.out | sed 's/^ARITY //' | sort > /tmp/v1-arity.$$
comm -23 /tmp/v1-shape.$$ /tmp/v1-arity.$$ | grep -v "LABEL\|FRAME\|HANDLER\|R-BLOCK\|R-LOOP\|R-TRY_TABLE\|R-CALL_REF" | grep -v "R-THROW$" \
  | sed 's/.*\/R-//; s/-.*//' | sort -u | tr '\n' ' '; echo
rm -f /tmp/v1-shape.$$ /tmp/v1-arity.$$
