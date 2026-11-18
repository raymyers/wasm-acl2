#!/bin/sh
# Measurements for notes/V2-flat.md, read from the certification output of
# rules/flat, machine/op-flat and lib/lists. Run at the repository root after
# `make -C engine check`:
#   sh plan/wasm-engine/notes/data/v2-flat/measure.sh > plan/wasm-engine/notes/data/v2-flat/measure.txt
steps() {  # steps FILE THEOREM: prover steps of one defthm
  awk -v t="$2" '
    index($0, "Form:  ( DEFTHM " t " ...)") || $0 == "Form:  ( DEFTHM " t {p=1}
    p && /^Prover steps counted:/ {print $4; exit}' engine/$1.cert.out
}
echo "== generator lines (rules/flat)"
for k in INSTRS INSTRS-NONE STATE STATE-FAILED; do
  echo "$k $(grep -c "^$k W3T" engine/rules/flat.cert.out)"
done
echo "== rules with no INSTRS lemma"
grep "^INSTRS-NONE" engine/rules/flat.cert.out | sed 's/^INSTRS-NONE //'
echo "== census lines"
grep -h -A1 "^INSTRS-CENSUS\|^STATE-CENSUS" engine/rules/flat.cert.out | grep -v "^--\|^NIL"
echo "== prover steps, rules/flat"
for t in STEP/SEARCH21-BECOMES-FLAT-SEARCH STEP/R-CTXT-INSTRS-BECOMES-FLAT-SEARCH \
         STEP/R-CTXT-LABEL-FAILS-WHEN-NOT-SHAPE STEP/R-CTXT-HANDLER-FAILS-WHEN-NOT-SHAPE \
         STEP/R-CTXT-FRAME-FAILS-WHEN-NOT-SHAPE \
         STEP_PURE-ARITY STEP_READ/SPLIT-ARITY STEP-OWN-ARITY \
         STEP-OWN-RESULT-SHAPE STEP-OWN-STATE-SHAPE \
         STEP_PURE-INSTRS-TRUE-LISTP STEP_READ/SPLIT-INSTRS-TRUE-LISTP \
         STEP/R-PURE-OF-OPERANDS-WHEN-NOT-ARITY STEP/R-READ-OF-OPERANDS-WHEN-NOT-ARITY \
         STEP-OWN-OF-OPERANDS-WHEN-NOT-ARITY \
         STEP-OF-OPERANDS-WHEN-NO-STEP-BELOW FLAT-SEARCH-OF-OPERANDS-WHEN-NO-STEP-BELOW \
         NO-STEP-BELOW-ARITY STEP-OF-REDEX \
         FLAT-SEARCH-SKIPS-TOO-FEW-OPERANDS FLAT-SEARCH-AT-REDEX FLAT-SEARCH-FINDS-REDEX \
         STEP-OF-FLAT-BLOCK-IS-FLAT-SEARCH STEP-OF-FLAT-BLOCK \
         STEP-OF-ADMIN-TERM-IN-FLAT-BLOCK-IS-FLAT-SEARCH STEP-OF-ADMIN-TERM-IN-FLAT-BLOCK \
         TRY-RULES-ON-REDEX STEP-OF-REDEX-BY-RELATION TRY-RULES-ON-REDEX-IS-STEP; do
  echo "$t $(steps rules/flat $t)"; done
echo "== prover steps, machine/op-flat"
for t in OP-STEP-IS-STEP-OF-FLAT-BLOCK OP-INSTR-P-WHEN-OP-STEP-RUNS OP-STEP-SIMULATES-FLAT; do
  echo "$t $(steps machine/op-flat $t)"; done
echo "== certification times"
for b in lib/lists rules/flat machine/op-flat; do
  echo "$b $(grep -h "^Time:" engine/$b.cert.out | tail -1)"
done
echo "== hints"
for b in rules/flat machine/op-flat; do
  echo "$b :use $(grep -c ':use' engine/$b.lisp) :cases $(grep -c ':cases' engine/$b.lisp) :expand $(grep -c ':expand' engine/$b.lisp) Subgoal $(grep -c '"Subgoal' engine/$b.lisp)"
done
