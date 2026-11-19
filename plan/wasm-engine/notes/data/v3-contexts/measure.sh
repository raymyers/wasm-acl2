#!/bin/sh
# Measurements for notes/V3-contexts.md, read from the certification output of
# rules/context, machine/op-context and lib/lists. Run at the repository root
# after `make -C engine check`:
#   sh plan/wasm-engine/notes/data/v3-contexts/measure.sh > plan/wasm-engine/notes/data/v3-contexts/measure.txt
steps() {  # steps FILE THEOREM: prover steps of one defthm
  awk -v t="$2" '
    index($0, "Form:  ( DEFTHM " t " ...)") || $0 == "Form:  ( DEFTHM " t {p=1}
    p && /^Prover steps counted:/ {print $4; exit}' engine/$1.cert.out
}
echo "== generator lines (rules/context)"
for k in EXIT-SEARCH EXIT-SEARCH-FAILED EXIT-BODY EXIT-BODY-FAILED; do
  echo "$k $(grep -c "^$k W3T" engine/rules/context.cert.out)"
done
echo "== census lines"
grep -h "^EXIT-SEARCH-CENSUS\|^EXIT-BODY-CENSUS" engine/rules/context.cert.out
echo "== the rules of an administrative term"
grep "^EXIT-BODY W3T" engine/rules/context.cert.out | sed 's/^EXIT-BODY //'
echo "== their searches, prover steps"
for f in $(grep "^EXIT-SEARCH W3T" engine/rules/context.cert.out | sed 's/^EXIT-SEARCH W3T:://'); do
  echo "$f $(steps rules/context $f-FAILS-WHEN-NOT-EXIT-BLOCK)"; done
echo "== prover steps of the generated rule lemmas: smallest, largest, sum"
for f in $(grep "^EXIT-BODY W3T" engine/rules/context.cert.out | sed 's/^EXIT-BODY W3T:://'); do
  steps rules/context $f-FAILS-WHEN-NOT-EXIT-BODY; done | sort -n |
  awk 'NR==1{min=$1} {max=$1; sum+=$1} END {print min, max, sum}'
echo "== prover steps, rules/context"
for t in NO-STEP-BELOW-WHEN-EXIT-HEAD STEP-OF-OPERANDS-EXIT-INSTR FLAT-SEARCH-OF-EXIT-INSTR \
         STEP-OF-REV-VALS-EXIT-INSTR-REST STEP-OF-VALS-EXIT-INSTR-REST \
         VALS-P-OF-TAKE-WHEN-LONGER-TAKE FIRST-NONVAL-WHEN-VALS-THEN-REFERENCE \
         STEP_READ/SPLIT/SEARCH118-SHAPE STEP_READ/SPLIT/SEARCH118-FAILS-WHEN-NOT-EXIT-BLOCK \
         STEP-OF-EXN-THROW NOT-EXIT-BODY-P-WHEN-BLOCK-STEPS \
         NOT-EXIT-BODY-P-OF-VALS-ADMIN-TERM-REST \
         STEP_PURE-OF-ADMIN-TERM-WHEN-BODY-NOT-EXIT \
         STEP_READ/SPLIT-OF-ADMIN-TERM-WHEN-BODY-NOT-EXIT \
         STEP-OF-ADMIN-TERM-IS-CONTEXT-RULE \
         STEP/R-CTXT-LABEL-OF-STEPPING-BODY STEP/R-CTXT-HANDLER-OF-STEPPING-BODY \
         STEP/R-CTXT-FRAME-OF-STEPPING-BODY \
         STEP-OF-ADMIN-TERM STEP-OF-ADMIN-TERM-IN-BLOCK; do
  echo "$t $(steps rules/context $t)"; done
echo "== prover steps, machine/op-context"
for t in ABS-CTRL-WHEN-CONSP ENTRY-OF-CAR-CTRL-FOR-STEP STEP-UNDER-CTRL OP-STEP-SIMULATES; do
  echo "$t $(steps machine/op-context $t)"; done
echo "== certification times"
for b in lib/lists rules/context machine/op-context machine/machine machine/ok machine/clock0; do
  echo "$b $(grep -h "^Time:" engine/$b.cert.out | tail -1)"
done
echo "== hints"
for b in rules/context machine/op-context; do
  echo "$b :use $(grep -c ':use' engine/$b.lisp) :cases $(grep -c ':cases' engine/$b.lisp) :expand $(grep -c ':expand' engine/$b.lisp) Subgoal $(grep -c '"Subgoal' engine/$b.lisp)"
done
