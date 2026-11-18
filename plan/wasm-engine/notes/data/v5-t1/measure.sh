#!/bin/sh
# Measurements for notes/V5-t1.md, read from the certification output of
# machine/spec-result and machine/opcodes. Run at the repository root after
# `make -C engine check`:
#   sh plan/wasm-engine/notes/data/v5-t1/measure.sh > plan/wasm-engine/notes/data/v5-t1/measure.txt
steps() {  # steps FILE EVENT NAME: prover steps of one event
  awk -v t="$3" -v e="$2" '
    /^Form:/ {if (p) {print "none counted"; exit} if (index($0, "Form:  ( " e " " t " ...)")) p=1}
    p && /^Prover steps counted:/ {print $4; exit}' engine/$1.cert.out
}
echo "== prover steps, machine/spec-result"
for t in MACHINE-CLOCK-IS-0-OR-1 MACHINE-STEP-RUNS-WHEN-CLOCK-1 MACHINE-STEP-CLOCK-1-CASES \
         MACHINE-CLOCK-1-SIMULATES MACHINE-STEP-SIMULATES MACHINE-RESULT-NOT-RUNNING \
         MACHINE-RESULT-IS-SPEC-RESULT; do
  echo "$t $(steps machine/spec-result DEFTHM $t)"; done
echo "MACHINE-CLOCKS (defun) $(steps machine/spec-result DEFUN MACHINE-CLOCKS)"
echo "== prover steps, machine/opcodes"
for t in OP-STEP-OUTSIDE-PROVED-OPCODES MACHINE-STEP-OUTSIDE-PROVED-OPCODES; do
  echo "$t $(steps machine/opcodes DEFTHM $t)"; done
echo "== census line"
grep -h "^PROVED-OPCODES-CENSUS" engine/machine/opcodes.cert.out
echo "== certification times"
for b in machine/spec-result machine/opcodes; do
  echo "$b $(grep -h "^Time:" engine/$b.cert.out | tail -1)"
done
echo "== hints"
for b in machine/spec-result machine/opcodes; do
  echo "$b :use $(grep -c ':use' engine/$b.lisp) :cases $(grep -c ':cases' engine/$b.lisp) :expand $(grep -c ':expand' engine/$b.lisp) Subgoal $(grep -c '"Subgoal' engine/$b.lisp)"
done
echo "== trust tags, skip-proofs, defaxiom in the two certificates"
for b in machine/spec-result machine/opcodes; do
  echo "$b ttags $(grep -c -i ':ttags' engine/$b.cert) skip-proofs $(grep -c -i 'skip-proofs' engine/$b.cert) defaxiom $(grep -c -i 'defaxiom' engine/$b.cert)"
done
