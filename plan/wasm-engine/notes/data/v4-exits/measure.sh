#!/bin/sh
# Measurements for notes/V4-exits.md, read from the certification output of
# rules/exits and machine/exit-steps. Run at the repository root after
# `make -C engine check`:
#   sh plan/wasm-engine/notes/data/v4-exits/measure.sh > plan/wasm-engine/notes/data/v4-exits/measure.txt
steps() {  # steps FILE THEOREM: prover steps of one defthm (a long name is on its own line)
  awk -v t="$2" '
    index($0, "Form:  ( DEFTHM " t " ...)") || $0 == "Form:  ( DEFTHM " t {p=1}
    $0 == "Form:  ( DEFTHM " {q=1; next}
    q {if ($0 == t || $0 == t " ...)") p=1; q=0}
    p && /^Prover steps counted:/ {print $4; exit}' engine/$1.cert.out
}
echo "== generator lines (rules/exits)"
for k in SEARCH-INSTRS SEARCH-INSTRS-NONE INSTRS INSTRS-NONE; do
  echo "$k $(grep -c "^$k W3T" engine/rules/exits.cert.out)"
done
echo "== census lines"
grep -h "^SEARCH-INSTRS-CENSUS\|^INSTRS-CENSUS" engine/rules/exits.cert.out
echo "== the searches, prover steps (generated, then by hand)"
for f in $(grep "^SEARCH-INSTRS W3T" engine/rules/exits.cert.out | sed 's/^SEARCH-INSTRS W3T:://') \
         STEP_PURE/SEARCH51 STEP_READ/SPLIT/SEARCH118 STEP_READ/SPLIT/SEARCH119; do
  echo "$f $(steps rules/exits $f-INSTRS-TRUE-LISTP)"; done
echo "== the 12 rules, prover steps"
for f in $(grep "^INSTRS W3T" engine/rules/exits.cert.out | sed 's/^INSTRS W3T:://'); do
  echo "$f $(steps rules/exits $f-INSTRS-TRUE-LISTP)"; done
echo "== prover steps, rules/exits"
for t in STEP_PURE-INSTRS-TRUE-LISTP-OF-ADMIN-TERM STEP_READ/SPLIT-INSTRS-TRUE-LISTP-OF-ADMIN-TERM \
         TRY-RULES-ON-ADMIN-TERM TRY-RULES-ON-ADMIN-TERM-RESULT \
         STEP-OF-ADMIN-TERM-WHEN-RULE-FIRES STEP-OF-ADMIN-TERM-IN-BLOCK-WHEN-RULE-FIRES \
         STEP-OF-EXIT-TERM \
         STEP_PURE-OF-VALS-TRAP-REST STEP_READ/SPLIT-OF-VALS-THROW_REF-REST \
         STEP_PURE-OF-VALS-THROW_REF-REST \
         STEP_READ/SPLIT/R-THROW_REF-INSTRS-OF-VALS-TRAP-REST \
         STEP_PURE/R-TRAP-INSTRS-OF-VALS-THROW_REF-REST \
         FIRST-NONVAL-WHEN-VALS-THEN-EXN-THROW EXN-BEFORE-THROW-P-WHEN-VALS-THEN-EXN-THROW \
         EXN-BEFORE-THROW-P-OF-REV-VALS-THROW_REF-REST \
         STEP_READ/SPLIT/SEARCH134-FAILS-WHEN-NOT-EXN-BEFORE-THROW \
         STEP_READ/SPLIT/R-THROW_REF-INSTRS-FAILS-WHEN-NOT-EXN-BEFORE-THROW \
         STEP_READ/SPLIT/R-THROW_REF-NULL-FAILS-WHEN-NOT-NULL \
         STEP_READ/SPLIT/R-THROW_REF-NULL-OF-REV-VALS-THROW_REF-REST \
         STEP-OF-BLOCK-RULE \
         STEP-OF-THROW_REF-INSTR-ALONE NO-STEP-BELOW-1-OF-THROW_REF \
         TRY-RULES-ON-NULL-THROW_REF-IS-STEP STEP-OF-NULL-THROW_REF-BLOCK-IS-FLAT-SEARCH \
         STEP-OF-NULL-THROW_REF-BLOCK; do
  echo "$t $(steps rules/exits $t)"; done
echo "== prover steps, machine/exit-steps"
for t in STEPN-1-UNDER-CTRL BLOCK-STEP-SIMULATES EXIT-STEP-SIMULATES ANYPREFIX-STEP-SIMULATES \
         OP-STEP-SIMULATES-THROW_REF-NULL; do
  echo "$t $(steps machine/exit-steps $t)"; done
echo "== certification times"
for b in rules/exits machine/exit-steps machine/machine machine/ok machine/clock0 fast/fast \
         fast/refine-op; do
  echo "$b $(grep -h "^Time:" engine/$b.cert.out | tail -1)"
done
echo "== hints"
for b in rules/exits machine/exit-steps; do
  echo "$b :use $(grep -c ':use' engine/$b.lisp) :cases $(grep -c ':cases' engine/$b.lisp) :expand $(grep -c ':expand' engine/$b.lisp) Subgoal $(grep -c '"Subgoal' engine/$b.lisp)"
done
