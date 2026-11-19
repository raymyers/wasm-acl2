#!/bin/sh
# Measurements for notes/V7-call-ref.md, read from the certification output
# of fast/call-ref, fast/inv and fast/spec-result. Run at the repository root
# after `make -C engine check`:
#   sh plan/wasm-engine/notes/data/v7-call-ref/measure.sh > plan/wasm-engine/notes/data/v7-call-ref/measure.txt
steps() {  # steps FILE EVENT NAME: prover steps of one event
  awk -v t="$3" -v e="$2" '
    /^Form:/ {if (p) {print "none counted"; exit}
              if ($0 == "Form:  ( " e " " t " ...)" || $0 == "Form:  ( " e " " t) p=1}  # a long name wraps
    p && /^Prover steps counted:/ {print $4; exit}' engine/$1.cert.out
}
for b in fast/call-ref fast/inv fast/spec-result; do
  echo "== prover steps, $b, every defthm, in the order of the book"
  grep -o "^Form:  ( DEFTHM [^ ]*" engine/$b.cert.out | awk '{print $4}' | awk '!seen[$0]++' |
  while read t; do echo "$t $(steps $b DEFTHM $t)"; done
done
echo "== fast/refine-op (certified again: FAST-STEP changed)"
for t in FAST-OP-STEP-REFINES FAST-STEP-REFINES; do echo "$t $(steps fast/refine-op DEFTHM $t)"; done
echo "== certification times"
for b in fast/fast fast/refine fast/refine-mem fast/refine-step fast/refine-hot fast/refine-op fast/ctrl-kinds fast/call-ref fast/inv fast/spec-result; do
  echo "$b $(grep -h "^Time:" engine/$b.cert.out | tail -1)"
done
echo "== hints"
for b in fast/call-ref fast/inv fast/spec-result; do
  echo "$b :use $(grep -c ':use' engine/$b.lisp) :cases $(grep -c ':cases' engine/$b.lisp) :expand $(grep -c ':expand' engine/$b.lisp) :induct $(grep -c ':induct' engine/$b.lisp) Subgoal $(grep -c '"Subgoal' engine/$b.lisp)"
done
echo "== the hypothesis of V6 is gone"
echo "no-call-ref in engine books: $(cat engine/*/*.lisp | grep -c -i 'no-call-ref')"
echo "== trust tags, skip-proofs, defaxiom in the three certificates"
for b in fast/call-ref fast/inv fast/spec-result; do
  echo "$b ttags $(grep -c -i ':ttags' engine/$b.cert) skip-proofs $(grep -c -i 'skip-proofs' engine/$b.cert) defaxiom $(grep -c -i 'defaxiom' engine/$b.cert)"
done
