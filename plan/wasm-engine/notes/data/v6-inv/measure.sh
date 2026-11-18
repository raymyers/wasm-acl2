#!/bin/sh
# Measurements for notes/V6-inv.md, read from the certification output of
# fast/inv and fast/spec-result. Run at the repository root after
# `make -C engine check`:
#   sh plan/wasm-engine/notes/data/v6-inv/measure.sh > plan/wasm-engine/notes/data/v6-inv/measure.txt
steps() {  # steps FILE EVENT NAME: prover steps of one event
  awk -v t="$3" -v e="$2" '
    /^Form:/ {if (p) {print "none counted"; exit}
              if ($0 == "Form:  ( " e " " t " ...)" || $0 == "Form:  ( " e " " t) p=1}  # a long name wraps
    p && /^Prover steps counted:/ {print $4; exit}' engine/$1.cert.out
}
echo "== prover steps, fast/inv, every defthm, in the order of the book"
grep -o "^Form:  ( DEFTHM [^ ]*" engine/fast/inv.cert.out | awk '{print $4}' | awk '!seen[$0]++' |
while read t; do echo "$t $(steps fast/inv DEFTHM $t)"; done
echo "== generated lemmas (one INV-LEMMA line each; INV-FAILED would follow a failed one)"
grep -h "^INV-LEMMA\|^INV-FAILED" engine/fast/inv.cert.out
echo "== prover steps, fast/spec-result"
grep -o "^Form:  ( DEFTHM [^ ]*" engine/fast/spec-result.cert.out | awk '{print $4}' | awk '!seen[$0]++' |
while read t; do echo "$t $(steps fast/spec-result DEFTHM $t)"; done
echo "== certification times"
for b in fast/inv fast/spec-result rules/shape; do
  echo "$b $(grep -h "^Time:" engine/$b.cert.out | tail -1)"
done
echo "== hints"
for b in fast/inv fast/spec-result; do
  echo "$b :use $(grep -c ':use' engine/$b.lisp) :cases $(grep -c ':cases' engine/$b.lisp) :expand $(grep -c ':expand' engine/$b.lisp) :induct $(grep -c ':induct' engine/$b.lisp) Subgoal $(grep -c '"Subgoal' engine/$b.lisp)"
done
echo "== trust tags, skip-proofs, defaxiom in the two certificates"
for b in fast/inv fast/spec-result; do
  echo "$b ttags $(grep -c -i ':ttags' engine/$b.cert) skip-proofs $(grep -c -i 'skip-proofs' engine/$b.cert) defaxiom $(grep -c -i 'defaxiom' engine/$b.cert)"
done
