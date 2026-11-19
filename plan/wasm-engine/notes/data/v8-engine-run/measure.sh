#!/bin/sh
# Measurements for notes/V8-engine-run.md, read from the certification output
# of run and fast/stretch. Run at the repository root after
# `make -C engine check`:
#   sh plan/wasm-engine/notes/data/v8-engine-run/measure.sh > plan/wasm-engine/notes/data/v8-engine-run/measure.txt
steps() {  # steps FILE EVENT NAME: prover steps of one event
  awk -v t="$3" -v e="$2" '
    /^Form:/ {if (p) {print "none counted"; exit}
              if ($0 == "Form:  ( " e " " t " ...)" || $0 == "Form:  ( " e " " t) p=1}  # a long name wraps
    p && /^Prover steps counted:/ {print $4; exit}' engine/$1.cert.out
}
for b in run fast/stretch; do
  echo "== prover steps, $b, every defthm, in the order of the book"
  grep -o "^Form:  ( DEFTHM [^ ]*" engine/$b.cert.out | awk '{print $4}' | awk '!seen[$0]++' |
  while read t; do echo "$t $(steps $b DEFTHM $t)"; done
done
echo "== certification times"
for b in run fast/stretch; do
  echo "$b $(grep -h "^Time:" engine/$b.cert.out | tail -1)"
done
echo "== hints"
for b in run fast/stretch; do
  echo "$b :use $(grep -c ':use' engine/$b.lisp) :cases $(grep -c ':cases' engine/$b.lisp) :expand $(grep -c ':expand' engine/$b.lisp) :induct $(grep -c ':induct' engine/$b.lisp) Subgoal $(grep -c '"Subgoal' engine/$b.lisp)"
done
echo "== trust tags, skip-proofs, defaxiom in the two certificates"
for b in run fast/stretch; do
  echo "$b ttags $(grep -c -i ':ttags' engine/$b.cert) skip-proofs $(grep -c -i 'skip-proofs' engine/$b.cert) defaxiom $(grep -c -i 'defaxiom' engine/$b.cert)"
done
echo "== modes of the spec functions a driver calls (symbol-class; :program is outside a theorem)"
echo "see modes.txt (modes.lsp)"
