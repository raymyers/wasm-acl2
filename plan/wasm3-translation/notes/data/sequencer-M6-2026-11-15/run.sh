#!/bin/sh
# Scratch test of the option C sequencer with step 3 (b) (wasm3 M6). From
# translate/ inside `nix develop ..`:
#   sh ../plan/wasm3-translation/notes/data/sequencer-M6-2026-11-15/run.sh
# Builds .probe/seq with the layout of translate/ (gen, rt, package.lsp,
# tests/sem-3.0 with the t6 book and V8 oracle), translates 3.0 with
# sequencer-b.lsp appended to a copy of config/wasm-3.0.lsp, certifies, and
# prints the T6 line. The real config is not touched.
set -e
D=$(cd "$(dirname "$0")" && pwd)
S=.probe/seq
rm -rf $S && mkdir -p $S/gen/wasm-3.0 $S/tests/sem-3.0
perl -0pe 's/\n\)\n\z/\n/' config/wasm-3.0.lsp > $S/wasm-3.0.lsp
cat $D/sequencer-b.lsp >> $S/wasm-3.0.lsp; echo ")" >> $S/wasm-3.0.lsp
ln -s ../../rt $S/rt; cp package.lsp portcullis.acl2 portcullis.lisp $S/
cp tests/sem-3.0/cert.acl2 tests/sem-3.0/t6-instr-typing-3.0.lisp tests/sem-3.0/typing-oracle-3.0.lsp $S/tests/sem-3.0/
{ echo "(assign il2acl2-target (quote (:version \"3.0\" :pkg \"W3T\" :il \"il/wasm-3.0.il.sexp\" :decls \"il/wasm-3.0.decls.lsp\" :config \"$S/wasm-3.0.lsp\" :outdir \"$S/gen/wasm-3.0/\" :book \"wasm3\")))"; cat il2acl2/run.lsp; } | acl2 > $S/gen.log 2>&1 || { tail -30 $S/gen.log; exit 1; }
$ACL2_SYSTEM_BOOKS/build/cert.pl --acl2 acl2 -j 8 $S/tests/sem-3.0/t6-instr-typing-3.0 > $S/cert.log 2>&1 || { grep -A8 "ACL2 Error" $S/gen/wasm-3.0/*.cert.out $S/tests/sem-3.0/*.cert.out | head -30; exit 1; }
grep -A12 "T6 instruction typing" $S/tests/sem-3.0/t6-instr-typing-3.0.cert.out | head -12
