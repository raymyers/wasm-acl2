wasm3 M6 step 2: a test of :rel-override for a member of a rec group.
test-entry.lsp is appended to a scratch copy of config/wasm-3.0.lsp (a
trivial Instrs_ok override: one instruction, checked by INSTR_OK). The
translator writes .probe/ov/gen/wasm-3.0 (target :config and :outdir
pointing there; rt and package.lsp beside it), 2_3-validation_instructions
certifies with INSTRS_OK inside the group's mutual recursion, and
check.lsp (run in that gen directory) prints OV (T NIL NIL): one add
accepted, two nops rejected (the stand-in takes one instruction only), a
block rejected (Instr_ok/block passes x* unbound: step 3).
