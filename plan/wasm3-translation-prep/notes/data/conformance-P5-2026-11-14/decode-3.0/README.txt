EXPERIMENT (wasm3 prep P5 item 3), not a pipeline: decode every module of the
converted spec-test-3 with the generated 3.0 binary parser.

Setup (scratch tree translate/.probe/exp3/, not in the repo):
- gen/wasm-3.0/ from `make gen SPEC=3.0` at the commit of P5-conformance's update;
- rt/ = translate/rt/ with (in-package "W1T") -> "W3T", rt/cert.acl2 including
  ../gen/wasm-3.0/portcullis, plus stubs3.lisp (the 46 builtins rt/ lacks,
  each returning nil; missing.txt) included from builtins.lisp;
- rt/prelude.lisp: %TRY-LOGIC expands to the :program version and
  %TRY-GUARDS to nothing (logic mode is irrelevant for decoding, and proof
  attempts in 5_2-binary_types ran >15 min);
- cert.pl gen/wasm-3.0/wasm3 (97 s), then `sh decode-all.sh ACL2 8 600`
  with data-path = the wasm3-spec-tests flake output.
Results: TOTALS.txt (by command kind), PER-SCRIPT.txt (name, decoded
commands, mismatches by kind).
