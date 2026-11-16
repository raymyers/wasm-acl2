# WASM ACL2 Formalization

A machine-checked formalization of the WASM operational semantics in ACL2, extending the [Kestrel Institute's WASM books](https://github.com/acl2/acl2/tree/master/books/kestrel/wasm).

**AI-use disclosure**: This is agent-generated code. It has not yet been evaluated by qualified researchers.

This repository holds two separate artifacts that share no code: semantics **generated from the SpecTec specification** for WASM 1.0, 2.0 and 3.0 under `translate/` (next section), and an earlier, agent-written WASM 1.0 formalization at the repository root ([README_WASM1_PORT.md](README_WASM1_PORT.md)).

## Generated from SpecTec: WASM 1.0, 2.0 and 3.0 (work in progress)

`translate/il2acl2/` is a translator, written in ACL2, from SpecTec's elaborated IL to ACL2 definitions. The output in `translate/gen/` is never edited by hand; a small counted config per version (`translate/config/`) holds the exceptions. No theorem connects the output to the SpecTec source: the translator is trusted, and the evidence for correctness is testing.

| Version | State | Main evidence |
|---|---|---|
| WASM 3.0 | Syntax, validation, numerics, execution and the binary format are translated (25 of 37 spec files; the text format and the soundness judgements are not). 25 books, about 349,000 lines, certify with no stubs and no dropped rules; execution (`STEP`, `STEPS`) is in logic mode | **64,005 of 64,018** commands of the official spec-test-3 suite pass (99.98%), through the generated parser, validator, instantiation and step function. None of the 13 failures is a wrong result |
| WASM 2.0 | Certifies with one stub (`Module_ok`); kept as a regression target | 8,724 scalar and 528 SIMD vectors agree with V8; not run against its suite |
| WASM 1.0 | Complete; output is checked in and kept byte-identical across translator changes | spec-test-1: 10,891 of 11,611 commands (last recorded run) |

```bash
nix develop
make -C translate check        # 1.0: regenerate, compare with the checked-in output, certify, test
make -C translate check-2.0
make -C translate check-3.0    # generate and certify gen/wasm-3.0 (about 5 min), run its test books
make -C translate spec-data spec SPEC=3.0   # the spec-test-3 suite (about 2 hours)
make -C engine check
make -C demo all check
```

Plans and notes, with the measurements behind every number: [plan/](plan/) (`wasm1-translation`, `wasm3-translation-prep`, `wasm3-translation`, `wasm3-demo`, `wasm-engine`).

## Initial agentic WASM 1.0 formalization

The files at the repository root (`execution.lisp`, `validation.lisp`, `proofs/`, `tests/`) are a WASM 1.0 semantics written by an AI agent on top of the Kestrel WASM books: 170 of 170 instructions, 45 certified books (27 proof books, 15 test books), tested against Node.js as an oracle. `make` (or `nix build`) certifies it.

Status, instruction coverage, files, build commands, design decisions and remaining work: **[README_WASM1_PORT.md](README_WASM1_PORT.md)**.
