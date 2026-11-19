# WASM ACL2 Formalization

WebAssembly (Wasm) is a compilation target supported by popular languages including C, C++, Go and Rust. Its official formal semantics is written in the SpecTec DSL.

This repository is an agentic port of the Wasm 3.0 semantics from SpecTec into ACL2, extending the [Kestrel Institute's WASM books](https://github.com/acl2/acl2/tree/master/books/kestrel/wasm). The agents were Claude Code and OpenHands, using the Claude Opus 5.5 and Fable 5.2 models. It passes 99.98% of Wasm's official test suite.

**LLM-use disclosure**: This is agent-generated code. It has not yet been evaluated by qualified researchers. We invite feedback on improvements, so that this experimental port can be refined into a reusable foundation and contributed to the ACL2 community books.

The repository holds two semantics that share no code. The first is generated from SpecTec for WASM 1.0, 2.0 and 3.0, under `translate/` (next section). A verified engine and a browser demo are built on its 3.0 output (sections below). The second is an earlier, agent-written WASM 1.0 formalization at the repository root ([README_WASM1_PORT.md](README_WASM1_PORT.md)).

## Generated from SpecTec: WASM 1.0, 2.0 and 3.0 (work in progress)

`translate/il2acl2/` is a translator, written in ACL2, from SpecTec's elaborated IL to ACL2 definitions. The output in `translate/gen/` is never edited by hand; a small counted config per version (`translate/config/`) holds the exceptions. No theorem connects the output to the SpecTec source: the translator is trusted, and the evidence for correctness is testing.

| Version | State | Main evidence |
|---|---|---|
| WASM 3.0 | Syntax, validation, numerics, execution and the binary format are translated (25 of 37 spec files; the text format and the soundness judgements are not). 25 books, about 349,000 lines, certify with no stubs and no dropped rules; execution (`STEP`, `STEPS`) is in logic mode | **64,005 of 64,018** commands of the official spec-test-3 suite pass (99.98%), through the generated parser, validator, instantiation and step function. None of the 13 failures is a wrong result |
| WASM 2.0 | Certifies with one stub (`Module_ok`); kept as a regression target | 8,724 scalar and 528 SIMD vectors agree with V8; not run against its suite |
| WASM 1.0 | Complete; output is checked in and kept byte-identical across translator changes | spec-test-1: 10,891 of 11,611 commands (last recorded run, [E2 notes](plan/wasm-engine/notes/E2-step-logic.md)) |

```bash
nix develop
make -C translate check        # 1.0: regenerate, compare with the checked-in output, certify, test
make -C translate check-2.0
make -C translate check-3.0    # generate and certify gen/wasm-3.0 (about 5 min), run its test books
make -C translate spec-data spec SPEC=3.0   # the spec-test-3 suite (about 2 hours)
make -C engine check
make -C demo all check
```

Plans and notes, with the measurements behind every number: [wasm1-translation](plan/wasm1-translation/plan.md), [wasm3-translation-prep](plan/wasm3-translation-prep/plan.md), [wasm3-translation](plan/wasm3-translation/plan.md) (evidence for 3.0: [evidence.md](plan/wasm3-translation/evidence.md)), [wasm3-demo](plan/wasm3-demo/plan.md), [wasm-engine](plan/wasm-engine/plan.md).

## Verified engine for WASM 3.0 (work in progress)

`engine/` is a second, faster definition of WASM 3.0 execution in ACL2, with the generated `translate/gen/wasm-3.0` as its specification. It is proved, for a configuration run by the function the drivers call, that the engine follows that specification or stops, and that a result of the engine is the specification's result. Host calls are outside: the engine stops at one. [engine/THEOREM.md](engine/THEOREM.md) is a guide for inspecting the theorems; [evidence.md](plan/wasm-engine/evidence.md) states what is proved, what is only tested, and what is neither. `make -C engine check` certifies every engine book and fails if one contains `skip-proofs` or `defaxiom`. It needs `make -C translate check-3.0` first. Plans: [plan.md](plan/wasm-engine/plan.md), [plan2.md](plan/wasm-engine/plan2.md).

The engine's target workload is the workshop talk's slides: `make -C engine slides` renders them with a bitmap renderer and compares each slide with V8, inside the theorem, and [engine/tex/](engine/tex/README.md) runs TeX (`tex.wasm`) to typeset the deck (not part of `check`; outside the theorem, since TeX calls host functions). The LaTeX source of the talk is `latex-slides/`.

## Browser demo

`demo/` runs WASM 3.0 modules in the browser with the generated semantics, compiled to JavaScript through JSCL, and shows each reduction step with the spec rules behind it. Build and checks: [demo/README.md](demo/README.md).

## Initial agentic WASM 1.0 formalization

The files at the repository root (`execution.lisp`, `validation.lisp`, `proofs/`, `tests/`) are a WASM 1.0 semantics written by a coding agent on top of the Kestrel WASM books: 170 of 170 instructions, 45 certified books (27 proof books, 15 test books), tested against Node.js as an oracle. `make` (or `nix build`) certifies it.

Status, instruction coverage, files, build commands, design decisions and remaining work: **[README_WASM1_PORT.md](README_WASM1_PORT.md)**.
