# How confident are we that a SpecTec-compiled WASM 3.0 semantics will work?

- Milestone: P0 (assessment from the baseline probe)
- Date: 2026-11-14
- Repo commit: 7b513d8
- Status: draft (revise after P1 and after the P5 decoder dry run)
- Feeds wasm3 plan: risks, milestone order (D6)
- Incorporated in wasm3 plan: yes (draft plan, §7 (risks))

## Summary

Fairly confident about execution and decoding, unsure about validation. The
evidence is thin: on 3.0 only the compile phase has run. Likely outcome: a 3.0
semantics that decodes, instantiates and runs real modules, generated almost
entirely from the spec. Main risk: validation ends up partly hand-written or
sound but incomplete, with more counted overrides than the 9 on 1.0.

## Findings

| Part | Confidence | Why |
|---|---|---|
| SpecTec hand-off, IL reading, naming | High | Ran on the full 3.0 source with the stock tool; the only schema failure is 3 text-grammar literals |
| Syntax recognizers, plain functions | High | No type is stubbed; 16 of 462 defs are, from two known causes (function arguments, inverses) |
| Execution (`Step`, instantiate, invoke) | Fairly high | About 10 of 218 reduction rules fail, from gaps with clear fixes. Same mechanism that reached 515/515 against V8 on 1.0 |
| Binary decoder | Medium | All 90 grammars compile, but it has never parsed a 3.0 module. On 1.0, compiling cleanly still hid two real bugs (version bytes, section lengths) |
| Numeric builtins | Medium-high, but it is labour | About 30 new hand-written ones incl. SIMD. V8 is the oracle as before; GC and exceptions have no equally cheap oracle |
| Type validation and subtyping | Low to medium | 13 stubs with root causes not isolated. Some rules (transitive heap subtyping, recursive type indices) are declarative in a way no input/output mode fixes |
| Instruction typing and `Module_ok` | Low for "generated and complete" | Hardest part of 1.0, which ended sound but incomplete with a hand-written `Module_ok`. 3.0: 110 rules vs 31, plus subtyping and local-initialization tracking |
| Passing spec-test-3 at scale | Unknown | Driver unfinished even for 1.0; byte-list memory took 8 s for a 40-iteration loop |

- SpecTec's own interpreter backend uses a hand-written validator, a signal
  that the typing rules are not straightforwardly executable.
- Fallback for execution only: SpecTec's algorithmic form (AL, Strategy B in
  the wasm1 plan) could replace `Step`. There is no such fallback for validation.

## Open questions

- P1 (per-rule gap list) turns "13 typing stubs, cause unknown" into evidence.
  Until then the typing rows are a guess.
- The P5 decoder dry run on spec-test-3 is the first real test of anything 3.0.
