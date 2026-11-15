# WASM 3.0 translation notes

Findings and designs from the milestones of [../plan.md](../plan.md).
Conventions (header, layout, when to write a note, session protocol) are
those of the prep notes:
[../../wasm3-translation-prep/notes/README.md](../../wasm3-translation-prep/notes/README.md).
Raw data goes under `data/<name>/` with the script that made it.

## Index

| Note | Milestone | Status | What it holds |
|---|---|---|---|
| [M0-target](M0-target.md) | M0 | final | 3.0 IL checked in; `make check-3.0` certifies in-tree in :program mode (1 min 32 s); builtins missing in `rt/` as stubs (27); config `:program` and `:memoize :recursive nil` (7 min 6 s without); `%FUEL` irrelevant-formal fix |
| [M0b-test-data](M0b-test-data.md) | M0b | final; one recommendation for M8 open | Reference interpreter in the flake; 259 of 259 spec-test-3 scripts converted (31 via `.bin.wast`); module check; cross-check against wast2json (217 of 228 the same); wabt errors in 9 scripts (`either`, subnormal rounding) |
| [M1-builtins](M1-builtins.md) | M1 | final | `rt/builtins-3.0.lisp` (3.0-only builtins, read for 3.0 only); D4 as the deterministic profile, `$R_*` = V8's choices (arm64); relaxed vectors with two results; `%fma`; `$hostcall` hook; 8,724 + 1,008 vectors, 26 builtin cases |
| [M2-decode](M2-decode.md) | M2 | final (totals corrected in M3); findings for the user | `make decode`: spec-test-3 decodes in-tree (2,266/2,266 modules; 710/712 malformed rejected, 2 crash); wabt compact imports (flake fixed); UTF-8 non-characters (rt/ fixed, 1.0 too); `:il-patch "Belem"`; 1.0: 54 import-section misses open |
| [M3-execution](M3-execution.md) | M3 | final; execution limits moved to M4 | `Step_read/array.new_data-num` (inverse for a middle argument); `:multi` propagation skips `Step`; `:decreasing` path `("Step" 0 2)`: 5.39 → 0.011 ms/step at 1 page; crash containment in the decode driver |
| [M4-conformance](M4-conformance.md) | M4 | final; config kind and entries for the user | 3.0 driver (`t7-lib-3.0`, `make spec SPEC=3.0`); `:il-variant` `$instantiate_unchecked`; spec-test-3: 56,460 of 56,986 `assert_return` + `assert_trap` outside gc/; bugs found: partial inverses, `Ref_ok` size check; what still fails, by cause |
| [M5-subtyping-cases](M5-subtyping-cases.md) | M5 | final (book); the `trans` cases wait | 46 subtyping and validity cases, expected answers from the rules; 35 right, the 11 wrong all need `trans` |
| [M5-trans](M5-trans.md) | M5 | final | `Heaptype_sub/trans` through `HEAPTYPE_SUB/ENUM2` (enumeration variants: collecting searches, on demand in the group); 46 of 46 cases; GC scripts; completeness arguments for the left-out rules |
| [M5-mode-table](M5-mode-table.md) | M5 item 1 | final (design and core); hand-over list open | Mode table design; what is implemented; measured results; `Heaptype_sub/trans` is not admissible |
| [M6-typing-cases](M6-typing-cases.md) | M6 | final; 24 of 24 with the sequencer (M6 strategy note, last section) | 24 function bodies through `EXPR_OK` against V8; 16 agree; the 8 wrong are valid bodies rejected (subsumption, dead code, `br` with a value, an initialized local) |
| [M6-instruction-typing-strategy](M6-instruction-typing-strategy.md) | M6 item 1 | final; the user chose option C (2026-11-14) | First run of generated 3.0 typing (13 of 23 cases right, 18 after the fix); why subsumption has no mechanical reading; proposer and checker recommended |
| [review-checker-blind-spots](review-checker-blind-spots.md) | cross-cutting; M5 | final for what was reviewed | The termination check cuts valid derivations in the 3.0 type group (9 of 22 cases right); fuel implemented (20 of 22). Config entries reviewed one by one. Silent single choices that no report lists |
| [M7-module-ok-strategy](M7-module-ok-strategy.md) | M7 item 1 | analysis final; strategy awaits the user's decision | The two cycles through the context; with `C` and `C'` given the generated rule compiles with 0 errors; proposer and checker recommended |
