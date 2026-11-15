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
| [M5-mode-table](M5-mode-table.md) | M5 item 1 | final (design and core); hand-over list open | Mode table design; what is implemented; measured results; `Heaptype_sub/trans` is not admissible |
| [M6-instruction-typing-strategy](M6-instruction-typing-strategy.md) | M6 item 1 | final; the user chose option C (2026-11-14) | First run of generated 3.0 typing (13 of 23 cases right, 18 after the fix); why subsumption has no mechanical reading; proposer and checker recommended |
| [review-checker-blind-spots](review-checker-blind-spots.md) | cross-cutting; M5 | final for what was reviewed | The termination check cuts valid derivations in the 3.0 type group (9 of 22 cases right); fuel implemented (20 of 22). Config entries reviewed one by one. Silent single choices that no report lists |
| [M7-module-ok-strategy](M7-module-ok-strategy.md) | M7 item 1 | analysis final; strategy awaits the user's decision | The two cycles through the context; with `C` and `C'` given the generated rule compiles with 0 errors; proposer and checker recommended |
