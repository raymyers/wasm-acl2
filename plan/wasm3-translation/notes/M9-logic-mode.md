# 3.0 in logic mode with time limits; the 3.0 mode manifest

- Milestone: M9
- Date: 2026-11-15
- Status: final
- Feeds wasm3 plan: §5 M9 (exit met), §6, "Current state"

## Summary

The config entry `:program` (M0) is replaced by `(:logic "time-limited
attempts" :seconds 20)`. Every generated 3.0 event goes through
`%TRY-LOGIC-T` / `%TRY-GUARDS-T` (`rt/builtins-3.0.lisp`). These make the
same attempts as 1.0's `%TRY-LOGIC` / `%TRY-GUARDS` (step limits and the
measure alternatives), and each attempt also runs under
`with-prover-time-limit 20`. An attempt that runs out of time falls back,
the same as one that fails.

The tests for this run are below; the logs are in `data/modes-M9-2026-11-15/`.

| | |
|---|---|
| Certification of `gen/wasm-3.0`, `-j 8` | **4 min 38 s** (`:program` mode: 1 min 32 s; before M9, one guard proof ran over 15 min) |
| Slowest book | `5_3-binary_instructions`, 118 s |
| Attempts stopped by the time limit | 4, in 3 decoder books: `GRAM/BINSTR/REP32`, `GRAM/BRECTYPE/REP9`, `GRAM/BTYPESEC/REP17` (`time-limit-hits.txt`) |
| Mode manifest `tests/sem-3.0/modes-3.0.lsp` | **:guards 429, :logic 692, :program 288** (1,409 functions) |
| `make check-3.0` (with `t0-modes-3.0`) | 4 min 45 s; T3/T5/T6 unchanged; stubs 0; `:MODES-MATCH-MANIFEST` |
| spec-test-3 on the logic-mode code | 63,324 / 63,880; `module` 2,263/2,263; `assert_invalid` 2,683/2,690; 11 min 18 s |

The spec-test-3 count matches M7's (63,326 / 63,883) except for `call`.
That script is at the per-script time limit in both modes: it also timed
out in the `:program` run 7c of M7, and it finished in the final M7 run.

## Mode manifest

The manifest has the same format as 1.0's. It is written by `make modes SPEC=3.0`
(`tests/sem-3.0/modes-write-3.0.lsp`). The test book
`tests/sem-3.0/t0-modes-3.0.lisp` is part of `check-3.0` and fails when the
certified modes differ from it. Variants made on demand are included: 19
entries for `INSTR_OK/OUT2`, `HEAPTYPE_SUB/ENUM2` and `DEFTYPE_SUB/ENUM2`.
`modes-lib` now finds defuns inside `%TRY-LOGIC-T` as well.

The 288 program-mode functions are concentrated in a few parts:
`2_1-validation_types` 64, `1_2-syntax_types` 60, `2_4-validation_modules` 27,
`1_4-syntax_modules` 25, `2_3-validation_instructions` 25,
`5_4-binary_modules` 21. By name (`program-functions.txt`): 96 are type
substitution, rolling and free-variable functions (`$subst_*`, `$free_*`,
`$rollrt` ...) over the mutually recursive type syntax; 132 are relations
(`*_OK`, `*_SUB`, `STEP`, `/W`); 30 are decoder grammar functions
(`GRAM/`); 9 are hand-written (sequencer, proposer); the rest are other
functions. Getting these into logic mode needs measures for the type group,
which D3 leaves out.

**Caveat.** With a wall-clock limit, the result depends on the machine.
The manifest records what this machine (darwin, 8 jobs) gives. On a slower
machine, an attempt that passes here can fall back, and `t0-modes-3.0`
would then report it.
