# `Module_ok` by proposer and checker; validation on spec-test-3

- Milestone: M7 (items 2-4), and the spec-test-3 run of M8
- Date: 2026-11-15
- Repo commit: c80d2e8 plus this note's commit
- Status: final
- Feeds wasm3 plan: §5 M7 (exit met), M8, §6, "Current state"

## Summary

**User decision (2026-11-15): proposer and checker.** `Module_ok` is
compiled in mode `(:given "C" "C'")` to `MODULE_OK/W`, which checks
every premise of the rule, including its own equations for the two
contexts. A hand-written entry `MODULE_OK (module)` proposes `C'` and `C`
(new config kind `:given-entry`, reason in the config). **3.0 has no stub
in the D3 scope.** `$instantiate` validates again. The test-only
`$instantiate_unchecked` (`:il-variant`) is removed, and the conformance
driver uses `$instantiate`, so `assert_invalid` is checked.

`make spec SPEC=3.0` (`TOTAL.txt`):

| Kind | Pass / counted |
|---|---|
| `module` (valid modules accepted) | **2,263 / 2,263** |
| `assert_invalid` | **2,683 / 2,690** |
| `assert_unlinkable` | **200 / 200** (16 before: import types are now matched) |
| `assert_uninstantiable` | 54 / 54 |
| `assert_malformed` (binary) | 710 / 710 |
| `assert_exception` | 18 / 18 |
| `assert_trap` | 4,924 / 4,924 |
| `assert_return` | 52,117 / 52,643 |
| `action` | 357 / 357 |
| all | **63,326 / 63,883** |

`assert_return` + `assert_trap` outside `gc/`: 56,460 of 56,986, the same
as without validation (M4). The 7 `assert_invalid` misses are data, not
validation (`assert-invalid-misses*.txt`): 3 modules that wabt kept as
text (`address.1.wat`, `simd_address.5/6.wat`; there is no binary to
check) and the 4 binaries without the data count section of M2 (the
reference interpreter refuses to decode them too).

## Translator and config work

- **`:given-entry`** (config kind): the relation compiled in a
  `(:given ...)` mode to `R/W`, followed by the hand-written entry `R`,
  which callers see with the `:fun` interface. The proposer is about 45
  lines: types by `Types_ok`, import types by `Import_ok`, the five `$..xt`
  projections, `x*` by `$funcidx_nonfuncs`, tags, globals, memories and
  tables by their generated relations, and `dt*` (`C.TYPES[x]`), `ok*`,
  `rt*` read off the syntax.
- **Bugs found by running it** (each fixed):
  1. `Types_ok` and `Globals_ok` recurse under a context that grows by the
     new types or globals, so the generated size check cut every list of
     two or more. No module with a type validated (found on the spectest
     module). Fix: `("Types_ok" . 1)`, `("Globals_ok" . 1)` in
     `:decreasing`, the M4 `Ref_ok` blind spot again.
  2. An equation with a variable-free option, `C.LABELS[l] = t* (REF
     NULL? ht)` (`br_on_non_null`), was compiled as an expression
     equality, where `NULL?` always gives `NULL`. Now that side is
     matched as a pattern (`varfree-opt-p`, translator). 1.0 is unchanged.
  3. The sequencer (M6): after a stack-polymorphic instruction the stack
     stays polymorphic for the rest of the sequence; `ref.test` and
     `ref.cast` take the top of the cast type's hierarchy; `ref.is_null`,
     `ref.as_non_null` and `br_on_null` take the nullable form; the
     conversions take `any`/`extern` with the operand's nullability;
     `br_table` takes its operands from the stack (`bot` where it is
     empty); and `return_call_ref` / `return_call_indirect` have table
     entries. Rejected valid modules went from 40 to 0 in four runs. The
     24 V8 cases stay 24/24.
  4. `spectest` lacked `table64`; the 3.0 data now builds `spectest-3.0.wat`.
     The 1.0 data is unchanged.
  5. A config that does not read (a paren too many) made `make gen` print
     "regenerated" over stale output. `gen` now fails on a raw Lisp error
     in its log.

## Data

`data/module-M7-2026-11-15/`: `TOTAL.txt`, `SUMMARY.txt`,
`FAILKINDS.txt` (the final run), `runA-*` (the first run with
validation: 40 valid modules rejected), `assert-invalid-misses*.txt`,
`trace.lsp` (debug aid: the first instruction the sequencer rejects in
each function, inside blocks too), `traces-after.txt`.
