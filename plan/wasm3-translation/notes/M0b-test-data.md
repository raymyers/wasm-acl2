# Test data for GC and exceptions: the reference interpreter as a converter

- Milestone: M0b (items 1 and 2)
- Date: 2026-11-14
- Repo commit: 24ac93a plus this note's commit
- Status: final; one recommendation for M8 is open (the user decides)
- Feeds wasm3 plan: §5 M0b (done), M5-M8 (GC test data), M8

## Summary

**259 of 259** spec-test-3 scripts are now converted (228 before). The
flake builds the reference interpreter of the pinned spec
(`.#wasm-ref-interp`, the native `wasm` executable, about 10 s). For each
script that `wast2json` cannot read, it runs `wasm -d S.wast -o S.bin.wast`.
That rewrites the script with every module in binary form.
`gen-spec-tests.mjs` reads the `.bin.wast` into the same command objects
as wast2json's JSON, so the output has the same format: `NAME.lsp` command
lists and `NAME.k.wasm` modules, in one `index.lsp`. All 31 scripts that
wabt skipped convert this way, among them **16 of 17 GC** and **3 of 5
exception** scripts (the remaining GC and 2 exception scripts were
already converted by wabt). The new list is `REFINTERP` in the flake
output; `SKIPPED` is now empty, so it is not written.

Checked:
- **The modules are right.** All 293 distinct module files instantiated by
  the 31 scripts validate with the reference interpreter. All 290
  `assert_invalid` modules are rejected by it (`validate.sh`).
- **The reader agrees with wast2json.** The 228 scripts that wabt reads
  were converted a second time through the interpreter (`xcheck.sh`). After
  normalizing representation-only differences (`norm.mjs`), **217 of 228
  give the same commands**. Of the other 11, 10 are wabt errors (below),
  and in 1 the interpreter's rewrite loses information: `inline-module`, a
  script made of bare module fields, comes out with no instantiation.
- **The existing data is unchanged.** The 1.0 data is identical to
  `translate/tests/spec/data`. Every file of the old 3.0 output is
  byte-identical; the new output only adds the 31 scripts and drops `SKIPPED`.

## What the 31 scripts hold

`counts.txt` (from `counts.sh`), commands by kind:

| Group | Scripts | assert_return | assert_trap | module | assert_invalid | other |
|---|---|---|---|---|---|---|
| core | 8 | 107 | 2 | 80 | 52 | register 11, assert_unlinkable 2 |
| exceptions | 3 | 47 | 2 | 11 | 11 | assert_exception 4, register 3, assert_unlinkable 2 |
| gc | 16 | 453 | 128 | 98 | 77 | action 20, register 12, assert_unlinkable 8 |
| memory64 | 3 | 166 | 634 | 64 | 83 | action 21, register 1 |
| bulk-memory | 1 | 81 | 584 | 41 | 67 | action 18, register 1 |
| **total** | **31** | **854** | **1,350** | **294** | **290** | 103 |

The interpreter's rewrite drops the text-only commands. In these 31
scripts there are 73 `assert_malformed` of `module quote`, all text format
(out of scope, D3). It writes every `assert_invalid` module in binary, even
those that wabt keeps as `.wat` (e.g. `address.1.wat`).

## Format additions

The value forms that only the new scripts use are documented in the
header of `gen-spec-tests.mjs`:
- GC references as `(:I31REF :ANY)`, `(:STRUCTREF :ANY)`,
  `(:ARRAYREF :ANY)`, `(:EQREF :ANY)`;
- typed nulls `(:ANYREF :NULL)`, `(:NULLREF :NULL)`, `(:NULLFUNCREF :NULL)`,
  `(:EXNREF :NULL)`, ...;
- a bare `(ref.null)` (any null) as `(:REF :NULL)`;
- `(ref.host n)` as `(:HOSTREF n)`;
- `either` results as `(:EITHER (VAL...))`.

Commands: `(module definition ...)` writes a file but no command;
`(module instance $I? $D?)` becomes `(:MODULE FILE NAME)`, with the file
of the named (or last) definition. `(assert_trap (module instance) ...)`
becomes `:ASSERT_UNINSTANTIABLE`, as wabt's does. Float literals are
converted exactly from the interpreter's hex form, and an inexact one is
an error.

## wabt's data has wrong expectations in 9 scripts (for M8)

Found by the cross-check, in data that was already converted:
- **`either` results are lost.** wabt writes the expected results as `()`
  for every `assert_return` with `either`: 6 relaxed-SIMD scripts and
  `memory64--memory_grow64`, `memory64--table_grow64`. A driver would
  check that they return nothing. The interpreter path keeps
  `(:EITHER ...)`.
- **Subnormal rounding.** In `simd--simd_lane`, `0x1.fffffffffffffp-1023`
  needs 53 bits as an f64 subnormal and rounds (to nearest even) to
  `0x1p-1022`. wabt truncates to `0x0.fffffffffffffp-1022` (4 asserts,
  bit pattern off by one). The interpreter prints `0x1p-1022`.
- Representation only, harmless: an untyped `(ref.null)` result is typed
  by wabt (`(:FUNCREF :NULL)`), and `(ref.func)` becomes `(:FUNCREF 0)`
  where any function reference is meant.

**Recommendation (for the user, M8):** convert every script through the
reference interpreter, and keep wast2json only for `inline-module` (or
drop that one script). It is the test suite's own tool. It agrees on 217
of 228 scripts and is right in 10 of the other 11. M0b did not change the
routing of the 228 scripts, because the item asks only for the ones that
wast2json cannot read.

## Data

`data/spec-test-3-M0b-2026-11-14/`: `counts.sh` and `counts.txt` (the
table above); `validate.sh` and `validate.txt` (the module check); `xcheck.sh` and `norm.mjs` (the cross-check), with
`xcheck-differ.txt` (the 11 differing scripts, first diff lines).
