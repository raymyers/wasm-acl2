# Instantiation and invocation: the 3.0 driver and spec-test-3

- Milestone: M4 (items 1-3)
- Date: 2026-11-15
- Repo commit: 3e753c2 plus this note's commit
- Status: final; one new config kind and two entries for the user
- Feeds wasm3 plan: §5 M4 (done), M7, M8, §6, §7

## Summary

`make spec SPEC=3.0` runs every spec-test-3 script (258; not
`skip-stack-guard-page`) on the generated 3.0 semantics: 8 sessions,
**10 min 37 s**. Results (`TOTAL.txt`):

| Kind | Pass / counted |
|---|---|
| `assert_return` | **52,106 / 52,643** |
| `assert_trap` | **4,924 / 4,924** |
| `assert_exception` | 18 / 18 |
| `action` | 357 / 357 |
| `module` | 2,262 / 2,263 |
| `assert_malformed` (binary) | 710 / 710 |
| `assert_uninstantiable` | 54 / 54 |
| `assert_unlinkable` | 16 / 200 (no import type check, see below) |
| commands that aborted (resource limits) | 24 |
| **all** | **60,447 / 61,193** |

**Exit metric: `assert_return` + `assert_trap` outside `gc/`: 56,460 of
56,986 (99.1%).** Skipped and not counted: `assert_invalid` (needs
`Module_ok`, M7), `assert_exhaustion` (no call-stack limit in the spec),
text-format `assert_malformed`.

Three bugs were found by running the suite and are fixed (two in the
translator, one config entry). The first run had **50,725 of 56,990**
for the same metric (`run1-*`; its summary also miscounted aborts).

## How instantiation works without `Module_ok` (item 1)

`$instantiate` has two premises: `Module_ok` (a stub until M7, which
signals an error) and `Externaddr_ok` on the import addresses, which
needs `Module_ok`'s import types. Decision D6 asks for a test-only path.
**New config kind `:il-variant`** (`emit.lisp`, an IL pre-pass after
`:il-patch`): a copy of a def under a new name, without the premises on
the named relations. The new 3.0 entry generates
`$instantiate_unchecked` (reason in the config). `$instantiate` is
unchanged. Only the driver uses the variant, so modules are not
validated and imports match by name only. That is why 184 of 200
`assert_unlinkable` fail: a type mismatch goes undetected. Remove the
entry once M7 translates `Module_ok`.

## The driver (items 2 and 3)

`tests/spec/t7-lib-3.0.lisp`, `run-one-3.0.lsp`, `run-all-3.0.sh`,
`summarize-3.0.sh`, adapted from the 1.0 driver:
- **Values:** v128 by lanes (`(:V128 :F32 (...))`, NaN classes per
  lane); references `REF.NULL_ADDR`, `REF.I31_NUM`, `REF.STRUCT_ADDR`,
  `REF.ARRAY_ADDR`, `REF.FUNC_ADDR`, `REF.EXN_ADDR`, `REF.HOST_ADDR`.
  wast's `(ref.extern n)` is `REF.EXTERN (REF.HOST_ADDR n)` and
  `(ref.host n)` is `REF.HOST_ADDR n`. `either` results and uncaught
  exceptions (`(REF.EXN_ADDR a) THROW_REF`) are handled.
- **Execution limits:** 200,000 steps per action or instantiation
  (`:FUEL`). Each command is its own top-level form (`ld ...
  :ld-error-action :continue`): a command that exhausts a Lisp resource
  aborts alone and is counted as failed (kind CRASH), and the script
  goes on with the state from before. The 24 aborted commands are
  `memory.grow` / `table.grow` by many pages (14), "too many locals" (2),
  deep recursion (`call_ref`, `local_tee`, 2), `memory_trap` and
  `multi-memory--memory_trap0` (2), the `test` action of `memory_copy`
  and `memory_copy64` (2, see below), and the last command of `call` and
  `call_indirect`, killed at the time limit (2) (`ABORTED.txt`).
  `timeout -k 30`: the `acl2` wrapper starts SBCL as a child, and an ACL2
  session does not stop on TERM while it computes. Without `-k` the first
  run had to be stopped by hand.
- **Data:** the flake now also builds `spectest.wasm` for 3.0 (the 1.0
  `spectest.wat`).

## Bugs found by the run (fixed)

1. **Partial inverse functions (translator).** `$inv_isize` is
   `hint(partial)`, and the IL gives it the result type `Inn?`. The
   inverse binding of `cpat` bound the option `((:I32))` instead of its
   element, so every equation solved through it failed. That covered
   float vector comparisons (`$fvrelop_`: all of `simd_f32x4_cmp` and
   `simd_f64x2_cmp`, 5,240 asserts) and the SIMD loads and stores with
   lanes, splats and extends (all of `simd_load_splat`, `load_extend`,
   `load*_lane`, `store*_lane`). Fix: when the inverse def returns an
   option (new `:opt-defs` from the IL), the binding takes its element
   and requires one. 1.0 output is unchanged (byte-identical; the extra
   fresh name is allocated only for a partial inverse).
2. **`Ref_ok` cut by the size check (config).** The output variant
   `Ref_ok/SPLIT` calls the check variant with the known type `REF ANY`
   as a third input (`Ref_ok/extern`). That made the callee's inputs
   larger than the caller's, so the generated check cut the rule. No
   externref had a type, and `$invoke` rejected every externref
   argument (`table_fill`, `table_set`, `elem`, `ref_test`, `extern`,
   ...). Fix: `("Ref_ok" . 1)` in the 3.0 `:decreasing` entry. The
   reference strictly shrinks in `extern` and stays equal in `sub`,
   where all inputs then shrink. This is the blind spot of
   review-checker-blind-spots, outside the fuel group: only behavioural
   runs find it.
3. **Summary miscount (driver).** `register` prints no `T7-CMD`, and
   nested `ld` prompts are `!>>`. The summary first counted 104 aborts;
   the real number is 24.

## What still fails, by cause (`FAILKINDS*.txt`)

Outside `gc/` (526 of 56,986 `assert_return` + `assert_trap`):
- **446** in `memory_copy` and `memory_copy64` (223 each): `checkRange`
  after a `test` action that aborted. `test` does 200 `memory.fill` /
  `memory.copy` of thousands of bytes, about 2-3 steps per byte, and the
  state stays as before. In the driver the action aborts. Run alone in a
  session it did not finish within 15 min, so the exact resource is not
  pinned down. Small overlapping copies and fills are correct, checked
  directly. A resource problem of byte-by-byte copying on lists, not a
  semantic one as far as checked.
- **43** step budget (`:FUEL`): `return_call*` with a count of
  1,000,000, `memory_fill`/`memory_copy` loops, `memory_grow` loops,
  `call_ref`.
- **33** relaxed SIMD (`relaxed_min_max`, `madd_nmadd`, `laneselect`,
  `dot_product`, `swizzle`, `q15mulr`): wabt wrote these scripts'
  `either` results as `()` (M0b), so the data is wrong, not the
  semantics. The M0b recommendation (convert through the reference
  interpreter) would fix them.
- **4** wrong results after an aborted grow (`memory_grow`,
  `memory_grow64`, `table_grow64`).

In `gc/` (not in the exit metric): 7 wrong results in `ref_test` and 4
traps in `ref_cast` / `type-subtyping`, from subtyping that needs
`Heaptype_sub/trans` (M5); 8 `assert_unlinkable`.

## Data

`data/conformance-M4-2026-11-14/`: `TOTAL.txt`, `SUMMARY.txt` (per
script), `FAILKINDS.txt`, `FAILKINDS-per-script.txt`, `ABORTED.txt`; and
`run1-TOTAL.txt`, `run1-SUMMARY.txt` (the first run, before the fixes;
its abort count is wrong, see bug 3). Made by `make spec SPEC=3.0` (`summarize-3.0.sh`) and `lists.sh`
(the per-script classes and the aborted commands).
