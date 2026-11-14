# Conformance driver: spec-test-1 result, 3.0 data, decode dry run

- Milestone: P5 (item 1: finish wasm1 T7; item 2: parameterize by version,
  assertion values; item 3: spec-test-3 dry run)
- Date: 2026-11-14
- Repo commit: fa5d888 plus this note's commit
- Status: final
- Feeds wasm3 plan: milestones (conformance), risks, probe table
- Incorporated in wasm3 plan: yes (draft plan, §2 (decode), §5 M2, M4, M8, §7)

## Summary

spec-test-1 on the generated 1.0 semantics: **10,848 of 11,606 commands
reached pass** (93.5%), or 10,848 of the 12,014 countable commands (90.3%).
67 scripts were run, each in its own ACL2 session (67 min with 8 in
parallel). 40 pass completely, 2 time out (1 h), and 5 stop on resource
limits. The largest single cause of failures is modules that instantiation
rejects as invalid, in 9 scripts.

spec-test-3 at the pinned rev has 259 scripts. wabt 1.0.41 (`wast2json
--enable-all`) converts 228 of them, with 5,365 modules and 62,383 commands. It
fails on 31: GC 16 of 17, exceptions 3 of 5, memory64 3, bulk-memory 1, and
8 top-level scripts. The cause is missing wabt syntax (`definition`,
`instance`, packed and `rec` types, `exn`). In a decode-only experiment
(scratch `rt/` in `W3T`, missing builtins stubbed) the generated 3.0 parser
decodes 4,562 of 4,639 well-formed modules (98.3%) and rejects 604 of 643
malformed ones.

## Findings

### Item 1: the wasm1 T7 driver

- The uncommitted driver (`t7-spec.lisp`, one book over all scripts) had
  aborted the whole run at the third script: the `binary` script makes the
  generated `GRAM/BLOCALS` recurse once per declared local and exhausts the
  control stack. Restructured, not special-cased:
  - `tests/spec/t7-lib.lisp`: the driver functions (unchanged semantics)
    plus `run-one-script`; every command prints a `T7-CMD kind ok` line as
    it finishes.
  - `run-one.lsp` (one session per script), `run-all.sh` (`xargs -P`,
    `timeout`), `summarize.sh` (per-script pass/run/state, from the
    `T7-CMD` lines, so a crashed script keeps the commands it finished).
  - `make spec` (`SPEC_JOBS` 8, `SPEC_TIMEOUT` 3600 s) writes
    `tests/spec/results/{SUMMARY,TOTAL}`.
- Scripts: spec-test-1 converts to 68 scripts (5 more, `conversions`,
  `f32`, `f64`, `float_exprs`, `float_misc`, use the old NaN assertion syntax
  that `wast2json` rejects). `skip-stack-guard-page` is not run (no
  call-stack limit in the spec semantics). Skipped command kinds:
  `assert_exhaustion` (5) and text-format `assert_malformed` (430).
- Per state (`spec-test-1-SUMMARY.txt`):
  - done, all pass: 40 scripts.
  - done with failures: 20. The modules of `br`, `br_table`, `return`,
    `select`, `unreachable`, `unwind`, `local_get`, `local_set`, `local_tee`
    are rejected as `:INVALID` by `$instantiate`, so all their
    `assert_return`/`assert_trap` fail (578 of the 758 failing commands). Likely cause, not
    checked script by script: the known incompleteness of 1.0 instruction
    typing on stack-polymorphic (dead) code (wasm1 T8, plan W13). Others:
    `linking` 49/111, `imports` 91/131, `utf8-*` 163/176 each (malformed
    UTF-8 accepted), `binary-leb128` 76/81, `func_ptrs` 30/36, `start`
    16/19, `loop`, `memory`, `names` 1 failure each.
  - timeout (1 h): `call` 31/32 and `call_indirect` 76/78 reached. Each
    step costs about 30 ms (W9: `%SIZE` termination checks over byte-list
    memories), and the driver's 3,000-step budget per action makes these
    scripts slow.
  - crashed: `binary` (control stack, too many locals) 47/47 reached,
    `memory_grow` 26/26 and `memory_trap` 13/13 (control stack), `data`
    25/35 and `elem` 20/28 (heap exhausted). All resource limits of the
    list-based runtime (W9), none a wrong answer.
- P6 input: the timeouts and crashes are the runtime baseline's cases.

### Item 2: by version, 3.0 values

- Flake: `mkSpecTests <major> <wast2json flags> <with spectest>`;
  `wasm1-spec-tests` (1.0's flags, unchanged output: the rebuilt data is
  byte-identical to the 2,451 files the driver uses) and
  `wasm3-spec-tests` (`--enable-all`). Scripts in a subdirectory are named
  `DIR--NAME`. `make spec-data SPEC=3.0` copies to `tests/spec/data-3.0/`.
- `gen-spec-tests.mjs`: values `(:V128 :F32 (lane ...))` (lanes as numbers
  or NaN classes), `(:EXTERNREF :NULL|n)`, `(:FUNCREF :ANY)`, `(:I32 :ANY)`
  when the JSON has no value; command `(:ASSERT_EXCEPTION ACTION)`; any
  other value or command becomes `(:UNSUPPORTED "type")` instead of
  aborting the conversion. On spec-test-3 nothing is unsupported, and ACL2
  reads all 62,383 commands back.
- spec-test-3 command mix (converted scripts): `assert_return` 51,894,
  `assert_trap` 3,580, `assert_invalid` 2,442, `module` 1,972,
  `assert_malformed` 1,872, `action` 300, `assert_unlinkable` 188,
  `assert_uninstantiable` 54, `register` 52, `assert_exhaustion` 15,
  `assert_exception` 14. Value types: i32 35,152; v128 lanes 68,666 (f64
  25,399, f32 25,384, i32 6,299, i16 4,083, i64 3,977, i8 3,524); f64
  15,973; f32 15,733; i64 4,478; refs 248.
- Not done: the ACL2 driver for 3.0 values (v128 lanes, references,
  exceptions). It needs a running 3.0 semantics.

### Item 3: spec-test-3 dry run

| Directory | Scripts | Converted | Failed |
|---|---|---|---|
| top level | 97 | 89 | 8 (`annotations`, `instance`, `memory`, `ref_null`, `table`, `type-canon`, `type-equivalence`, `type-rec`) |
| bulk-memory | 8 | 7 | 1 |
| exceptions | 5 | 2 | 3 |
| gc | 17 | 1 | 16 |
| memory64 | 25 | 22 | 3 |
| multi-memory | 41 | 41 | 0 |
| relaxed-simd | 7 | 7 | 0 |
| simd | 59 | 59 | 0 |
| **total** | **259** | **228** | **31** |

- The failures are gaps in wabt: each first error is a parse error at valid
  3.0 syntax. The suite is written for the reference interpreter in the
  pinned spec repo (not built or tried here). Converting with it
  (it can write scripts with binary modules; exact flags to be checked) could recover the GC
  and exception scripts if it parses them (to be checked), at the cost of a
  small `.bin.wast` reader in place of
  `wast2json`'s JSON. That is the recommended route for GC.
- Decode-only pass rate (2026-11-14, an experiment, see
  `data/conformance-P5-2026-11-14/decode-3.0/README.txt`). The generated 3.0
  books were certified in a scratch tree with `rt/` copied into package
  `W3T`, the 46 builtins `rt/` lacks stubbed (`nil`), and all functions in
  `:program` mode. Then `GRAM/BMODULE` ran on every module command of the
  228 scripts:

| Command kind | Modules | Decoded | As expected |
|---|---|---|---|
| `module` | 1,956 | 1,898 | 1,898 |
| `assert_invalid` (well-formed binary) | 2,441 | 2,433 | 2,433 |
| `assert_unlinkable` | 188 | 181 | 181 |
| `assert_uninstantiable` | 54 | 50 | 50 |
| `assert_malformed` (binary; must not decode) | 643 | 39 | 604 |

  - **4,562 of 4,639 well-formed modules decode (98.3%)**; **604 of 643
    malformed ones are rejected (93.9%)**. All 39 wrongly accepted are
    invalid UTF-8 in names (`utf8-*` scripts, 13 each), the same failure as
    in spec-test-1. Misses in decoding: `bulk-memory--table_copy` and
    `memory64--table_copy64` 18 each; the rest are scattered over modules with
    imports, multiple memories and data segments (`PER-SCRIPT.txt`).
    `binary` stops at "too many locals" (control stack), as in 1.0.
  - Caveat: stubbed builtins return `nil` (`$s33_to_u32` among them, which
    block types use), so some misses may come from stubs, not the parser.
  - Translator bug found by this first certification of 3.0 code: aux
    functions of a relation in a rec group can contain the recursive
    premise's size check against the relation's own formals, which the aux
    did not take (`COMPTYPE_SUB/MAP5`: free `%A0 %A1`). Fixed in
    `compile.lisp` (`close-aux-formals`: such an aux gets the formals it
    uses as extra parameters); 1.0 is unchanged.
  - Certification time risk: with the normal `%TRY-LOGIC`/`%TRY-GUARDS`,
    `5_2-binary_types` spent more than 15 CPU minutes in one guard proof
    (`Subgoal 1.101'`) before I stopped it. The prover step limits do not
    bound wall time when single steps are slow. Up to `5_1` the logic-mode
    chain took about 40 s.

## Open questions

- `rt/` package decision (the decode number above comes from a scratch copy).
- Whether to build the reference interpreter in the flake for the GC and
  exception scripts.

## Data

`data/conformance-P5-2026-11-14/`: `convert-spec-test-3.sh` (the
conversion and counts above), `spec-test-3-wast2json-failed.txt` (the 31
failures with wabt's first error), `spec-test-1-SUMMARY.txt` and
`spec-test-1-TOTAL.txt` (from `make spec` at this note's commit),
`spec-test-1-failure-samples.txt`.
