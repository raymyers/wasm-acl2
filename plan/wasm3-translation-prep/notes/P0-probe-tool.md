# The probe as a make target; G7 and wide grammar literals fixed

- Milestone: P0 (all three items: `make -C translate probe SPEC=3.0`; fix G7;
  schema accepts grammar character codes wider than one byte)
- Date: 2026-11-14
- Repo commit: 653f435 plus this note's commit (the measurements below were
  taken on the working tree that became that commit)
- SpecTec: `WebAssembly/spec@943c5df` (the flake pin)
- Status: final
- Feeds wasm3 plan: probe table, gap list
- Incorporated in wasm3 plan: yes (draft plan, §2 (probe table), §8 notes)

## Summary

`make -C translate probe SPEC=<v>` reproduces the plan §1 numbers for 1.0, 2.0
and 3.0 in one command each (about 13 s for 3.0), with no skip list and no
change under `gen/`. After the two fixes, 3.0 has **0 schema errors** (was 3)
and the translator **no longer crashes**: 111 stubs (the 110 of the baseline
plus the zero-arity relation, now a clean stub). With the D3 scope
(`EXCLUDE='X.* 6.* 7.*'`) 3.0 has **35 stubs**. 1.0 passes `make check`
byte-identically.

## Findings

### The tool

- `translate/Makefile` target `probe`; variables `SPEC` (default 3.0),
  `EXCLUDE` (file globs), `PROBE_CONFIG`, `PROBE_DROP` (config kinds to
  ignore: `:rel-override :il-patch` for every version except 1.0, as in the
  baseline).
- It runs the pinned SpecTec from the flake on
  `specification/wasm-<v>/*.spectec` of the pinned source, into
  `translate/.probe/<v>/` (git-ignored): `wasm-<v>.il.sexp`, `names.lsp`,
  `run.lsp`, `acl2.log`, `report.txt`, `errors.lsp`.
- `translate/il2acl2/probe.lsp`: schema check and mangling (the parts of
  `il-check`, called directly so they do not stop at the first failure),
  IL statistics (§1.1), translator phase 1 (`cforms` with the context
  `gen-phase1` builds), then the report. The report has no timings, so it is
  a deterministic function of the IL and the config and can be diffed.
- `translate/il2acl2/probe-names.sh`: maps every `syntax`/`def`/`relation`/
  `grammar` declaration to its source file, so stubs are grouped by file
  (the "cluster" column of §1.2) without a hand-written, version-specific
  table. A stub maps to its IL id through the inverse of the mangle table.

### G7: zero-arity relation

- Cause: `relation NotationTypingPremisedots: ...` has the empty tuple, so
  arity 0. In `:fun` mode `crel-1` asked `gsyms-prefixed` for `(1- 0) = -1`
  formals; `zp` in raw Lisp does not stop at negative numbers, so it recursed
  until the control stack ran out.
- Fix (`compile.lisp`, `crel-1`): arity 0 logs "relation with an empty tuple
  (arity 0)" in every mode, and `rel-stubs` uses `(nfix (1- n))`. The
  relation becomes a stub with zero formals.
- 3.0 has **two** relations with no rules: `NotationTypingPremisedots`
  (arity 0) and `NotationTypingPremise` (arity 1, compiles: an always-false
  predicate). Both are in `X.2`.

### Schema: grammar literals

- `schema.lisp`: `hexbyte-p` (exactly `0xNN`) became `hexcode-p`: `0x`
  followed by 2 to 6 hex digits, which covers Unicode code points up to
  `0x10FFFF`. The compiler (`csym`) already compares a literal as an integer
  with the input element, so nothing else changed.
- 3.0 schema errors: 3 → 0. 1.0 and 2.0: 0 → 0.

### Reproduced numbers

All of plan §1.1 and §1.2 that the baseline measured, except the
`hint(inverse)` counts (hints are not in the IL; P3), match exactly.
Corrections and details the baseline did not have:

| | Plan §1 said | Probe |
|---|---|---|
| 3.0 `.spectec` files | 39 | **37** (lines 9,353 as stated) |
| 1.0 phase-1 events | 473 (W7) | 477 = 473 `%TRY-LOGIC` events in `gen/wasm1.lisp` + 4 `memoize` events: both right, they count different things |
| 2.0 clause-less defs | (63 `hint(builtin)`) | 64 |
| 2.0 rules: `Instr_ok` / `Step_pure` / `Step_read` / `Step` | not measured | 74 / 56 / 47 / 23 |
| 2.0 defs with type parameters | not measured | 8 (0 with function parameters) |
| 3.0 stubs | 110 + crash | 111, no crash (1,080 errors = 1,079 + the G7 error) |
| 3.0 dropped split-variant rules, all attempts | not counted | 61 |

### 3.0 with the D3 scope

`make probe SPEC=3.0 EXCLUDE='X.* 6.* 7.*'`: 25 files, 7,008 lines, 758
top-level forms, 509 rules in 85 relations, 89 clause-less defs, 87 binary
grammars, 0 schema errors, 993 events, **35 stubs**, 249 errors:

| File | Stubs |
|---|---|
| 2.1-validation.types | 11 (`Deftype_sub` and `Comptype_sub` are declared here, defined in 2.2) |
| 2.2-validation.subtyping | 2 |
| 2.3-validation.instructions | 2 |
| 2.4-validation.modules | 1 |
| 3.2-numerics.vector | 13 |
| 4.3-execution.instructions | 3 |
| 4.4-execution.modules | 2 |
| 5.1-binary.values | 1 (`$utf8single`) |

## Open questions

- Error attribution is still per function and from the `:fun` attempt (W3);
  that is P1.
- `probe-names.sh` matches only declarations at the start of a line. Every
  stub of 1.0, 2.0 and 3.0 was attributed to a file, so none is missed today.

## Data

`data/probe-P0-2026-11-14/` (from `translate/`, inside `nix develop ..`):

| File | Command |
|---|---|
| `report-1.0.txt` | `make probe SPEC=1.0` |
| `report-2.0.txt`, `errors-2.0.lsp` | `make probe SPEC=2.0` |
| `report-3.0.txt`, `errors-3.0.lsp` | `make probe SPEC=3.0` |
| `report-3.0-core.txt` | `make probe SPEC=3.0 EXCLUDE='X.* 6.* 7.*'` |

The scripts are `translate/il2acl2/probe.lsp`, `translate/il2acl2/probe-names.sh`
and the `probe` target in `translate/Makefile`, at this note's commit. The
IL dumps are regenerated by the same command and are not stored.
Supersedes the scripts in `data/probe-2026-11-14/` as the way to take a probe;
that directory stays as the baseline evidence.
