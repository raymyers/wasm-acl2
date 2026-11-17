# Multi-spec layout: directories, packages, flake outputs

- Milestone: P2 (all five items: spec parameter, config validation, book split, mode manifest, flake checks)
- Date: 2026-11-14
- Repo commit: ec20d63 plus this note's commit
- Status: final for P2 (the `rt/` package question stays open, see below)
- Feeds wasm3 plan: scheme delta (package and layout), decisions (D2)
- Incorporated in wasm3 plan: yes (draft plan, §1 (D2), §4 (layout and packages))

## Summary

`SPEC=1.0|2.0|3.0` now selects IL, config, output directory, book and
package for `make il|check-il|gen|check-gen|probe`. 1.0 moved to
`config/wasm-1.0.lsp` and `gen/wasm-1.0/`. Its generated definitions are
byte-identical and only 2 header lines changed (config path, `rt` include
path). `make check` passes. 2.0 and 3.0 run through both translator phases.
They cannot be certified yet: `rt/` is written in package `W1T`, a cost of
D2 that the plan did not list.

## Findings

### Layout (assumes D2's recommendation: one tree, per-version packages)

| What | 1.0 | 2.0 | 3.0 |
|---|---|---|---|
| IL | `il/wasm-1.0.il.sexp` (checked in) | `il/wasm-2.0.il.sexp` (not checked in) | `il/wasm-3.0.il.sexp` (not checked in) |
| Flake output | `wasm1-il` (unchanged) | `wasm2-il` | `wasm3-il` |
| Source files | all 10 | all 10 | 25 of 37: `X.*`, `6.*`, `7.*` left out (D3 recommendation, listed in `$out/FILES`) |
| Config | `config/wasm-1.0.lsp` (was `il2acl2-config.lsp`) | `config/wasm-2.0.lsp`, provisional | `config/wasm-3.0.lsp`, provisional |
| Output | `gen/wasm-1.0/` | `gen/wasm-2.0/` (not checked in) | `gen/wasm-3.0/` (not checked in) |
| Book, package | `wasm1.lisp`, `W1T` | `wasm2.lisp`, `W2T` | `wasm3.lisp`, `W3T` |

- Flake outputs are `wasmN-il`, not the plan's `wasm-il.<v>`: a flake's
  `packages` may hold only derivations, so nested attribute sets are not
  allowed, and a dot in an attribute name needs quoting on the command
  line. `wasm1-il` keeps its name, so `check-il` for 1.0 is unchanged.
- The provisional 2.0/3.0 configs are the 1.0 config without `:il-patch`
  and `:rel-override`. That is exactly what the P0/P1 probes used, so the probe
  needs no `PROBE_DROP` any more. Probe reports for 1.0, 2.0 and 3.0 (D3
  scope) are identical to the P1 data.
- `make probe` now defaults to `SPEC=1.0` (it shared the variable with
  `gen`). Before, it defaulted to 3.0.
- `make il SPEC=3.0` and `make gen SPEC=3.0` work: 1,086 events, the same as
  the P1 probe of the D3 scope. 2.0: 688 events.
- The emitter takes a target plist `(:version :pkg :il :config :outdir
  :book)`; `run.lsp` reads it from `il2acl2-target`, which the Makefile
  prepends. Phase 2 switches to the target's package with
  `set-current-package` so symbols print unqualified.
- Paths updated: `rt/cert.acl2`, `tests/sem/*`, `compare/*` (and, in the
  working tree only, the uncommitted T7 files `tests/spec/cert.acl2` and
  `t7-spec.lisp`).

### Open: the runtime's package (affects D2)

`rt/prelude.lisp` and `rt/builtins.lisp` are `(in-package "W1T")`, and
`rt/cert.acl2` loads `gen/wasm-1.0/portcullis`. The hand-written runtime is
therefore inside the generated 1.0 package, whose import list is computed
from the generated names. A `W3T` book cannot include it. Options:

| Option | Cost |
|---|---|
| A. `rt/` in a fixed package `WRT` defined in `translate/package.lsp`; each generated package imports `WRT`'s builtin symbols | 1.0's `gen/wasm-1.0/package.lsp` changes (one more import list); builtins become shared across versions, which suits D2 |
| B. One `rt/` per version (`rt/wasm-<v>/`), copied and edited | Duplication of the numeric core (about 320 lines today, about 30 new builtins for 3.0) |
| C. One package for all versions | The import list would depend on every version's generated names, coupling versions |

Recommendation: A. It needs a user decision with D2 and lands with P3's
builtin classification. Until then only 1.0 certifies.

## Open questions

- Whether to check in the 2.0/3.0 IL now (0.8 MB and 1.2 MB) so `check-il`
  covers them. Not done: no target uses them until P4.

## Data

No measurements beyond the probe comparison (identical to
`data/probe-P1-2026-11-14/`). Reproduce with `make probe SPEC=<v>` and
`make gen SPEC=<v>` (after `make il SPEC=<v>`).

## 2026-11-14: item 2, config validation

- `emit.lisp` `config-errors`: every entry must name something in the IL
  (rules in plan item text, plus: `:decreasing` index below the relation's
  arity, `:sized` variable occurs in the grammar, `:il-patch` `:old` still
  occurs in the form, unknown kinds rejected). An `:inverse` partner may be
  missing from the IL only when the function is itself a `:def` override
  (`utf8`/`inv_utf8`). `gen-phase1` fails on any error; the probe prints them.
- 1.0: no errors, `gen/` unchanged, `make check` passes. A copy of the 1.0
  config with two typos (`Step/ctxt-instr`, `Instrs_okk`) makes `make gen`
  fail with both listed.
- 2.0 and 3.0 provisional configs: exactly one stale entry each, the inverse
  pair `bytes_`/`inv_bytes_` (2.0/3.0 have `nbytes_`, `vbytes_`, and in 3.0
  `zbytes_`, `cbytes_`). Removed; it had no effect, so the probe reports are
  unchanged. `utf8`, `Step/ctxt-instrs`, `Bsection_`/`Bcode` `len` all exist
  in 2.0 and 3.0.
- **Finding for P3**: 2.0 and 3.0 *declare* the inverses as defs:
  3.0 has `inv_concat_`, `inv_concatn_`, `inv_isize`, `inv_jsize`,
  `inv_fsize`, `inv_jsizenn`, `inv_ibits_`, `inv_fbits_`, `inv_ibytes_`,
  `inv_fbytes_`, `inv_nbytes_`, `inv_vbytes_`, `inv_zbytes_`, `inv_cbytes_`,
  `inv_signed_`, `inv_lanes_` (16, matching the 16 `hint(inverse)`).
  So most S1 failures in the gap list (`$jsize`, `$nbytes_`, `$zbytes_`,
  `$concat_`, `$ibits_`, `$isize` patterns) need only the pairs, which P3
  reads from the hints. The plan's "generated inverses for finite
  functions" becomes "builtins for the declared `inv_*` defs".

## 2026-11-14: item 3, one generated book per source file

- `make il` also writes `il/wasm-<v>.decls.lsp` (from
  `il2acl2/spec-decls.sh`, formerly `probe-names.sh`): every declaration's
  source file. Checked in for 1.0 and compared by `check-il`. The 1.0 IL is
  unchanged.
- Each form's events go to the part (book) of its file. Parts are
  consecutive runs of IL order, and each part includes the one before it (the
  first includes `rt/builtins`). The label of a form is the minimum file
  index of itself and every later form (suffix minimum), so a form that the
  IL places before its file's neighbours joins the earlier part. That is
  sound for any labelling that is non-decreasing in IL order, since every
  dependency comes earlier in the IL.
  - The first version ("never go back") collapsed 3.0 into 7 parts: the IL
    places some `5.1` forms among the `1.1` ones. With the suffix minimum
    3.0 has 24 parts (25 files; `1.0-syntax.profiles` produces no events),
    2.0 has 10, and 1.0 has 10 (one per file).
- The top book keeps the name `wasm1.lisp` (not the plan's `top.lisp`), so
  every test keeps its `include-book`. It holds the header (now with the
  part list) and includes the last part.
- 1.0: the parts' events, concatenated, are byte-identical to the old
  single book (37,065 lines); the header gains the part list. `make check`
  (25 books certified) and `make compare` pass. `check-gen` now compares the
  whole set of generated files. The two tests that read generated code as
  data (`t8-proofs`, `t8-run`) read `8-reduction.lisp`.
- Part sizes: 1.0's largest is `A-binary` (20,651 lines, of 37,263). In 3.0
  `5_3-binary_instructions` has 245,830 of 363,736 lines and
  `4_3-execution_instructions` 61,035. The chain gives no parallelism, and
  the binary-instruction part dominates. A finer split (by rec group or
  size) is possible later with the same labelling rule.

## 2026-11-14: item 4, mode manifest

- Modes are decided at certification time (`%TRY-LOGIC`, `%TRY-GUARDS`), so
  the translator cannot write them and `check-gen` cannot compare them.
  Instead:
  - `gen/wasm-1.0/modes.lsp` (checked in): every generated function, per
    part in IL order, as `:GUARDS` / `:LOGIC` / `:PROGRAM`, read from the
    certified world (`symbol-class`).
  - `tests/sem/t0-modes.lisp` (part of `make test`, so of `make check`)
    fails certification when the certified modes differ, listing
    `(name recorded certified)`. Tested: one entry flipped to `:PROGRAM`
    gives `((MUT^UUU-P :PROGRAM :GUARDS))` and a failed certification.
  - `make modes` rewrites the manifest (`tests/sem/modes-write.lsp`);
    `check-gen` ignores `modes.lsp` when it compares file lists.
  - Stubs and dropped rules stay in the generated header, which `check-gen`
    already compares.
- 1.0 measured: 503 functions, **160 guard-verified, 308 logic, 35
  program**. The wasm1 plan's T8 entry (491 / 466 logic / 25 program,
  counted by hand) is stale. The 35 are the same groups it lists (the
  instruction-typing clique, `Expr_ok`, `Expr_ok_const`, `Func_ok`,
  `Global_ok`, `Elem_ok`, `Data_ok`, the `Module_ok` override functions,
  `$instantiate`), plus the `/SPLIT` variants of the callers.
- Only for 1.0: the test books are 1.0's. A 2.0/3.0 manifest needs those
  targets to certify (the `rt/` package question).

## 2026-11-14: item 5, flake checks

- `checks.<system>.translate-gen-wasm1`: copies `translate/` into the
  sandbox and runs `make check-gen SPEC=1.0` with the flake's ACL2 (two
  fresh translator runs must equal the checked-in `gen/wasm-1.0/`). 8 s
  on aarch64-darwin with ACL2 already built. Passes.
- `checks.<system>.translate-il` now also compares `il/wasm-1.0.decls.lsp`.
- Per target: only 1.0 has a checked-in output. A `translate-gen-wasm3`
  check is one copy of the block once 3.0's `gen/` is checked in (P4 or the
  wasm3 plan).

## 2026-11-14 correction (from P3)

The item 2 finding above says the 16 `inv_*` inverses are declared defs and
that P3's "generated inverses for finite functions" becomes "builtins for
the declared `inv_*` defs". Partly wrong: `inv_isize`, `inv_jsize`,
`inv_fsize` and `inv_jsizenn` are *defined* in the spec (with clauses), so
they need nothing. The other 12 are clause-less builtins. See
[P3-builtin-inventory.md](P3-builtin-inventory.md).

## 2026-11-14: option A implemented (assumed, reversible)

To unblock the 2.0 gate (P4) the recommended option A was implemented. It is
recorded as an assumption, like D2, D3 and D5, for the user to confirm.

- `translate/package.lsp` defines `WRT` (`*acl2-exports*`); `rt/prelude.lisp`
  and `rt/builtins.lisp` are in `WRT`; `rt/cert.acl2` includes
  `../portcullis` (no generated package needed any more).
- The generated `defpkg` imports `*acl2-exports*` minus the clash list,
  plus every name `rt/` defines (`defun`, `defmacro`, `defthm`, `defconst`) as a
  `WRT` symbol. The translator already reads that list for the builtin
  check. The generated `portcullis.acl2` first loads `../../package.lsp`.
- 1.0: generated books byte-identical (the symbols print the same in
  `W1T`); `gen/wasm-1.0/package.lsp` gains the import list and
  `portcullis.acl2` one line. `make check` (incl. `t0-modes`: modes
  unchanged), `make compare` and the T7 driver pass.
