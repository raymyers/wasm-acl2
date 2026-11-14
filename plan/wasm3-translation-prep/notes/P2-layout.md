# Multi-spec layout: directories, packages, flake outputs

- Milestone: P2 (item 1: spec target as a parameter; item 2: config validation)
- Date: 2026-11-14
- Repo commit: ec20d63 plus this note's commit
- Status: draft (items 3-5 of P2 add to it; the `rt/` package question is open)
- Feeds wasm3 plan: scheme delta (package and layout), decisions (D2)
- Incorporated in wasm3 plan: no

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
