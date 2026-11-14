# Per-rule gap list for WASM 3.0 (and 2.0)

- Milestone: P1 (per-rule gap list: rule id, cause, gap id from plan §2, proposal)
- Date: 2026-11-14
- Repo commit: 507f7f9 plus this note's commit (translator with P1 items 1-3)
- Status: draft (update after P4; the causes of S1 and G9 entries are to be
  confirmed when the fixes land)
- Feeds wasm3 plan: gap list, milestones, config budget
- Incorporated in wasm3 plan: no

## Summary

In the D3 scope (`0.*`-`5.*`) the 35 stubs of P0 become 21 stubs (16 defs,
`Module_ok`, and 4 typing relations that lose every rule) and 14
relations emitted without 42 rules. Measured in the mode that got furthest,
only **14 rules** fail: S1 inverses (4), G5 disjunctions (3), G8 existential
index (2, new), G9 binding order in a list pattern (2, new), G3 (1), G4 (1)
and S4 (`Module_ok`, 1). The other failures are typing rules that fail only
in `:fun`, which P4's mode table removes, and, for `Step_read` in its
execution mode `:fun`, 2 more S1 inverses (`load-num-val`, `vload-num-val`).
Defs: G1 (8), S1 (5), G2 (2), S5 (1).

## How to read the tables

- Source: `make probe SPEC=3.0 EXCLUDE='X.* 6.* 7.*'` → `rules.txt` (one line
  per failing rule and mode, with error kinds and the first error) and
  `errors.lsp` (every error with `:rule`, `:pos`, `:mode`).
- "Best" is the attempt with the fewest failing rules (`:fun`, `:check`, or
  `:multi` = check variant + split variant). "Emitted" is the mode the
  relation is generated in. Since P1 it is always `:fun` when dropping
  rules saves `:fun`, the interface the old whole-relation stub had (see
  [P1-typing-root-causes.md](P1-typing-root-causes.md) for why that is not
  the right mode for typing).
- A rule in the "emitted" column but not the "best" column fails only
  because of the mode (`:fun` takes the last component as the output).

## Findings

### Relations (D3 scope)

Attempt scores, failing rules for `:fun` / `:check` / `:multi`:

| Group | fun / check / multi | Emitted (`:fun`) |
|---|---|---|
| Type validation + subtyping (19 relations, one `rec`) | 22 / 9 / **2** | 17 rules dropped across 9 relations; `Deftype_sub`, `Deftype_ok`, `Subtype_ok2`, `Resulttype_ok` lose every rule and stay stubs |
| `Instr_ok`, `Instrs_ok` | 15 / 9 / **3** | `Instr_ok` 96/110, `Instrs_ok` 4/5 |
| `Step_read` | 7 / **5** / 5 | 96/103 |
| `Step_pure` | **2** / 2 / 2 | 77/79 |
| `Step` | **1** / 1 / 1 | 35/36 |
| `Module_ok` | **1** / 1 / 1 | stub (its only rule) |

Failing rules in the best attempt, with one cause each:

| Rule | Best mode | Cause | Gap | Proposal |
|---|---|---|---|---|
| `Deftype_sub/super` | `:multi` (check) | `C ⊢ typeuse*[i] <: deftype_2` with `i` bound only by `i < \|typeuse*\|`: an existentially quantified index | **G8** (new) | When a variable is bound only by `v < \|l\|` with `l` bound, enumerate `v` over `0..\|l\|-1` (bounded existential search) |
| `Heaptype_sub/rec-sub` | `:multi` (check) | Same shape: `j < \|typeuse*\|`, `typeuse*[j]` in the conclusion | **G8** | Same |
| `Instr_ok/select-impl` | `:multi` (check) | `t' = numtype \/ t' = vectype`: disjuncts bind different variables | G5 | `t'` is bound by then: compile the disjunction as a test |
| `Instr_ok/array.new_data` | `:multi` (check) | `$unpack(zt) = numtype \/ ... = vectype` | G5 | Same |
| `Instr_ok/array.init_data` | `:multi` (check) | Same | G5 | Same |
| `Step_pure/vsplat` | `:fun` | `CONST $lunpack(Lnn) c_1` is matched before `VSPLAT (Lnn X M)` binds `Lnn`; the later `c = $inv_lanes_(...)` then sees `Lnn`, `M`, `c_1` unbound | **G9** (new, cause probable) | Defer call patterns inside a list pattern until the other elements are matched, as `cpat-args-defer` already does for top-level arguments |
| `Step_pure/vreplace_lane` | `:fun` | Same shape | G9 | Same |
| `Step_read/vload-pack-val` | `:check` | `(if $ibytes_(K, j) = ...)^(k<M)` binds `j*` only through an `if` premise | G4 | As plan §2.1 G4 |
| `Step_read/vload-splat-val` | `:check` | Pattern `$jsize(Jnn)`: solve `N = $jsize(Jnn)` for `Jnn` | S1 | Generated inverse of a finite function (P3) |
| `Step_read/vload_lane-val` | `:check` | Same, `$jsize(Jnn)` | S1 | Same |
| `Step_read/array.new_data-num` | `:check` | `(if $cunpack(zt) =/= eps)^n`: iteration with a counter and no domain; also `$concatn_` of `$zbytes_` as a pattern | G3 (+ S1) | As plan §2.1 G3; inverse pairs from the IL (P3) |
| `Step_read/array.init_data-num` | `:check` | Pattern `$zbytes_(zt, c)`: no inverse pair | S1 | Inverse pairs from the IL hints (P3) |
| `Step/vstore_lane-val` | `:fun` | Pattern `$jsize(Jnn)` | S1 | Generated inverse (P3) |
| `Module_ok/` | `:fun` | The context `C` is built from outputs of premises that take `C` (the 1.0 cycle), plus tags and staged `C'`; 26 errors | S4 | New hand-written override, or modes per premise once P4 lands |

Rules that fail only in the emitted `:fun` mode (not in the best attempt):

| Rules | Cause in `:fun` |
|---|---|
| `Step_read/load-num-val`, `Step_read/vload-num-val` | `$nbytes_(nt, c) = bytes`, `$vbytes_(V128, c)`: needs the inverse (S1). The 1.0 config pairs `bytes_`/`ibytes_`/`fbytes_`, but 3.0 calls `nbytes_`/`vbytes_`/`zbytes_`: an instance of W5, an entry that silently does not apply |
| 11 `Instr_ok` stack-polymorphic rules (`unreachable`, `br`, `br_table`, `return`, `return_call*`, `throw`, `throw_ref`) + `Instrs_ok/sub` | `t_1*` unconstrained in `:fun` (as in 1.0; the 1.0 answer is `:multi`) |
| `Instr_ok/extern.convert_any`, `any.convert_extern` | `null_1? = null_2?` with both sides unbound in `:fun` |
| 20 type-group rules | The subject of `C ⊢ x : OK` is taken as the output; see [P1-typing-root-causes.md](P1-typing-root-causes.md) |

### Defs (D3 scope; whole-def stubs, unchanged by P1)

| Def | Cause | Gap |
|---|---|---|
| `$vunop_`, `$vbinop_`, `$vternop_`, `$vrelop_`, `$vshiftop_`, `$vswizzlop_`, `$vextunop__`, `$vextbinop__` | Function-valued argument (`(def "f")`), 53 sites | G1 |
| `$fvrelop_` | Pattern `$isize(Inn)` | S1 (generated inverse) |
| `$ivbitmaskop_` | Pattern `$ibits_(32, c)` | S1 (builtin inverse) |
| `$ivadd_pairwise_`, `$ivdot_`, `$ivdot_sat_` | Pattern `$concat_(N, (j_1 j_2)*)` | S1 (`$inv_concat_`, a builtin the spec also uses directly) |
| `$utf8single` | Result defined arithmetically (1.0 `$utf8`) | S5 |
| `$evalexprs`, `$evalglobals` | `Eval_expr: z; expr ~>* z'; val*` has two outputs | G2 |

Binary grammars: all 87 compile (no gap).

### Outside the D3 scope (full 3.0 run)

- `6.*` text format: 69 grammars stubbed, 736 "grammar symbol" errors (G6).
- `7.*` soundness: `Context_ok`, `Moduleinst_ok`, `Store_ok`, `Extend_store`
  stubs (each a single rule); `ImmutReachable` emitted 2/5, its 3 dropped
  rules are G8 (`i < |s.STRUCTS[a].FIELDS|`).
- `X.*` notation: `NotationTypingPremisedots` (G7, arity 0) and
  `NotationTypingScheme` stubs.

### 2.0

`make probe SPEC=2.0`: 5 stubs (`$vrelop_`, `$vextunop__`, `$vextbinop__`,
`Module_ok`, `GRAM/Binstr`; was 10) and 5 relations emitted without 20 rules
(`Instr_ok` 67/74, `Instrs_ok` 3/5, `Step_pure` 51/56, `Step_read` 42/47,
`Step` 22/23). Attempt scores: `Instr_ok` group 9 / 3 / 2, `Step_read`
5 / 3 / 3. The 2.0 gate (P4) needs the same S1, G5 and mode work as 3.0.

## Open questions

- G9's mechanism is inferred from the error sequence (`Lnn` unbound when the
  first list element is matched), not from reading the pattern compiler.
  Confirm when fixing.
- The emitted mode for typing is `:fun` and therefore not useful; P4 decides.

## Data

`data/probe-P1-2026-11-14/` (commit: this note's): `report-<v>.txt`,
`rules-<v>.txt`, `errors-<v>.lsp` from `make probe SPEC=<v>`;
`*-3.0-core.*` from `make probe SPEC=3.0 EXCLUDE='X.* 6.* 7.*'`.
