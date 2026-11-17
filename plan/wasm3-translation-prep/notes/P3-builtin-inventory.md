# Builtin inventory of WASM 3.0 (D3 scope)

- Milestone: P3 (item 3: builtin classification from `hint(builtin)`)
- Date: 2026-11-14
- Repo commit: 17cf813 plus this note's commit
- Status: final for the classification; the oracle column is a plan, not a
  measurement
- Feeds wasm3 plan: builtin inventory, config budget, decisions (D4)
- Incorporated in wasm3 plan: yes (draft plan, §2, §3, §5 M1)

## Summary

3.0 (`0.*`-`5.*`) has 89 clause-less defs: 77 numeric, 11 choice parameters
(`$ND`, ten `$R_*`), 1 host hook (`$hostcall`), no notation ones in this
scope. 34 of the 77 numeric ones have no definition in `rt/`. The other 43
exist by name from 1.0, but their 3.0 signatures are not checked. Every one
carries `hint(builtin)` except `$s33_to_u32`, which the config lists as
numeric. 2.0: 64 clause-less, all numeric, 21 missing from `rt/`. 1.0: 45,
none missing.

## Findings

- Mechanism (`emit.lisp`): category from the config entry `(:builtins
  "categories" :choice (...) :host (...) :notation (...) :numeric (...))`,
  otherwise `:numeric` if the def has `hint(builtin)`. A clause-less def in
  no category is a hard error. Before the entry was added, 2.0 and 3.0
  failed on `$s33_to_u32`. Config validation checks that every listed name
  is a clause-less def.
- `rt/` check: the translator reads `rt/prelude.lisp` and
  `rt/builtins.lisp` and lists numeric builtins whose mangled name is not
  defined there. The list goes into the generated header ("Numeric builtins
  with no definition in rt/ yet") and the probe report. It checks names
  only, not arity or meaning: 3.0 may have changed a 1.0 signature, which only
  certification and the oracle vectors would show.
- The header gains the non-numeric and missing sections only when they are
  non-empty, so 1.0's generated code and header are unchanged.
- Correction to P2: of the 16 `inv_*` functions, `inv_isize`, `inv_jsize`,
  `inv_fsize`, `inv_jsizenn` are defined in the spec (they have clauses).
  The other 12 are clause-less builtins. P3 item 4 ("generated inverses
  for finite functions") needs no translator work.
- Oracle sources (column 4) are the plan for P4/the wasm3 plan. The numeric
  ones reuse the 1.0 approach (Node/V8 runs WASM ops); the byte encodings
  use store/load round trips; list functions and `$ceilz` need no external
  oracle; the choice parameters are fixed by D4, and V8's relaxed-SIMD
  results are the reference if D4 is accepted.

### Table (3.0, D3 scope, IL order)

| Def | Category | In `rt/` | Oracle source |
|---|---|---|---|
| `$inv_concat_` | numeric | missing | none needed: list function, checked by concat(inv(x)) = x |
| `$inv_concatn_` | numeric | missing | none needed: list function, checked by concat(inv(x)) = x |
| `$ND` | choice | n/a | V8 relaxed-SIMD behaviour (D4 fixes the choice) |
| `$R_fmadd` | choice | n/a | V8 relaxed-SIMD behaviour (D4 fixes the choice) |
| `$R_fmin` | choice | n/a | V8 relaxed-SIMD behaviour (D4 fixes the choice) |
| `$R_fmax` | choice | n/a | V8 relaxed-SIMD behaviour (D4 fixes the choice) |
| `$R_idot` | choice | n/a | V8 relaxed-SIMD behaviour (D4 fixes the choice) |
| `$R_idot_add` | choice | n/a | V8 relaxed-SIMD behaviour (D4 fixes the choice) |
| `$R_iq15mulr` | choice | n/a | V8 relaxed-SIMD behaviour (D4 fixes the choice) |
| `$R_trunc_u` | choice | n/a | V8 relaxed-SIMD behaviour (D4 fixes the choice) |
| `$R_trunc_s` | choice | n/a | V8 relaxed-SIMD behaviour (D4 fixes the choice) |
| `$R_swizzle` | choice | n/a | V8 relaxed-SIMD behaviour (D4 fixes the choice) |
| `$R_laneselect` | choice | n/a | V8 relaxed-SIMD behaviour (D4 fixes the choice) |
| `$s33_to_u32` | numeric | missing | binary decoder (wabt/V8 accept the block type) |
| `$ibits_` | numeric | missing | V8 memory store/load round trips |
| `$fbits_` | numeric | missing | V8 memory store/load round trips |
| `$ibytes_` | numeric | in rt/ (1.0, by name) | V8 memory store/load round trips |
| `$fbytes_` | numeric | in rt/ (1.0, by name) | V8 memory store/load round trips |
| `$nbytes_` | numeric | missing | V8 memory store/load round trips |
| `$vbytes_` | numeric | missing | V8 memory store/load round trips |
| `$zbytes_` | numeric | missing | V8 memory store/load round trips |
| `$cbytes_` | numeric | missing | V8 memory store/load round trips |
| `$inv_ibits_` | numeric | missing | V8 memory store/load round trips |
| `$inv_fbits_` | numeric | missing | V8 memory store/load round trips |
| `$inv_ibytes_` | numeric | in rt/ (1.0, by name) | V8 memory store/load round trips |
| `$inv_fbytes_` | numeric | in rt/ (1.0, by name) | V8 memory store/load round trips |
| `$inv_nbytes_` | numeric | missing | V8 memory store/load round trips |
| `$inv_vbytes_` | numeric | missing | V8 memory store/load round trips |
| `$inv_zbytes_` | numeric | missing | V8 memory store/load round trips |
| `$inv_cbytes_` | numeric | missing | V8 memory store/load round trips |
| `$truncz` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$ceilz` | numeric | missing | none: rational ceiling, tested by definition |
| `$iclz_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$ictz_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$ipopcnt_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$iq15mulr_sat_` | numeric | missing | V8 SIMD / scalar ops (Node) |
| `$irelaxed_q15mulr_` | numeric | missing | V8 relaxed SIMD |
| `$iavgr_` | numeric | missing | V8 SIMD / scalar ops (Node) |
| `$inot_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$irev_` | numeric | missing | V8 SIMD / scalar ops (Node) |
| `$iand_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$iandnot_` | numeric | missing | V8 SIMD / scalar ops (Node) |
| `$ior_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$ixor_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$ishl_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$ishr_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$irotl_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$irotr_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$ibitselect_` | numeric | missing | V8 SIMD / scalar ops (Node) |
| `$irelaxed_laneselect_` | numeric | missing | V8 relaxed SIMD |
| `$fabs_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$fneg_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$fsqrt_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$fceil_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$ffloor_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$ftrunc_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$fnearest_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$fadd_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$fsub_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$fmul_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$fdiv_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$fmin_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$fmax_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$fpmin_` | numeric | missing | V8 SIMD / scalar ops (Node) |
| `$fpmax_` | numeric | missing | V8 SIMD / scalar ops (Node) |
| `$frelaxed_min_` | numeric | missing | V8 relaxed SIMD |
| `$frelaxed_max_` | numeric | missing | V8 relaxed SIMD |
| `$fcopysign_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$feq_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$fne_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$flt_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$fgt_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$fle_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$fge_` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$frelaxed_madd_` | numeric | missing | V8 relaxed SIMD |
| `$frelaxed_nmadd_` | numeric | missing | V8 relaxed SIMD |
| `$wrap__` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$extend__` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$trunc__` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$trunc_sat__` | numeric | missing | V8 SIMD / scalar ops (Node) |
| `$relaxed_trunc__` | numeric | missing | V8 relaxed SIMD |
| `$demote__` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$promote__` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$convert__` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$narrow__` | numeric | missing | V8 SIMD / scalar ops (Node) |
| `$reinterpret__` | numeric | in rt/ (1.0, by name) | V8 (existing 1.0 numeric vectors) |
| `$lanes_` | numeric | missing | V8 SIMD / scalar ops (Node) |
| `$inv_lanes_` | numeric | missing | V8 SIMD / scalar ops (Node) |
| `$hostcall` | host | n/a | none: the conformance driver's host module |

## Open questions

- Arity and meaning of the 43 builtins that exist by name: check when 3.0
  first certifies (needs the `rt/` package decision, P2-layout).
- D4 (nondeterminism policy) decides what the 11 choice parameters return.

## Data

`data/builtin-inventory-2026-11-14/`: `clauseless.lsp` (lists clause-less
defs and their hints for 1.0/2.0/3.0), `make-table.sh` (builds the table
above), `report-3.0-core.txt` (probe with the builtin line).
