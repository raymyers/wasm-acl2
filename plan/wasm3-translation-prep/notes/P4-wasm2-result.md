# WASM 2.0 as a full target (the P4 gate)

- Milestone: P4 (item: 2.0 as a full target; and the P4 exit)
- Date: 2026-11-14
- Repo commit: d55e442 plus this note's commit
- Status: final
- Feeds wasm3 plan: milestones, builtin inventory, risks, config budget
- Incorporated in wasm3 plan: yes (draft plan, §1 (D1), §6 (config budget))

## Summary

The generated WASM 2.0 semantics translates with **1 stub (`Module_ok`)**,
certifies (about 85 s), and agrees with Node/V8 on **8,724 of 8,724 scalar
numeric vectors** and **528 of 528 SIMD vectors**. This meets the P4 exit.
`make -C translate check-2.0` reproduces it in about 2 min 20 s. Getting
there took:

- the runtime package `WRT` (P2-layout option A, assumed);
- 21 new builtins in `rt/`;
- declared modes for instruction typing;
- two counted `:il-patch` entries for a 2.0 source bug in the vector decoder;
- two translator fixes: elided projections in patterns, and the calling
  convention of declared `:multi` relations.

## Findings

- Builtins added to `rt/builtins.lisp` (logic mode, from the 2.0 spec text
  and SpecTec's `backend-interpreter/numerics.ml`): `$s33_to_u32`,
  `$narrow__`, `$trunc_sat__`, `$ibits_`, `$fbits_`, `$inv_ibits_`,
  `$inv_fbits_`, `$nbytes_`, `$inv_nbytes_`, `$vbytes_`, `$inv_vbytes_`,
  `$irev_`, `$iandnot_`, `$ibitselect_`, `$iavgr_`, `$iq15mulr_sat_`,
  `$fpmin_`, `$fpmax_`, `$lanes_`, `$inv_lanes_`, `$inv_concat_` (pairs, as
  numerics.ml). 2.0 now has 0 numeric builtins missing in `rt/`; 3.0 has 13.
- Config (`config/wasm-2.0.lsp`, counted):
  - `:modes`: `Instr_ok`, `Instrs_ok` `:multi`.
  - Two `:il-patch` entries for `Binstr`: in the 2.0 source, `0xFD 12:Bu32
    (b:Bbyte)^16 => VCONST V128 b' -- if $ibytes_(128, b') = b` elaborates
    `b`, `b'` as single bytes, binds no list in the iteration, and compares
    with `[b]`, so no `v128.const` decodes. `i8x16.shuffle` (`l^16`) has the
    same defect. Both are patched to the form the 3.0 source uses (the
    iteration binds `b*`/`l*`; `VCONST V128 $inv_ibytes_(128, b^16)`).
- Translator fixes found on the way (1.0 unchanged):
  - `cpat`: `(proj (uncase x "%") 0)` on an elided newtype is `x` as a
    pattern too (as `cexp` already had).
  - Declared `:multi` relations got the `:fun` calling convention from
    `set-modes`, so callers passed too few arguments. Found by the 2.0
    certification (`INSTRS_OK takes 3 arguments`); the probe could not see
    it.
- Probe after the gate (`data/probe-P4-gate-2026-11-14/`): 2.0: 1 stub
  (`Module_ok`), 2 dropped rules (`Instr_ok/select-impl`, G5, and
  `Instrs_ok/sub`), 32 errors. 3.0 D3 scope: 2 stubs
  (`Module_ok`, `$utf8single`), 7 dropped rules, 56 errors; full 3.0: 76
  stubs (69 text grammars).
- Vectors: `tests/sem-2.0/t3-numerics-2.0.lisp` runs the 1.0 vectors
  (8,015) plus `numeric-vectors-2.0.lsp` (709: 8 saturating truncations, 5
  sign extensions; `gen-numeric-vectors.mjs 2.0`; the 1.0 output of the
  generator is unchanged). `tests/sem-2.0/t3-simd-2.0.lisp` reduces
  `[VCONST a, VCONST b, (VCONST c,) op]` with the generated `Step_pure` and
  compares with V8 for 22 SIMD ops (`gen-simd-vectors.mjs`, 24 vectors
  each, finite float lanes).
- Not checked in: `gen/wasm-2.0/` (20 MB, deterministic from the checked-in
  `il/wasm-2.0.il.sexp`); `check-2.0` regenerates it.
- Not covered: 2.0 typing and module tests, the 2.0 spec test suite, and
  NaN-producing SIMD float lanes.

## Data

`data/probe-P4-gate-2026-11-14/` (`report-2.0.txt`, `report-3.0*.txt`,
`rules-3.0-core.txt`, `vectors-2.0.txt`); `make -C translate check-2.0`.
