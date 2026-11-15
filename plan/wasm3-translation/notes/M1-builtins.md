# Numerics and builtins for 3.0: rt/builtins-3.0.lisp, D4, relaxed SIMD

- Milestone: M1 (items 1-3)
- Date: 2026-11-14
- Repo commit: 9c25ceb plus this note's commit
- Status: final
- Feeds wasm3 plan: §2, §3, §5 M1 (done), §6, "Current state"

## Summary

Every clause-less def of 3.0 now has a definition. The probe reports
"numeric 77 (no definition in rt/: 0)", and `gen/wasm-3.0` has **1
stub** (`Module_ok`, M7), down from 27. `make check-3.0` runs three new
test books (1 min 39 s in all):

| Book | Result |
|---|---|
| `t3-numerics-3.0` | **8,724 of 8,724** scalar vectors agree with V8 (the 1.0 and 2.0 vectors; 3.0 adds no scalar operator) |
| `t3-simd-3.0` | **1,008 of 1,008** SIMD vectors agree: the 528 of 2.0 (same PRNG) and **480 relaxed-SIMD vectors** (20 operators × 24) in the deterministic profile |
| `t3-simd-3.0`, full profile | **480 of 480** relaxed vectors give V8's own result when the builtins run with `$ND` true and the `$R_*` of `rt/` |
| `t3-builtins-3.0` | **26 of 26** cases: byte encodings, `$ceilz`, `$inv_concatn_`, `$utf8single`, the `$hostcall` default, `$ND` and `$R_*` |

The 1.0 gate (byte-identical) and the 2.0 gate (8,724/8,724, 528/528)
stay green.

## Where the definitions are

`rt/builtins-3.0.lisp` (package `WRT`, includes `rt/builtins`). The
translator reads it for `SPEC=3.0` only (`rt-files-for`, also used by
the probe through the new `probe-version`), and the first 3.0 part
includes it. So the 1.0 and 2.0 import lists and generated code do not
change. Adding these names to the shared `builtins.lisp` would have
changed `gen/wasm-1.0/package.lsp`.

- **Representation:** `$zbytes_` / `$inv_zbytes_` (packed `I8` / `I16`
  as `$ibytes_` of 8 / 16 bits, `V128` as `$vbytes_`, else `$nbytes_`),
  `$cbytes_` / `$inv_cbytes_`, as in SpecTec's `numerics.ml`.
- **Sequences:** `$inv_concatn_(n, l)` splits into lists of n elements
  and drops a shorter rest, as in `numerics.ml`.
- **`$ceilz`:** the ceiling of a rational.
- **`$utf8single`:** new config entry `:def "utf8single"`, with its
  reason in the config. It follows the four clauses and gives no result
  for a surrogate or above U+10FFFF. It is the last stub of a def. No
  generated code calls it today, because the `utf8` override replaces
  the 3.0 `$utf8` that uses it.
- **`$hostcall`:** a hook, `(defattach %hostcall-hook ...)`. The default
  has no result, so a host function call does not step. A driver (M4)
  attaches a function to `(hostfunc store vals)` that returns
  `(:RES store result)` or `(:BOT)`. Gotcha, found by the test book: ACL2
  does not use attachments when it evaluates a `defconst`, only at the
  top level and in `make-event`.
- **Relaxed builtins:** `$irelaxed_q15mulr_`, `$irelaxed_laneselect_`,
  `$frelaxed_min_`, `$frelaxed_max_`, `$frelaxed_madd_`,
  `$frelaxed_nmadd_`, `$relaxed_trunc__`. Each is written from the 3.0
  prose (`document/core/exec/numerics.rst`) as `relaxed(R)[A_0, ...]` in
  a helper that takes the profile, e.g. `(%frelaxed-madd nd r n a b c)`.
  The builtin passes `($ND)` and its `$R_*`. Alternative 1 of `relaxed_madd`
  is a new fused multiply-add, `%fma`, rounded once. Alternative 1 of
  `relaxed_trunc` is "any value" in the prose, so the builtin always takes
  alternative 0.

## D4 for relaxed SIMD

D4 says "deterministic profile: `$ND` false, `$R_*` fixed to the values
V8 uses". With `$ND` false, `relaxed(R)[...]` is `A_0` whatever R is.
This holds both in the generated `$relaxed2` / `$relaxed4` and in the
builtins. SpecTec's interpreter does the same: `ND` false, every R 0,
"use deterministic behaviour" in each relaxed builtin. So the
**semantics is the deterministic profile**. The `$R_*` values record
V8's choices and change no result.

V8 itself does not follow the deterministic profile. Measured on this
machine (arm64, Node v24.18.1), V8's relaxed instruction equals the
deterministic result on 24 of 24 vectors for 17 of the 20 operators.
The exceptions are `f32x4.relaxed_madd` (19 of 24), `f32x4.relaxed_nmadd`
(22 of 24) and `f64x2.relaxed_nmadd` (20 of 24), where V8 fuses
(`v8-vs-deterministic.txt`). So the oracle cannot be V8's relaxed
instruction alone. The vector generator (`gen-simd-vectors.mjs 3.0`)
writes two results per relaxed vector:
- **DET**: V8 running the strict equivalent (e.g. `f32x4.add (f32x4.mul
  a b) c` for `relaxed_madd`, `i8x16.swizzle` for `relaxed_swizzle`,
  shuffles and `extmul` for the dot products). The generated semantics
  must give this.
- **V8**: V8's relaxed instruction. The builtins in the full profile
  (`$ND` true, rt's `$R_*`) must give this. That checks two things: that
  `$R_*` are V8's choices (`R_fmadd` = 1, the others 0), and the `%fma`
  that `$ND` false never uses.

The operands mix NaNs (quiet, signalling, negative), signed zeros,
infinities, out-of-range values, `0x8000` lanes and swizzle indices of
16 and above, so the alternatives differ. Checked
(`madd-discrimination.lsp`): with `R_fmadd` = 0, only 44 of the 48 madd
vectors give V8's result; with 1, all 48 do. So 4 vectors test the
fusing. That is few, but they pass.

The choices are V8's **on arm64**. On x86-64, V8 could make other
choices (e.g. for `relaxed_min` with NaNs or `relaxed_trunc`). With
`$ND` false that changes nothing in the semantics, only the full-profile
count of the test.

## Config budget after M1

`config/wasm-3.0.lsp`: 10 entries. `:def utf8single` is new (reason in
the config); the others are as after M0.

## Data

`data/builtins-M1-2026-11-14/`: `probe-3.0-core.txt` (the probe after
M1: 1 stub, 0 builtins missing), `v8-vs-deterministic.txt` (per relaxed
operator, how often V8 equals the deterministic result),
`madd-discrimination.lsp` / `.txt` (the R_fmadd check above). The
vectors are `translate/tests/sem-3.0/simd-vectors-3.0.lsp`
(`node tests/oracle/gen-simd-vectors.mjs 3.0`).
