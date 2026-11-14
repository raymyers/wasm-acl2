# Hints at the hand-off: SpecTec patch, IL hint forms, inverse pairs

- Milestone: P3 (item 1: patch `backend-ast/print.ml` to emit hint
  definitions; schema and reader accept them)
- Date: 2026-11-14
- Repo commit: f9c403e plus this note's commit
- Status: final
- Feeds wasm3 plan: scheme delta, builtin inventory, decisions (D5)
- Incorporated in wasm3 plan: no

## Summary

A 15-line patch (`nix/spectec-ast-print-hints.patch`, applied to the
flake's `spectec`) prints every `HintD` as `(hint <kind> "<id>" ["<rule>"]
(<name> "<text>") ...)`. The 1.0 IL gains exactly 244 one-line hint forms
and is otherwise byte-identical. The translator splits hints off after
reading, so the generated 1.0 code is unchanged. 3.0 carries all 16
`hint(inverse)` pairs; 2.0 carries 12. This follows D5's recommendation,
which the user has not yet confirmed.

## Findings

- The patch: `HintD hd -> hintdef hd`; hint expressions are EL (surface)
  syntax, printed as text with `El.Print.string_of_exp` (the library
  already depends on `el`). Hints attached to type cases and fields
  (`typcase`'s `_hints`) are still not printed.
- Hint forms per IL: 1.0 244, 2.0 366, 3.0 (D3 scope) 713. Names in 1.0:
  `show` 104, `desc` 86, `builtin` 45, `macro` 5, `partial` 2, `inverse` 4.
  A definition can have several hint forms (e.g. `ibytes_` has one with
  `show` + `inverse` and one with `builtin`).
- Removing the hint lines from the new 1.0 IL gives the old IL exactly.
  `make check` passes. `t1-il` still sees 318 definitions and now also
  checks hints: shape, and that each names a defined `typ`/`rel`/`def`/
  `gram` (`rule` hints: their relation). Negative tests added.
- Translator: `read-il` (top.lisp) returns `(mv erp defs hints state)`;
  `il-check`, `gen-phase1` and the probe use it. `il-check`'s summary adds
  `:hints`.
- Inverse pairs in the IL:
  - 2.0 (12): `concat_`, `isize`, `jsize`, `fsize`, `signed_`, `ibits_`,
    `fbits_`, `ibytes_`, `fbytes_`, `nbytes_`, `vbytes_`, `lanes_`.
  - 3.0 (16): the 12 of 2.0 plus `concatn_`, `jsizenn`,
    `zbytes_`, `cbytes_`. Each `f` pairs with `inv_f`.
  - The 1.0 config's 5th pair, `utf8`/`inv_utf8`, is not a hint: it is the
    hand-written partner of the `utf8` `:def` override.

## Open questions

- Upstreaming: the patch is small and independent of this project. Offering
  it to WebAssembly/spec is a user decision (D5).

## Data

`make -C translate il SPEC=<v>` (patched SpecTec) and
`make -C translate probe SPEC=<v>` ("hint forms" line).
`grep '(inverse' translate/il/wasm-<v>.il.sexp` lists the pairs.

## 2026-11-14: item 2, inverse pairs from the IL

- `emit.lisp` `all-inverse-pairs`: the pairs from `hint(inverse)` in the IL,
  then from `:def` overrides that declare `:inverse` (only
  `(:def "utf8" :inverse "inv_utf8")`), then any `:inverse` config entry
  (none left). The `:inverse` entry is gone from all three configs.
- 1.0: the pair list is the same as before, in the same order (`signed_`,
  `ibytes_`, `fbytes_`, `bytes_`, `utf8`). Generated code is unchanged;
  only the header's config listing changed (the entry is gone and the `utf8`
  reason mentions its inverse). `make check` passes.
- Effect (probe, `data/probe-P3-2026-11-14/`):

| | before (P1/P2) | after |
|---|---|---|
| 2.0 stubs | 5 | **2** (`Module_ok`, `GRAM/Binstr`): `$vrelop_`, `$vextunop__`, `$vextbinop__` now compile |
| 2.0 `Step` / `Step_read` / `Step_pure` | 22/23, 42/47, 51/56 | **23/23**, 46/47, 52/56 |
| 3.0 D3-scope stubs | 21 | **16**: `$fvrelop_`, `$ivbitmaskop_`, `$ivadd_pairwise_`, `$ivdot_`, `$ivdot_sat_` now compile |
| 3.0 dropped rules (D3 scope, emitted) | 42 | 36 |
| 3.0 `Step` / `Step_read` / `Step_pure` | 35/36, 96/103, 77/79 | **36/36**, 101/103, 77/79 |
| 3.0 failing reduction rules | 10 of 218 | **4**: G9 2 (`vsplat`, `vreplace_lane`), G3 1 (`array.new_data-num`), G4 1 (`vload-pack-val`) |

- P3 exit check: no remaining "pattern" error in 3.0 involves a function
  with an inverse hint. The 17 left are `$utf8single` (S5), `:fun`-mode
  typing artifacts (`clos_deftype`, index and length patterns), `Module_ok`
  (S4) and text grammars (`6.*`, out of scope).
- Consequence for builtins: generated 3.0 code now calls the 16 `inv_*`
  functions (clause-less defs), so they join the builtin inventory (item 3).
