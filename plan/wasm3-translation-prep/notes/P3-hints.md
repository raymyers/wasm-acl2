# Hints at the hand-off: SpecTec patch, IL hint forms, inverse pairs

- Milestone: P3 (item 1: patch `backend-ast/print.ml` to emit hint
  definitions; schema and reader accept them)
- Date: 2026-11-14
- Repo commit: f9c403e plus this note's commit
- Status: draft (items 2-4 of P3 add to it)
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
