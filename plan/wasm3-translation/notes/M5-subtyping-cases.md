# Subtyping behavioural cases (before `trans`)

- Milestone: M5 (item "Behavioural cases")
- Date: 2026-11-15
- Repo commit: 2c044c1 plus this note's commit
- Status: final for the book; the cases that need `trans` wait for M5's
  `trans` item
- Feeds wasm3 plan: §5 M5 (exit: the behavioural cases pass)

## Summary

`tests/sem-3.0/t5-subtyping-3.0.lisp` (in `make check-3.0`) calls the
generated relations of the type group directly: 46 cases. Each expected
answer comes from the rules of `2.2-validation.subtyping.spectec`, and
each case says which rule decides it. **35 of 46 are right. The 11 wrong
ones all need `Heaptype_sub/trans`**, which is dropped today. The book
reports the count and does not fail on a wrong answer. It fails only if
a case uses an encoding that the generated recognizers reject (all
accept).

## The cases

The plan's list is all there:
- abstract hierarchies: `I31 <: EQ`, `I31 <: ANY`, `STRUCT <: ANY`,
  `ARRAY <: ANY`, `EQ <: ANY`, `deftype <: STRUCT`, `deftype <: EQ`,
  `deftype <: ANY`, `NONE <: I31`, `NONE <: STRUCT`, `NOFUNC <: FUNC`,
  `NOEXTERN <: EXTERN`, `BOT <: I31`;
- one negative case per hierarchy and across: `I31 <: FUNC`,
  `FUNC <: ANY`, `EXTERN <: ANY`, `EXN <: ANY`, `ANY <: EQ`,
  `NOFUNC <: I31`, `NONE <: FUNC`, `deftype <: FUNC`;
- defined types and `_IDX` on each side: `B <: A` (declared), `A <: B`
  (no), `(type 0) <: STRUCT`, `A <: (type 0)`, `(type 1) <: (type 0)`,
  `(type 0) <: (type 1)` (no), `(type 1) <: EQ`;
- `REC i` in a rec-group context (`C.RECS[0]` declares `(type 1)` = B as
  supertype): `REC 0 <: (type 1)` (rec-sub), `REC 0 <: STRUCT`,
  `REC 0 <: (type 0)` (the supertype of the declared one), `REC 0 <: FUNC`
  (no);
- reference types, with null and without;
- fields: immutable covariant, mutable invariant (`mut (ref i31) <: mut
  (ref null i31)` is no), `mut` against `const`;
- function types: contravariant parameters, covariant results, and the
  wrong direction;
- validity: `valtype_ok`, a missing type index, `deftype_ok`.

## The 11 wrong ones

`I31 <: ANY`, `STRUCT <: ANY`, `ARRAY <: ANY`, `deftype A <: EQ`,
`deftype A <: ANY`, `NONE <: I31`, `NONE <: STRUCT` (its premise is
`STRUCT <: ANY`), `(type 1) <: EQ`, `REC 0 <: STRUCT`, `REC 0 <: (type 0)`,
`(ref i31) <: (ref null any)`. Each needs a chain of two or more steps.

One correction to my own expectation: `REC 0 <: STRUCT` is not decided
by `rec-struct`. In the IL that rule matches only a subtype with an empty
supertype list (`SUB final? (STRUCT ...)` elaborates to
`SUB final? [] (STRUCT ...)`). With a declared supertype the answer
(yes) goes through `rec-sub` and `typeidx-l`, so through `trans`.

## Data

The book itself, and its output in
`translate/tests/sem-3.0/t5-subtyping-3.0.cert.out` after
`make check-3.0`.
