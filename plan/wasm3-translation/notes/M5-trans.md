# `Heaptype_sub/trans` through an enumeration variant

- Milestone: M5 (item "Translate `Heaptype_sub/trans` with an enumeration variant")
- Date: 2026-11-15
- Repo commit: 39781b8 plus this note's commit
- Status: final
- Feeds wasm3 plan: §3, §5 M5 (exit met), §7, M6

## Summary

`Heaptype_sub` is complete: **21 of 21 rules**, and the 19-relation type
group has no dropped rule. `trans` is translated as the user decided
(2026-11-14): its intermediate type `heaptype'` comes from an
**enumeration variant** `HEAPTYPE_SUB/ENUM2(C, ht_1)`, the list of every
type that one rule other than `trans` relates `ht_1` to. Measured:
- The behavioural book: **46 of 46** subtyping and validity cases right
  (35 before). `make check-3.0` reports it.
- The M6 typing cases: the three that needed `trans` are now right
  (`I31 <: ANY`, `A <: eq`, `none <: struct`); the other results are
  unchanged (`typing-cases-after-trans.txt`).
- spec-test-3 GC scripts: `ref_test` 71/71 (was 64), `ref_cast` 45/45
  (was 42), `type-subtyping` 75/83 (was 74; the 8 left are
  `assert_unlinkable`), 1-2 s each (`gc-scripts.txt`).
- Gates: 1.0 byte-identical, 2.0 8,724/8,724 and 528/528, 3.0 all counts
  as before.

## The mechanism (translator, `compile.lisp`)

It follows the refined plan in M5-mode-table; it is general, not
specific to `trans`:
1. **Collecting search points.** With `:collect`, a `:choose` returns the
   `append` of every value's results. The index premise `j < |l|` with
   `j` unbound becomes such a search point, so `rec-sub` gives every
   `typeuse*[j]`.
2. **Enumeration variant `R/ENUM<i>`** (mode `(:all i)`): the rules in
   output mode `i` with `:collect`, their results appended. A rule that
   does not compile in that mode is left out and listed in the header.
3. **Premises.** A premise of a relation of the current fuel group, with
   only its last component unbound and at least three components, uses
   `R/ENUM<i>` and searches its results (duplicates removed). This
   applies only in a check variant or an enumeration variant. In a `:fun`
   attempt it made `Reftype_sub` compute a first supertype instead of
   checking one, which I caught by its arity in the test book. It does
   not apply inside an iterated premise, a disjunction or an existential
   loop, which have no search points (`:no-search`). In a check variant
   of the same relation, a result equal to the premise's last input is
   skipped: in `trans` the witness `ht' = ht_1` turns the second premise
   into the goal, and without the skip the search would ask itself again
   until the fuel ends.
4. **Made on demand inside the group** (`crel-form`): the group is
   compiled, the demanded variants until no new one is demanded, then
   the group again with them, then the variants. They are fuelled like
   the group's relations and belong to its mutual recursion. Two are
   made: `HEAPTYPE_SUB/ENUM2` and `DEFTYPE_SUB/ENUM2` (`def` and
   `Deftype_sub/super` call each other).

The name suffix is `/ENUM<i>`, because `R/ALL<k>` already names the
compiler's aux functions for iterated premises.

## Completeness: the rules the enumeration leaves out

The check variant's `trans` is: some `y` in `ENUM(ht_1)` with `y <> ht_1`,
`Heaptype_ok(C, y)` and `C |- y <: ht_2` (the full relation, recursively,
with `trans`). Take a derivation of `ht_1 <: ht_2` that ends in `trans`
through `y'`. Its left premise `ht_1 <: y'` ends in some rule `r`, and
`trans` can be assumed not to be `r` (re-associate). If `r` is
enumerated, its output `y1` is in `ENUM(ht_1)`, and `y1 <: ht_2` follows
by `trans` from `y1 <: y'` and `y' <: ht_2`. The left-out rules
(header):
- **`trans`**: by construction; the check variant chains the steps.
- **`bot`** (`BOT <: ht`): then `ht_1 = BOT`, and `BOT <: ht_2` holds by
  `bot` directly.
- **`none`, `nofunc`, `noexn`, `noextern`** (`NONE <: ht` if `ht <:
  ANY`, ...): then `ht_1 = NONE`, and `ht_2` is above a type of the
  `any` hierarchy. The hierarchies are disjoint and each has one top, so
  `ht_2 <: ANY`, and `NONE <: ht_2` holds by `none` directly. The same
  holds for the other three.
- **`typeidx-r`** (`ht <: _IDX x` if `ht <: C.TYPES[x]`): an intermediate
  `_IDX x` can be replaced by `C.TYPES[x]`. On the right side,
  `_IDX x <: ht_2` comes from `typeidx-l` (`C.TYPES[x] <: ht_2`), so the
  chain goes through the defined type, which the induction reaches.
- **`Deftype_sub/refl`** (equal after `$clos_deftype`; the output is
  under a function, so it is not computable): an intermediate type equal
  up to closure. The rules that take a step from a defined type (`struct`,
  `array`, `func` through `Expand`, `super` through its declared
  supertypes) depend only on the type up to closure. So the step can
  start from `ht_1` itself.

The last two arguments are made from the rules, not checked by a test.

## Data

`data/trans-M5-2026-11-15/`: `t5-subtyping.txt` (46 of 46),
`typing-cases-after-trans.txt` (the M6 cases),
`gc-scripts.txt` (six GC scripts before and after),
`wasm3-header-enum.txt` (the header lines on the variants).
