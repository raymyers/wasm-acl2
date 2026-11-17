# Review: where the gates cannot see a wrong argument

- Milestone: cross-cutting (model-choice item 5 of the prep: the soundness
  argument for each counted override, the nondeterminism policy, anything
  "sound but incomplete"). Its main finding lands in M5
- Date: 2026-11-14
- Repo commit: 689e678 plus this note's commit
- Status: final for what was reviewed; the "not reviewed" list is open
- Feeds wasm3 plan: §5 M5 (termination of the type group), §7 (risks)

## Summary

One new defect, found by running the generated code: in the 3.0 type
group the generated termination check ("the callee's inputs are smaller")
cuts valid derivations. Any rule that passes its arguments unchanged to
another relation of the group, or looks a type up in the context, never
fires. **9 of 22 type cases are right**; `valtype_sub (ref i31) <: (ref
null i31)` is rejected. Recommended: fuel instead of the size check for
this group. The config entries themselves hold up. Three kinds of silent
single choice are not reported anywhere.

## 1. The termination check is incomplete for the type group (new)

Every recursive premise in a `rec` group is preceded by a generated test:
the callee's inputs must be smaller (`acl2-count`) than the caller's. The
1.0 plan justified it with "derivations never need a subgoal that is not
smaller". That holds for 1.0 and 2.0, whose only `rec` group is
`Instr_ok`/`Instrs_ok` (largest group: 2 members). It is false for the
19-relation 3.0 group, in three ways:

| Shape | Example | Why the check fails |
|---|---|---|
| Delegation with the same arguments | `Valtype_sub/ref` to `Reftype_sub`; `Storagetype_sub/val` to `Valtype_sub`; `Heaptype_sub/def` to `Deftype_sub`; `Valtype_ok/ref` to `Reftype_ok` | equal size is not smaller |
| Lookup in the context | `Heaptype_sub/typeidx-l`: `_IDX x` becomes `C.TYPES[x]` | the defined type is larger than the index |
| A larger context | `Deftype_ok`: premise under `C, RECS subtype^n` | the inputs grew |

Measured (`data/typing-M6-2026-11-14/results-3.0-types.txt`, 22 cases
with two defined struct types, one a declared subtype of the other):

| Case | Expected | Got |
|---|---|---|
| `valtype_sub (ref i31) <: (ref null i31)` | T | NIL |
| `reftype_sub` on the same pair | T | T |
| `valtype_ok (ref null i31)`, `deftype_ok A` | T | NIL |
| `storagetype_sub i32 <: i32`, `fieldtype_sub` on an `i32` field | T | NIL |
| `(type 0) <: struct`, `(type 1) <: (type 0)`, `A <: (type 0)` | T | NIL |
| `heaptype_sub B <: A` (declared supertype) | T | NIL |
| `deftype_sub B <: A` | T | T |
| the 3 negative cases | NIL | NIL |
| total right | | **9 of 22** |

(Two of the 13 misses, `A <: eq` and `none <: struct`, are `trans`.)

No probe number shows this. All 19 relations "translate", and the check
is in code that compiles. It also explains part of the instruction-typing
misses: a reference operand reaches `Valtype_sub`.

**Recommendation.** For this group, replace the size check by fuel:

- each relation function takes a fuel argument, returns `nil` at zero and
  passes one less to every relation it calls in the group;
- callers outside the group keep the present names and arities through an
  entry function that supplies the bound, as memoized relations already
  have an entry and an inner function;
- chosen per group by a counted config entry, so `Instr_ok`/`Instrs_ok`
  and with them 1.0 and 2.0 stay as they are.

Why fuel and not a finer order: delegation alone could be ordered by a
rank on the relations, but lookups and growing contexts cannot, and
`trans` needs fuel anyway (M5-mode-table). Fuel is also a measure ACL2
accepts without proof, which helps M9. Its cost: a search that fails
through a cycle runs until the bound, so the bound must be small enough
for the Lisp stack and large enough for real types (the `Steps` bound of
1,000,000 is too deep; something like the type nesting depth times the
number of types). An invalid context can be cyclic, a valid one cannot.

This comes **before** `trans` in M5: without it the enumeration for
`trans` would recurse into relations that still cut.

### Done (2026-11-14, user go-ahead)

Implemented as recommended: config `(:fuel ... :rels ("Heaptype_ok"))`
makes the group of a listed relation a fuel group (`fuel-wrap` in
`compile.lisp`; bound `(%TFUEL)` = 10,000 in `rt/prelude.lisp`).

- The same 22 cases: **20 right** (9 before). The 2 left are the `trans`
  cases. The 23 instruction cases are unchanged (18 right).
- 3.0 probe: same stubs and dropped rules; 19 more defuns (the entries).
- 1.0: every definition byte-identical. `gen/wasm-1.0/package.lsp`
  imports one more runtime symbol (`%TFUEL`), since every generated
  package imports all names of `rt/`. `make check` and `make check-2.0`
  pass.
- Not exercised: a search that really runs to the bound. The cyclic
  context I tried (a type whose declared supertype is its own index)
  answered at once. So the stack-safety of 10,000 is an estimate.

## 2. Config entries

| Entry | Versions | What tests cannot see | Verdict |
|---|---|---|---|
| `:split Step ctxt-instrs` (redex strategy) | all | whether restricting the redex to "the trailing values and the first non-value instruction" loses steps | **Holds for 3.0.** No value is itself reducible in the pinned 3.0 (`REF.NULL ht` is an instruction that reduces to the value `REF.NULL_ADDR`), so the hole of an evaluation context is at the first non-value. Rules that consume instructions after it (`trap-instrs`, `throw_ref-instrs`) match the whole sequence under `Step/pure` or `Step/read` before the context rule is tried. The same result is reached, but possibly in a different number of steps (`v TRAP a b` takes two). So a proof of step-for-step agreement with the generic search (wasm1 T8) would fail; agreement of results is the right statement |
| `:sized` (`len = \|\|BX\|\|`) | all | whether "parse the next item from exactly `len` bytes" is what the lost premise meant | **Holds.** The generated code takes `len` bytes, parses the item from them and requires nothing left. That is the premise |
| `:decreasing` (`Instr_ok`, `Instrs_ok`) | all | whether the order cuts derivations | Holds for what it covers; under option C `Instrs_ok` is overridden. The type group is section 1 |
| `:memoize` | all | nothing: `hons-copy` is the identity | Holds |
| `:witness` | all | whether one witness is enough | Written per entry. Under option C the 3.0 entry shrinks to `Ref_ok`, `Externaddr_ok` |
| `:def utf8` | all | the hand-written inverse | **Known gap**: accepts malformed UTF-8 (39 cases, M2) |
| `:builtins` (11 choices, host) | 3.0 | whether each choice is V8's | Not checkable before M1 |
| `:rel-override Module_ok` | 1.0 | whether the hand-written staging equals the rule | Tested only (T6, T7); no argument is written |
| `:il-patch` | 1.0, 2.0 | whether the source is really wrong | The probe reports when a patch no longer applies; fine |

## 3. Existential searches (G5, G8)

Both are sound (a found value satisfies every premise) and complete
(every candidate is tried: all indices below `|l|`, every value of the
finite types). They only run in check mode, and the other premises may
not bind variables, which is checked. No gap found.

## 4. Single choices that no report lists

The witness rule covers values taken from an output variant. Three other
places pick one value silently:

| Place | What is chosen | Where it occurs (3.0, D3 scope) |
|---|---|---|
| `x <- e` with `x` unbound | the first element of `e` | 14 premises, counted in the source and not by the translator: the numeric results (`c <- $binop_(...)` and the like, 10), `$inv_lanes_` (3), `$hostcall` (1 of its 2). These are the D4 nondeterminism sites: the policy is enforced by the **order of the list** a builtin returns. M1 should state that as the builtin contract |
| `a \/ b` that binds variables | the first disjunct that holds | not counted |
| a `:fun` relation called with its output already known | the first rule's output is compared with the known value | not counted (mode-table hand-over item 4) |

The last two need a counter in the translator, like the witness sources.

## 5. Not reviewed

- `rt/` (hand-written numerics): guarded by the V8 vectors, not read.
- The grammar translation (PEG ordered choice against the declarative
  grammar): 98.3% of spec-test-3 modules decode; the 1.7% are open in M2.
- This session's own translator changes beyond what the 1.0 and 2.0
  gates and the 45 cases above exercise.

## Data

`data/typing-M6-2026-11-14/`: `cases-3.0-types.lsp`,
`results-3.0-types-before-fuel.txt`, `results-3.0-types.txt` (run by the
same `run.sh`).
