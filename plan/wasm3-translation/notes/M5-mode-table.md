# Mode table: design, and the part that is implemented

- Milestone: M5 (item 1: mode table design: inference per relation, any
  output positions, existentials)
- Date: 2026-11-14
- Repo commit: f5d4bbb plus this note's commit
- Status: final for the design and the implemented core; the hand-over
  list at the end is open
- Feeds wasm3 plan: §4 (modes), §5 M5 and M6, §6 (config budget), §7 (risks)
- Inputs: [P4-mode-table-design](../../wasm3-translation-prep/notes/P4-mode-table-design.md),
  [P1-typing-root-causes](../../wasm3-translation-prep/notes/P1-typing-root-causes.md)

## Summary

A mode is a set of output positions, and a relation has one primary mode
plus variants. The translator can check two of the three properties a mode
needs (every rule compiles; no rule is lost against the check variant). It
cannot check the third (one witness is enough), so that one is now an
error unless a counted config entry accepts it. With this, 3.0 needs **0
declared modes instead of 22**, with the same stubs (2) and dropped rules
(2). 1.0 definitions are byte-identical. A new finding: `Heaptype_sub/trans`
is **not admissible**, so it cannot simply stay dropped.

## The design

### 1. What a mode is

A mode of a relation with n components is the list of its output
positions. The other positions are inputs. The function returns `t`/`nil`
for no output, `(list out)` for one, and `(list (list out_i out_j ...))`
for several.

| Old name | Output positions | Function |
|---|---|---|
| `:check` | none | `R` |
| `:fun` | (n-1) | `R` |
| `:fun2` | (n-2 n-1) | `R` |
| `:split` | second half of a last component `c(a, b)`; else (n-1) | `R/SPLIT` |
| `:multi` | two modes at once: `:check` and `:split` | `R` and `R/SPLIT` |
| new: `(:out i j ...)` | any positions | `R/OUT<i><j>...` |

A relation has a **primary mode** (the function named `R`, the interface
for tests and drivers) and **variants** that exist because some premise
needs them.

### 2. Three properties of a mode, and who checks each

| Property | Meaning | Checked by |
|---|---|---|
| Consistent | every rule can be scheduled: inputs bind what the premises need, and the outputs are bound at the end | the compiler (an error per failing rule) |
| Complete against the check variant | no rule is dropped only because of the mode | the compiler (rules dropped from an output variant) |
| One witness is enough | a premise that takes an output and then constrains it loses no derivation | nobody: it is a property of the type system (principal types, determinism) |

The old inference scored attempts by failing rules only, which is property
1. It could not see property 3, and that is how `:multi` "compiled"
`Heaptype_sub/trans` with one arbitrary `heaptype'`.

The rule for property 3 (the **witness rule**): a premise that takes a
value from an output variant that drops rules is an error, "witness
choice". A counted config entry `(:witness "label" :rels ("R" ...) :reason
...)` accepts a relation as a witness source and holds the argument. So
every single-witness assumption is either rejected or written down.

What the witness rule does not cover: a `:fun` relation is still assumed
to be functional (first rule that applies), also when a caller passes it
a known output and compares. That assumption is as old as the translator
and is not listed anywhere yet (hand-over item 4).

### 3. Inference

For each relation or `rec` group, in this order:

1. **All `:fun`.** If every member compiles: done. (As before, a group
   that calls a `:multi` relation is then compiled `:multi`.)
2. **Demote to a fixpoint.** Members that fail become `:check` and the
   group is compiled again. A member that compiled in `:fun` only because
   it took an output from a member that is now `:check` fails in turn. This
   repeats until no `:fun` member fails. Modes only move down, so the
   result is the assignment with the most `:fun` members in which every
   `:fun` member compiles. The old inference did one round and then gave
   up; this is what "inference per relation" means here.
3. **`:multi` for all members**, compiled to a fixpoint of the witness
   rule: a pass records which output variants dropped rules, and if a new
   one is not an accepted witness source, the pass is repeated, now with
   "witness choice" errors at the premises that used it.
4. **No assignment compiles every rule**: the attempt with the fewest
   failing rules is emitted without them (per-rule stubs). On a tie the
   earlier attempt wins, so `:fun` is kept when nothing is better.

Then, independently of the group's own modes:

5. **Variants on demand.** When a rule is stuck (no premise can run) and a
   premise calls a relation of an earlier form with some components
   unbound, the translator makes the variant whose outputs are exactly
   those components. It is used only if every rule of the relation
   compiles in that mode. Otherwise the premise fails as before, visibly.
   The variant is emitted just before the first form that calls it.
   Demand is the last resort, after the tests, the ordinary premises and
   the bounded existential searches (G5, G8), so it never changes a rule
   that compiles without it.

Declared modes (`:modes`) still override step 1 to 4 for one relation.
No config uses them now.

### 4. Why demand, and why only as a last resort

The right mode of a relation depends on its callers, not on how many of
its rules compile. `Step_read` must return the next configuration because
`Step` needs it. `Heaptype_ok` must be a check because every caller knows
the heap type. Callers come after callees in the IL, so the group's own
inference (steps 1 to 4) cannot see them. Step 5 is where demand enters.

The full demand-driven design would derive every mode from the callers,
including the variants of a `rec` group. That would replace `:multi` by
demanded variants and stop emitting variants nobody calls (2 of 7 in 1.0,
7 of 15 in 3.0, measured below). It changes 1.0 output, so it is a
separate step (hand-over item 1).

## What is implemented (in `translate/il2acl2/compile.lisp`)

| Piece | Functions | Effect |
|---|---|---|
| Demotion to a fixpoint | `crel-demote`, `fun-members` | type group found as all `:check` |
| Witness rule | `witness-choice-p`, `crel-members-w`, config `:witness` | `trans` fails visibly in `:multi` too |
| Emit the best attempt | `crel-partial` | type group emitted `:check`, not `:fun` with 22 rules dropped |
| Modes `(:out ...)` and variants on demand | `crule-premise-demand`, `demands-of`, `resolve-demand`, `cform-d` | `Eval_expr` gets `EVAL_EXPR/OUT23` without a declaration |
| Report | probe: witness sources, variants, and only the final dropped rules | |

## Measured results

All from `make probe` (11 s per run) and `make gen`; data and scripts in
[data/probe-M5-2026-11-14](data/probe-M5-2026-11-14/).

| | Before | After |
|---|---|---|
| 3.0 (D3 scope) declared modes | 22 | **0** |
| 3.0 stubs / dropped rules | 2 / 2 | 2 / 2 (the same ones) |
| 3.0 final modes `:fun`/`:check`/`:multi`/`:closure` | 21/47/15/1 | 22/47/15/1 (`Eval_expr` is `:fun` plus the variant (2 3)) |
| 3.0 config entries | 7 | 7 (`:modes` out, `:witness` in) |
| 2.0 declared modes | 2 | **0** |
| 2.0 stubs / dropped rules / final modes | 1 / 1 / 14,18,8,1 | the same |
| 1.0 final modes | 13/15/7/1 | the same |
| 1.0 `gen/` | | every definition byte-identical; 1 header line added (the new config entry) |
| 1.0 config entries | 7 | 8 (`:witness`) |

The evidence table of the inputs note, row by row:

| Evidence | Result |
|---|---|
| Type group (19): all `:check`, `trans` not hidden | inferred: demotion ends all `:check` with 1 failing rule, `:multi` has 1 too (witness choice), tie goes to `:check` |
| `Instr_ok`, `Instrs_ok`: `:multi` | inferred in 1.0, 2.0, 3.0, with the witness entry |
| `Eval_expr`: two outputs | variant (2 3) on demand |
| `Step`, `Step_read`, `Step_pure`: `:fun` | kept: all three attempts tie at 1 failing rule for `Step_read`, the earliest wins |
| 1.0 unchanged | definitions byte-identical |

### Experiment A: demotion alone is not safe

With the fixpoint but without the witness rule, and nothing declared, the
3.0 type group ends `:multi` with **0 failing rules reported**
(`exp-A-3.0-core.txt`: modes 19/24/41/1, 1 dropped rule in total). The
count improved and the translation got worse: `trans` was compiled with a
single witness. This is why the witness rule comes with the inference and
not after it.

### Experiment B: every single-witness premise

Probes with the `:witness` entries removed list the premises that rely on
one witness (`exp-B-*.txt`):

| Version | Rules that take a value from an output variant that drops rules |
|---|---|
| 1.0 | `Instrs_ok/seq`, `Externaddr_ok/sub` |
| 2.0 | `Instrs_ok/seq`, `Instrs_ok/sub`, `Externaddr_ok/sub` |
| 3.0 | `Heaptype_sub/trans`; `Instr_ok/block`, `loop`, `if`, `try_table`; `Instrs_ok/seq`, `sub`; `Ref_ok/sub`; `Externaddr_ok/sub` |

This answers the open question of P1-typing-root-causes ("which other
rules bind an existential through a split variant"). The accepted sources
are `Instr_ok`, `Externaddr_ok` (1.0), plus `Instrs_ok` (2.0), plus
`Ref_ok` (3.0). The reasons are in the three config files. The 3.0 entry
is marked provisional: whether one witness is enough for instruction
typing under subsumption is the M6 go/no-go, and the six `Instr_ok` /
`Instrs_ok` rules above are exactly where it has to be argued.

### Variants on demand

3.0: 1 emitted, `("Eval_expr" 2 3)`, called by `$evalexprs` and
`$evalglobals`. 1.0 and 2.0: none emitted. Demands that failed (some rule
does not compile in that mode) and variants that compiled but are not
called by emitted code come from discarded attempts; the probe lists them.

### Output variants nobody calls (the case for full demand)

Calls of each `R/SPLIT` in the generated code (`split-calls.txt`): 1.0
emits 7 and calls 5 (`EXPR_OK_CONST/SPLIT`, `FUNC_OK/SPLIT` are never
called by generated code; a test and the `Module_ok` override use
`FUNC_OK/SPLIT`). 3.0 emits 15 and calls 8.

## `Heaptype_sub/trans` is not admissible

M5 item 2 asks whether `trans` can stay dropped. It cannot. Read from the
rules of `2.2-validation.subtyping.spectec` (not from a test run): besides
`trans`, the only rules that can conclude `x <: ANY` are `refl`, `eq-any`
(`EQ <: ANY`), `none`, `bot`, and `typeidx-l`, which only passes the
question on to the defined type. So `I31 <: ANY`, `STRUCT <: ANY` and
`deftype <: ANY` have no derivation without `trans`, and neither has
`deftype <: EQ`. `NONE <: I31` needs `I31 <: ANY` as a premise. The
current 3.0 translation rejects all of them.

The existential searches (G5, G8) do not fit either: `heaptype'` ranges over
all heap types, and the generated termination check (callee inputs smaller
than the caller's) cuts `C ⊢ EQ <: ANY` under `C ⊢ I31 <: ANY`, because
`EQ` is not smaller than `ANY`.

Proposal for M5 item 2, in the terms of this design:

- Take `heaptype'` from `Heaptype_sub` itself in mode `(:out 2)` as an
  **enumeration**: all one-step supertypes of `heaptype_1` that the other
  rules can compute (`eq-any`, `i31-eq`, `struct-eq`, `array-eq`, `struct`,
  `array`, `func`, `typeidx-l`, `rec-struct/array/func`, and `rec-sub` over
  every index j). Then check `heaptype' <: heaptype_2`. An enumeration
  variant returns every witness, so the witness rule is satisfied without
  a config entry, except for the rules it drops (`none`, `nofunc`, `noexn`,
  `noextern`, `bot`, `typeidx-r`, `def`), which need a short argument each.
- Termination by fuel, as the `:closure` mode already does, since "one
  step up" has no syntactic measure.
- If that is too much machinery for one rule, a `:rel-override` of
  `Heaptype_sub` with the same algorithm is the fallback (1 config entry).

Either way `trans` is the first user of an **enumeration variant** (all
witnesses instead of the first). That is the general answer of this
design to an existential that the inputs do not determine.

## Handed over (not implemented)

1. **Demand inside a `rec` group** (recursive variants), which lets
   demand replace `:multi` and the propagation rule. Changes 1.0 output by
   removing uncalled variants, so it needs its own milestone statement.
2. **Enumeration variants** and fuelled recursion for `Heaptype_sub/trans`
   (above), or the override.
3. **The second half of `c(a, b)`** is still its own mode (`:split`), not
   an `(:out ...)` position. Positions as paths would unify them.
4. **A list of the `:fun` relations called with a bound output.** These
   rest on "functional" without a check. A cheap sufficient check exists
   (one rule, or rules whose input patterns start with different
   constructors); the rest would be listed like witness sources.
5. **Mode manifest**: `gen/wasm-1.0/modes.lsp` and `t0-modes` do not know
   `(:out ...)` variants yet (none exists in 1.0).
6. **`Module_ok`** (M7): its staged contexts are not helped by variants
   on demand; the probe shows the same errors as before.

## Risks

- Step 4 no longer prefers `:fun` when `:fun` has more failing rules than
  `:check`. If a translator gap makes a `Step` rule fail only in `:fun`,
  the relation becomes `:check` and its callers fail loudly (stubs), not
  silently. Today all three attempts tie for `Step_read`. Full demand
  (item 1) removes the risk.
- A variant on demand is accepted when every rule compiles. It is then
  assumed functional like any `:fun` relation (item 4).

## Data

`data/probe-M5-2026-11-14/`: final reports and failing-rule lists for
1.0, 2.0 and 3.0 (D3 scope); `exp-A-3.0-core.txt`; `exp-B-*.txt`;
`split-calls.txt`; `run.sh` (how each file was made).
