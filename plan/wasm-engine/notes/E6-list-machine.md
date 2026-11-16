# The list machine: dispatch on the head instruction, the spec's own rule functions on the redex

- Milestone: E6 (items 1 to 4 done; item 5 has two open differences)
- Date: 2026-11-15
- Repo commit: 174d6fb plus this note's commit
- Status: draft (two commands of differential test 2 differ)
- Feeds engine plan: E6, E7 (primitives, rates), E8 (widening), E11 (shape of the simulation lemmas), E3 (constraints C1, C2)
- Incorporated in engine plan: yes (E6, "Current state")

## Summary

- `engine/machine/machine.lisp` is the list machine of
  [E5-machine](E5-machine.md): store, frame, operand stack, instruction
  list, explicit control stack, status. It is in logic mode with every
  guard verified, and certifies in 3.7 s.
- **The machine does not restate any rule.** It picks the redex by the
  head instruction and applies the spec's own rule functions
  (`STEP_PURE/R-*`, `STEP_READ/SPLIT/R-*`, `STEP/R-*`) to it, in the order
  in which `STEP` tries them. The rule table and the function that calls
  a rule by name are made by `make-event` from the bodies of `STEP_PURE`,
  `STEP_READ/SPLIT` and `STEP` (212 rules), so they follow the
  specification when it is regenerated. D6 holds in the strongest form:
  arithmetic, memory and type checks are those of the rule functions.
- **C1 of E3 is proved** for this machine (`engine/machine/ok.lisp`,
  `machine-step-preserves-ok`, no `skip-proofs`).
- **Differential test 1: 0 disagreements** in 10 runs (10,050 machine
  steps, 5,572 spec steps), including a trap and an uncaught exception.
  At every step `machine-abs` after the step equals the spec stepped
  `machine-clock` times.
- **Differential test 2**: over 258 spec-test scripts, 33,113 commands
  give the same result and store as the spec (14,303 inside S0) and 2
  differ (`fib-i32` in `call_indirect.wast`), which are being checked.
- The list machine is already 23 to 27,000 times faster than the spec on
  code without memory traffic (914,349 spec steps/s on the counting loop,
  2 ms against 54 s on the call chain of depth 150). On memory traffic it
  is as slow as the spec, because it uses the spec's memory and rules.
  That is E7.

## Findings

### How a step is made

`i` is the head of `is`. The redex is always a subterm of `machine-abs`,
so a clock-1 step is "a rule function applied to a subterm of the
configuration":

| Situation | Step | Clock |
|---|---|---|
| `i` is a value (`VAL-P`) | push it on `vals` | 0 |
| `i` is `LABEL_`, `HANDLER_` or `FRAME_` | enter it: push a control entry with the current `vals` and `(cdr is)`; for a frame, switch the frame | 0 |
| `i` takes `k` operands | redex = top `k` values and `i`; try the rules of `i`'s opcode; `vals := (drop k vals)`, `is := result ++ (cdr is)`, store and frame from the rule | 1 |
| `TRAP` (`THROW_REF`) with other values or instructions in the block | `TRAP-INSTRS` (`THROW_REF-INSTRS`) on the whole block | 1 |
| block empty, or `BR`, `RETURN`, `TRAP`, `THROW_REF` at the head, inside an entry | rebuild the entry's administrative term around the block; try the rules whose redex is that term (`LABEL-VALS`, `BR-LABEL-ZERO`, `FRAME-VALS`, `RETURN-FRAME`, `TRAP-LABEL`, `THROW_REF-HANDLER-CATCH`, ...); `vals := v`, `is := result ++ r`, pop | 1 |
| block empty with no entry; `TRAP` alone with no entry; `(ref) THROW_REF` alone with no entry | `:done`, `:trap`, `:throw` | 0 |
| no rule fires, or a shape is wrong | `:stuck` | 0 |
| the opcode has no rules or no known arity | `:unsupported` | 0 |

The rule results are kept as they are. A result that contains a `LABEL_`
or `FRAME_` term (`block`, `loop`, `call_ref`) is entered by the next,
clock-0 step. So there is no case in the machine for `block`, `call` or
`br`: those are rule functions.

`machine-clock` is 0 when the step leaves `machine-abs` unchanged (a value
push, an entry, a stop), else 1. It is defined from the step itself, so
the clock is 0 for a step into `:stuck` or `:unsupported` too, which C2
needs (those steps change only the status).

**Arities.** Most are fixed by the opcode (`binop` 2, `select` 3,
`call_indirect` 0, ...). Three come from the spec's own functions, as in
the rules: `block`, `loop`, `try_table` from `$BLOCKTYPE_`; `call_ref` from
`EXPAND` of the function's type; `throw` from the tag's type. A first run
had `call_indirect` at arity 1; differential test 2 found it (3 commands
of `block.wast` stuck), and in 3.0 the rule takes no operand (it rewrites
to `table.get`, which takes the index).

**Rule table.** `place-alist` sorts the 212 rule functions by where their
redex is: `(:op KEYWORD)` for `val^k instr` (the keyword from the rule id,
with `IF` mapped to `IFELSE`), `(:entry :l)`, `(:entry :h)`, `(:entry :f)`
for rules whose id names a label, handler or frame, and `:anyprefix` for
`TRAP-INSTRS` and `THROW_REF-INSTRS`. The six rules `STEP/R-PURE`,
`STEP/R-READ` and `STEP/R-CTXT-*` are left out: they are the search the
machine replaces. `THROW_REF` on a null reference is a flat rule
(`THROW_REF-NULL`, arity 1) and is routed to the opcode step.

**Guards.** Every machine function has guard `T` or `(natp n)` and is
guard-verified. The spec functions it calls (`$BLOCKTYPE_`, `EXPAND`,
`VAL-P`, every rule function) are logic mode without verified guards, and
are called through `EC-CALL`. This is how "guards verified" (E6) and D6
fit together. E7 replaces the calls it needs fast by `mbe`.

**Loader.** `ms-of-config` makes a machine state from a spec
configuration, and `machine-abs` gives it back (`abs-of-loader T` in every
run). The configuration comes from the spec's `$instantiate` and
`$invoke`. So module instantiation is still the spec's, including its
recursive memory allocation (E0). E9 needs its own instantiation for
MuPDF's 352 pages. This is the "loader from a decoded module" of the item,
with that limit.

### The invariant and C1 (item 2)

`machine-ok` (in `ok.lisp`): `vals` and every saved `v` are true lists of
values, `is` and every saved `r` are true lists, every control entry is a
five-element list of kind `:l`, `:h` or `:f` with a natural `n`, and a
label's continuation is a true list. The machine checks the two shapes
that it takes from rule results: an administrative term is entered only
if it has exactly four parts with a natural `n` and a true-list body
(`enterable-p`), and the result of `TRAP-INSTRS` must be a true list.
Otherwise the machine is stuck.

`machine-step-preserves-ok` proves C1. The proof needs no fact about any
rule function: the results are opaque (`try-rules` disabled), and every
case keeps the shapes because the machine builds them. Certification of
`ok.lisp`: 10 to 13 s.

One failed attempt, kept here as step.md asks: the first `enter-step-ok`
failed at

```
Subgoal 2.16.3.5'
(IMPLIES (AND ... (NOT (EQUAL (CAR (CAR (MS-IS S))) :LABEL_%{%}%))
              (NOT (EQUAL (CAR (CAR (MS-IS S))) :HANDLER_%{%}%))
              (NOT (EQUAL (CAR (CAR (MS-IS S))) :FRAME_%{%}%)) ...)
```

`enter-step` on a term that is not administrative pushed an entry of kind
`NIL`. `machine-step` never calls it that way, but `enterable-p` now
requires an administrative term, which made the lemma true for any state.

### Differential test 1 (item 4)

`difftest.lsp`, `difftest-run.lsp`; `data/e6-machine/difftest1.out`. The
E0 benchmarks, at sizes the spec can follow at every step:

| Run | Machine steps | Spec steps | Disagreements | Final status | Final = spec's own run |
|---|---|---|---|---|---|
| count 200 | 2,823 | 1,611 | 0 | `:done` | yes |
| memloop 100 | 2,223 | 1,211 | 0 | `:done` | yes |
| nested 50 | 1,923 | 1,211 | 0 | `:done` | yes |
| throw 30 | 1,373 | 701 | 0 | `:done` (465) | yes |
| fac loop 25 | 554 | 300 | 0 | `:done` | yes |
| fac rec 20 | 553 | 255 | 0 | `:done` (20!) | yes |
| calls 20 | 560 | 268 | 0 | `:done` (210) | yes |
| 7 / 0 | 12 | 5 | 0 | `:trap` | yes |
| 7 / 2 | 15 | 5 | 0 | `:done` (3) | yes |
| uncaught throw | 14 | 5 | 0 | `:throw` | yes |

The spec step counts are those of E0 (count: 8 per iteration plus 11).
The four hand simulations of [E5-machine](E5-machine.md) are covered by
these runs (a loop with `br_if`, a call that returns, a trap in nested
blocks, a caught `throw` two frames up). They were not traced row by row.

### Differential test 2 (item 5)

`difftest2-one.lsp`, `difftest2-all.sh`, `difftest2-summary.sh`;
`data/e6-machine/difftest2/` (one output per script and `SUMMARY`). The
T7 driver of spec-test-3 (`translate/tests/spec/t7-lib-3.0.lisp`, used as
a certified book, not changed) runs every script. For each action command
(`action`, `assert_return`, `assert_trap`, `assert_exception`) the same
`$invoke` configuration is run on the spec (T7's `DO-ACTION`, fuel 200,000
spec steps) and on the machine (fuel 2,000,000 machine steps), from the
same script state, and the result and the store after the command are
compared. The script then continues from the spec's state. Modules are
instantiated by the spec. Each command also records the highest D5 group
of an instruction the machine executed (S0 to S3, S4 = outside D5).

Run of 2026-11-15, 258 scripts (all of spec-test-3 but
`skip-stack-guard-page`), 6 at a time, 900 s per script:

| Class | Commands |
|---|---|
| same result and same store | 33,113 |
| different | 2 (see below) |
| machine `:unsupported` (all outside D5) | 24,773 |
| spec out of fuel (not compared) | 45 |
| not an invocation (`get` of a global) | 11 |

| Group | Same |
|---|---|
| S0 | 14,303 |
| S1 | 17,991 |
| S2 | 176 |
| S3 | 66 |
| outside D5, but supported by the generic step | 563 |
| group printed on another line | 14 |

The machine was `:stuck` on no command except the two below. The
unsupported commands stop at GC, i31, reference conversion, table and
segment instructions (`ref.test`, `array.get`, `array.new_data`,
`i31.get`, `table.size`, `data.drop`, ...), none of which MuPDF uses.

256 scripts finished. `call.wast` and `call_indirect.wast` reached the time
limit (the spec is slow on their deep recursions, E0). Every command they
ran before the limit was compared.

The two differences are both in `call_indirect.wast`: `fib-i32` with 2
and with 5. The spec returns 2 and 8; the machine reported `:stuck`. The
first run had `call_indirect` at arity 1 (stuck on 3 commands of
`block.wast`); after the fix these two remained. Run alone (differential test 1 on
`call_indirect.0.wasm`, 80 machine steps, result 2) and in the script with
the earlier commands run on the machine (driver mode `D2-ONLY`), the same
commands agree. So the difference depends on the script state that the
spec's runs of the earlier commands left. A third run of the whole script
with a 2,400 s limit was started to see the stuck state.

### Rates (not an E6 goal; input to E7)

`rate-run.lsp`, `data/e6-machine/rate.out`; spec steps the machine run
stands for, per second, against E0:

| Program | Spec (E0) | List machine |
|---|---|---|
| count 20,000 | 39,604 | 914,349 |
| nested 5,000 | 24,872 | 863,388 |
| throw 3,000 | 23,515 | 348,540 |
| calls depth 150 | 36 | 979,000 |
| memloop 10,000, 1 page | 20,652 | 27,469 |
| memloop 10,000, 16 pages | 4,366 | 1,768 |

The first four lose the search and the depth cost. The memory loop keeps
the spec's cost, since the machine runs the spec's out-of-bounds rules on
the spec's byte list. At 16 pages it is slower than the spec. That was not
investigated, since E7 replaces the memory.

## What this means for E7 and E11

- **E7.** The primitives of the step function are the state accessors
  (`ms-*`, `entry-*`) and `apply-rule`. The stobj machine has to give fast
  versions of `apply-rule` for the rules that touch memory, locals and
  globals, as `mbe` with the rule function as the logical side, and keep
  the store in the stobj. This is the "mbe fast paths" of E5, at the level
  of rules.
- **E11.** Every clock-1 step is a rule function on a subterm of
  `machine-abs`. The simulation lemma for a step is then: `STEP` of the
  whole configuration equals the rule result put back in place. That is
  the context lemma alone, plus the dispatch lemmas of E4 item 4 (no
  earlier rule of `STEP` fires). There is no clean-form lemma per rule to
  write, because the machine never states what a rule does.

## Open questions

- Why the machine is slower than the spec on memory at 16 pages.
- Whether the arity table is complete for S1 to S3 and H. The table has
  entries for all of D5, and test 2 covers the scripts that use them.

## Data

`engine/machine/`: `machine.lisp`, `ok.lisp`, `difftest.lsp`,
`difftest-run.lsp`, `rate-run.lsp`, `difftest2-one.lsp`,
`difftest2-all.sh`, `difftest2-summary.sh`. `data/e6-machine/`:
`difftest1.out`, `rate.out`, `difftest2/SUMMARY` and
`difftest2/D2-LINES.txt.gz` (every `D2-` line of every script; the raw
session outputs, 8.8 MB, are not kept).
