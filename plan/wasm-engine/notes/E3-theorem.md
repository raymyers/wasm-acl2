# The theorem: stated for any machine and proved at run level

- Milestone: E3 (all three items; item 2 in the second session, 2026-11-15)
- Date: 2026-11-15
- Repo commit: this note's commit
- Status: final
- Feeds engine plan: E3, E11, §3 (theorem shape), "Litmus milestones", "Current state"
- Incorporated in engine plan: yes (E3, §3, E11, "Current state")

## Summary

- `engine/theorem/simulation.lisp` certifies with no `skip-proofs` and no
  `defaxiom`. It states the theorem over `W3T::STEP` and
  `W3T::STEPS/%FUEL`, which E2 put in `:logic`.
- The machine is six constrained functions. Four constraints say what a
  machine must satisfy. From them the book **proves** the run-level
  theorem `ENGINE-RESULT-IS-SPEC-RESULT`.
- So the plan's "`skip-proofs` confined to one named event" is not
  needed. What is left for E11 is to prove the four constraints for the
  real machine and to instantiate the theorem
  (`:functional-instance`).
- The theorem is one direction: a result of the machine is a result of
  the spec. A machine that stops without a result claims nothing.

## Findings

### The statement

```lisp
(defun stepn (k c)            ; exactly k spec steps: (list c') or nil
  (if (zp k) (list c)
    (let ((r (w3t::step c))) (and r (stepn (1- k) (car r))))))

(defthm engine-result-is-spec-result
  (implies (and (m-ok s)
                (m-result-p (m-run n s))
                (natp fuel)
                (< (m-clocks n s) fuel))
           (equal (w3t::steps/%fuel fuel (m-abs s))
                  (list (m-abs (m-run n s))))))
```

`m-run n s` is the machine run for at most `n` steps while `m-running`.
`m-clocks n s` is the sum of `m-clock` over the steps that run took.

Reasons for each hypothesis:

| Hypothesis | Reason |
|---|---|
| `(m-ok s)` | The invariant of E5 (operands are values, lists are true lists, control entries have a known shape). Without it `abs` can build a term in which `ctxt-instrs` picks a different redex. It is a property of states the loader builds, and a step keeps it (C1) |
| `(m-result-p (m-run n s))` | The claim is about runs that end with values or a trap. If the machine's fuel `n` runs out, or the machine is stuck or meets an unsupported instruction, there is no claim |
| `(natp fuel)`, `(< (m-clocks n s) fuel)` | `STEPS/%FUEL` returns `nil` when its fuel runs out. It needs the steps of the run and one more call, the one in which `STEP` returns `nil` |

No typing hypothesis (D2). No hypothesis about host functions: `$hostcall`
is the constrained `%hostcall-hook`, so every theorem about `STEP` holds
for every host.

### The constraints a machine must satisfy

| | Constraint | Milestone that proves it for the real machine |
|---|---|---|
| C1 | `(m-ok s)` and `(m-running s)` imply `(m-ok (m-step s))` | E6 (it is also a good test of the machine) |
| C2 | `(m-ok s)` and `(m-running s)` imply `(stepn (m-clock s) (m-abs s)) = (list (m-abs (m-step s)))` | E11, one group at a time. This is the simulation proof |
| C3 | `(m-ok s)` and `(m-result-p s)` imply `(w3t::step (m-abs s)) = nil` | E3 item 2 below, with the dispatch lemmas of E4 |
| C4 | `(m-result-p s)` implies not `(m-running s)` | by definition of the machine |
| | `(m-clock s)` is a natural number | by definition |

C2 with `m-clock` 0 says `abs` is unchanged (the machine moved a value
from the instructions to the operand stack). The E5 machine has clock 0
or 1 everywhere except bulk memory.

**How a subset is expressed** (the litmus test asks, per group, that the
theorem holds for that subset): the real machine sets its status to
`:unsupported` on an instruction outside the proved subset. Then
`m-running` is false and `m-result-p` is false, so C2 has nothing to
prove for it and the theorem makes no claim. Widening the subset in E11
means moving instructions out of that case. The litmus check "no opcode
of the census is outside the subset" is then a test on the machine's
dispatch.

### The fuel relation (item 3)

Machine fuel `n` counts machine steps. Spec fuel counts calls of `STEP`.
The relation is `m-clocks n s < fuel`. The spec's own top function
`STEPS` uses `(%FUEL)` = 1,000,000, which is far below a MuPDF run, so
the theorem is about `STEPS/%FUEL` with any fuel, not about `STEPS`.

### What was proved here

`m-run-ok` (the invariant holds along a run), `stepn-of-+`,
`m-run-simulates` (`n` machine steps are `m-clocks n s` spec steps),
`stepn-then-no-step-is-steps` (the link from `stepn` to the spec's
`STEPS/%FUEL`), and the theorem. `W3T::STEP` is disabled in the book: the
proofs use only that it is a function. Certification: 2.2 s.

### Item 2, open: facts about the spec alone

- "`STEP` returns at most one result": not needed any more. C2 states the
  result of `STEP` as an equality, and `STEPS/%FUEL` takes the `car`.
- "A value sequence does not step" (C3 for `:done`), and "`TRAP` alone
  does not step" (C3 for `:trap`): needed. Each says that every rule
  function of `STEP`, `STEP_PURE` and `STEP_READ` returns `nil` on that
  input, and that the `ctxt-instrs` search finds no split. With one
  function per rule (E2) each of these is a small lemma; they are the
  same lemmas as the dispatch lemmas of E4, so they belong with E4.

## Item 2: the facts C3 needs, proved (second session, 2026-11-15)

`engine/rules/terminal.lisp` (certifies in 130 s) proves, for any state
`z`, with no `skip-proofs`:

| Theorem | Says | The machine's status |
|---|---|---|
| `step-of-vals` | `(vals-p l)` implies `STEP` of `(z; l)` is `nil` | `:done` |
| `step-of-trap-alone` | `STEP` of `(z; TRAP)` is `nil` | `:trap` |
| `step-of-uncaught-exception` | `(val-p (ref.exn_addr a))` implies `STEP` of `(z; (ref.exn_addr a) THROW_REF)` is `nil` | `:throw` |

`engine/machine/terminal-ok.lisp` (2.5 s) puts them together for the list
machine of E6: `machine-result-is-terminal`, which is **constraint C3**:

```
(implies (and (machine-ok s) (machine-result-p s))
         (not (w3t::step (machine-abs s))))
```

For this, `machine-ok` now ties each result status to its shape
(`status-ok`: `:done` with no instruction and no control entry; `:trap`
with the block `TRAP` alone; `:throw` with one exception reference and
`THROW_REF`), and the machine reports `:trap` and `:throw` only for exactly
`(:TRAP)` and `(:THROW_REF)`. C1 (`machine-step-preserves-ok`) was proved
again with the stronger invariant. **The hypothesis of
`step-of-uncaught-exception`** (the reference is a `VAL-P`) is discharged
by `machine-ok`, whose operand stack holds values only. It is not a
hypothesis of the machine theorem.

How it was proved, and what failed first (raw checkpoints in
`data/e3-c3/attempt1-two-values.txt`):

1. `STEP` on two symbolic values, all rule definitions enabled: failed on
   `STEP_PURE/SEARCH171` (the search of `trap-instrs` for a `TRAP` after a
   prefix of values), which needs an induction.
2. `STEP` on any value list, all rule definitions enabled: stopped after
   359 s, all of it preprocessing (57 prover steps). Expanding `STEP` with
   212 rule definitions enabled builds a term too large to work on.
3. What works: one lemma per function, made by `make-event`. For each of
   the 14 search functions on `STEP`'s path, "returns `nil` on a list
   whose elements are values or `nil`" (what `take` and `nthcdr` of a
   value list give), by the search's own induction: 11 prove; the three
   that do not are `STEP/SEARCH21` (`ctxt-instrs`, which a value list
   never reaches: `STEP/PREFIX7`, the index of the first non-value, is its
   length) and `STEP_READ/SPLIT/SEARCH118`/`119`, which no rule lemma
   needed. Then for each of the 212 rule functions, "returns `nil` on a
   value list", with the rule's definition enabled: all prove except
   `STEP/R-CTXT-INSTRS`, which is in `STEP`'s clique and is opened by an
   explicit `:expand`. The three relations then follow in 0.01 s each with
   every rule function closed.

   The key rewrite rule: an element of such a list never has the head
   keyword of an instruction that is not a value. It must be stated both
   ways round, `(equal (car (car x)) kw)` and `(equal kw (car (car x)))`,
   because ACL2 puts the constant first. The first version had only one
   orientation, and every search lemma failed.
4. The exception case used the same generator on the list
   `(ref.exn_addr a) THROW_REF`. Two rules (`TRAP-INSTRS`,
   `THROW_REF-INSTRS`) search a list that is not all values; they and
   `ctxt-instrs` are proved with their searches expanded. `ctxt-instrs`
   reaches `STEP` of `THROW_REF` alone, proved like `TRAP` alone.

This is the dispatch-lemma machinery that E4 item 4 asks for, in its
first form: per rule function, "fails on inputs of this shape". E11 needs
the same per rule for "the head is opcode k".

## Open questions

- Should `:stuck` carry a claim (the spec is stuck too)? It needs the
  failure of all 218 rules on the machine's stuck states. Not needed for
  the litmus test.
- A liveness statement (the machine does not stutter forever) is not part
  of the theorem. It follows from the E5 argument that a clock-0 step
  shortens the instruction list.

## Data

`engine/theorem/simulation.lisp`; `make -C engine check` certifies it and
fails if an engine book contains `skip-proofs` or `defaxiom`. Item 2:
`engine/rules/terminal.lisp`, `engine/machine/terminal-ok.lisp`,
`data/e3-c3/attempt1-two-values.txt`.
