# The theorem: stated for any machine and proved at run level

- Milestone: E3 (item 1 and item 3 done; item 2 open)
- Date: 2026-11-15
- Repo commit: this note's commit
- Status: draft (item 2 is open)
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

## Open questions

- Should `:stuck` carry a claim (the spec is stuck too)? It needs the
  failure of all 218 rules on the machine's stuck states. Not needed for
  the litmus test.
- A liveness statement (the machine does not stutter forever) is not part
  of the theorem. It follows from the E5 argument that a clock-0 step
  shortens the instruction list.

## Data

`engine/theorem/simulation.lisp`; `make -C engine check` certifies it and
fails if an engine book contains `skip-proofs` or `defaxiom`.
