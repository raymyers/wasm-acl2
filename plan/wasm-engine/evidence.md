# Evidence that the engine runs the generated WASM 3.0 semantics

Written 2026-11-17 for the ACL2 Workshop. It gathers what the notes,
recorded data and certified books of [plan.md](plan.md) show about one
question: when the engine runs a module, does it compute what the
generated semantics (`translate/gen/wasm-3.0`, `W3T::STEP`) defines?
Whether that semantics is the WebAssembly spec is a separate question,
answered in [../wasm3-translation/evidence.md](../wasm3-translation/evidence.md).

The proof facts were checked on 2026-11-17 (`make -C engine check`
passes: 16 books, no `skip-proofs`, no `defaxiom`). The test figures are
the recorded ones of 2026-11-15 and 2026-11-16; they were not run again
for this document.

**In one paragraph.** There is no end-to-end theorem yet. The engine is
two machines. The list machine applies the semantics' own rule functions,
so no instruction is written twice; that its step is a spec step is
proved for the steps that stand for no spec step and tested for the
others (10,050 steps compared one by one, 33,113 spec-test commands, 0
disagreements in the integer core). The fast machine, which runs the
demos, is proved equal to the list machine step by step
(`FAST-STEP-REFINES`), with `call_ref` left out; that its invariant
survives a step, and so the statement about a whole run, is not proved
but tested (32,649 commands with equal final states, 0 different). The
TeX run adds parts with no proof and little test: 18 host functions and
a run loop in raw Lisp.

## 1. The claim, in layers

```
W3T::STEP                 the generated semantics (spec configurations)
   ^   (A) machine-abs: a list-machine step is CLOCK spec steps
list machine              engine/machine/machine.lisp   MACHINE-STEP
   ^   (B) fm->ms: a fast-machine step is a list-machine step
fast machine              engine/fast/fast.lisp         FAST-STEP (stobj, byte array)
   ^   (C) the driver: loader, run loop, host functions
a run of a module         engine/slides, engine/tex
```

| Layer | Proved | Tested only | Neither |
|---|---|---|---|
| Run-level theorem for any machine | all of it (`ENGINE-RESULT-IS-SPEC-RESULT`) | | |
| (A) list machine | invariant kept; results are terminal; clock-0 steps | clock-1 steps (tests 1, 2) | |
| (B) fast machine | one step, all rules but two | invariant kept, whole runs (lockstep, test 3) | `call_ref` of a host function |
| (C) slides driver | | pixels equal to V8's, 7 of 7 | |
| (C) TeX driver | | | host functions, run loop, `data.drop` shortcut |

## 2. How it was built

Three choices in the construction carry much of the argument.

- **The rule functions are the spec's.** The translator emits one ACL2
  function per reduction rule (212 of them, `*step-rules*`). Both
  machines call these functions (`apply-rule`); neither contains a
  second definition of what an instruction does. What the machines add
  is structural: an explicit control stack in place of nested
  `LABEL_`/`FRAME_`/`HANDLER_` terms, the choice of the redex, and (fast
  machine) memory 0's bytes in an array.
- **Fast paths are proved, or exact.** The fast machine's shortcuts
  (memory rules reading the array, six hot instructions) each have a
  lemma that they equal the general path. A rule with no such lemma goes
  through a fallback that puts the bytes back, applies the rule function
  on the full store, and copies the result out. A result the fast
  machine cannot hold stops it with `:unsupported`; it does not guess.
- **Test before proving** (decision D7). Every layer was compared with
  the layer above on concrete runs before any proof was tried, so the
  theorems below were stated about machines that already agreed on the
  tests.

Loading uses the spec, not the engine: the generated decoder and the
generated `$instantiate`/`$invoke` build the initial configuration.

## 3. What is proved

All in certified books; `make -C engine check` fails if a book contains
`skip-proofs` or `defaxiom`.

### 3.1 The run-level theorem, for any machine

`engine/theorem/simulation.lisp`, `ENGINE-RESULT-IS-SPEC-RESULT`: for a
machine given as constrained functions with four constraints (C1: a
step keeps the invariant; C2: the abstraction of a step is `clock` spec
steps; C3: a result state does not step in the spec; C4: a machine with a
result has stopped), if the machine stops with a result within `n` steps then
`STEPS/%FUEL` on the abstraction of the start gives the abstraction of
the end, for any fuel above the run's clock sum. To use it for a machine
one proves C1 to C4 and instantiates.

### 3.2 The list machine (layer A)

| | Book | Theorem |
|---|---|---|
| C1 | `machine/ok.lisp` | `machine-step-preserves-ok` |
| C3 | `machine/terminal-ok.lisp`, `rules/terminal.lisp` | `machine-result-is-terminal` (a value sequence, `TRAP` alone and an uncaught exception do not step; one generated lemma per rule function and search function) |
| C2, clock 0 | `machine/clock0.lisp` | `machine-clock-0-simulates`: value pushes, entering a label, handler or frame, and stops leave the abstraction unchanged |

Not proved: C2 for the clock-1 steps (a rule applied to a redex inside
the control stack is a `STEP` of the whole configuration). This is
milestone E11 and is the main open proof.

### 3.3 The fast machine (layer B)

`engine/fast/refine-op.lisp`, `FAST-STEP-REFINES`:

```lisp
(implies (and (fmp fm) (fast-inv-store (fm-store fm)) (ctrl-kinds-ok (fm-ctrl fm))
              (not (equal (entry-kind (car (fm-is fm))) :call_ref))
              (not (equal (fm-status (fast-step fm)) :unsupported)))
         (equal (fm->ms (fast-step fm)) (machine-step (fm->ms fm))))
```

In words: for a well-formed stobj whose store is the fast store and
whose control entries are labels, handlers or frames, one step of the
fast machine, seen as a list state with the bytes put back, is one step
of the list machine, unless the instruction is `call_ref` or the fast
machine refuses. It is not limited to the integer core: it holds for
every rule with a lemma, floats included.

Under it:

- `frame.lisp`: a rule that is neither pure nor a memory rule ignores
  the bytes (per rule).
- `memory.lisp`, `refine-mem.lisp`: the fast versions of all 19 memory
  rules equal the rules on the full store.
- `refine.lisp`: the fallback is exact; per-rule facts for 88 of the 90
  fallback rules.
- `refine-hot.lisp`: the six fast paths (`local.get`, `local.set`,
  `local.tee`, `binop`, `relop`, `br_if`) equal the general path.
- `refine-step.lisp`: one statement per rule for 210 of 212 rules, and
  per opcode for every opcode but `call_ref`.

Not proved:

- **The invariant across a step**: that `fmp`, `fast-inv-store` and
  `ctrl-kinds-ok` hold again after `fast-step`. Without it the step theorem
  does not chain into a statement about `fast-run`. Parts exist: the
  array stays a byte list across any rule; the store invariant is kept
  by the frame-safe rules.
- **Loading**: that `fm-load-ms` gives a state with the invariant.
- **`call_ref` of a host function**: its two rules have no lemma.

`frame`, `refine` and `refine-step` each end with a check that the rules
without a lemma are exactly the recorded ones. Before 2026-11-17 the
fallback that keeps one hard rule from stopping a book had also hidden
two interrupted proofs; that can no longer certify.

## 4. What is tested

| Test | Compares | Result | Record |
|---|---|---|---|
| 1 | At every step of every benchmark: `(machine-abs (machine-step s))` against the spec stepped `(machine-clock s)` times | 10,050 steps in 10 runs, 0 disagreements, including a trap and an uncaught exception | [E6-list-machine](notes/E6-list-machine.md) |
| 2 | List machine against the generated semantics, per command of the 258 spec-test-3 scripts | 33,113 commands agree (14,303 in S0, 17,991 in S1, 176 in S2, 66 in S3); 24,773 stop at instructions outside the subset; none differs in S0 | [E6-list-machine](notes/E6-list-machine.md) |
| Lockstep | Fast machine against list machine at every step of the benchmarks | 0 disagreements | [E7-fast-machine](notes/E7-fast-machine.md) |
| 3 | Fast machine against list machine, final states with memory, per command of the 258 scripts | 32,649 equal, 24,726 `:unsupported` on both in equal states, 0 different; 7 scripts stopped at 900 s with every command run agreeing | [E7-fast-machine](notes/E7-fast-machine.md) |
| Slides | Engine's framebuffer against V8's on the same module | 7 of 7 slides identical | [E12-slides](notes/E12-slides.md) |

What each one supports:

- **Test 1 is the missing theorem C2, checked on concrete states.** It
  is the strongest evidence for the open part of layer A, and the
  narrowest: ten programs.
- **Test 2** covers breadth: every instruction of the subset that the
  spec suite exercises, compared with the semantics itself, not with
  another implementation.
- **Lockstep and test 3** are layer B's run-level statement on concrete
  runs: they exercise the invariant that the step theorem assumes.
- **The slides** are the only comparison with an independent
  implementation, and the only end-to-end one. They also depend on the
  translation being right, which the other tests do not.

Test 3 found a real bug: the memory fast paths assumed the store has one
memory. The refinement lemmas already had that as a hypothesis; the
machine now checks it and takes the exact fallback otherwise. So the
tests can find what the proofs had not yet covered, and the proofs'
hypotheses were the right place to look.

Two S1 lines of test 2 were reported different; both were printed after
the time limit signalled the session, were re-runs of commands that had
agreed, and agree on every replay.

## 5. The two demos

### Slides (`engine/slides`)

A renderer compiled to WebAssembly, using the integer core only, no host
functions. Evidence: layers A and B as above, plus pixel equality with
V8 on all 7 slides. It is not inside the proved subset until C2 is done.

### TeX (`engine/tex`)

`tex.wasm` on the fast machine: 606,084,354 instructions and 63,744 host
calls for the 33-slide deck. Beyond layers A and B it rests on parts
with no proof:

- **The 18 host functions** (files, terminal, date) are raw Lisp in
  `texrun.lisp`. They read and write the memory array directly and do
  not go through the spec's `$hostcall`. Evidence: the output is the
  deck.
- **The run loop** is raw Lisp: it calls `WE::FAST-STEP` for every
  instruction and the host functions between them. No theorem about a
  run covers it.
- **`data.drop`**: the driver applies the rule to the state without the
  bytes, to avoid copying 72 MB forty times. That the rule ignores the
  bytes is assumed; it has no frame lemma.
- **`f32` instructions**: covered by `FAST-STEP-REFINES` (layer B); in
  layer A they are outside the integer core, with test 2's S1 commands
  as evidence.
- **No reference comparison**: the DVI has not been compared with
  another TeX's.

Not checked: whether the run executes `call_ref`, the one opcode outside
the step theorem.

## 6. Threats to validity

- **Layer A's open step is the common one.** Almost every step of a run
  is a clock-1 step. The evidence there is by construction and by test.
- **The tests share the semantics.** Tests 1 to 3 compare the engine
  with the generated semantics or with itself. They say nothing about a
  translation error; only the slides and the spec suite do.
- **The step theorem has hypotheses nobody has discharged for a run.**
  In particular `:unsupported` is excluded by hypothesis, and the
  invariant is assumed at every step.
- **The benchmarks are small** next to the TeX run (10,050 compared
  steps against 606 million executed).
- **Trusted throughout**: ACL2 and SBCL, the translator and SpecTec, and
  for TeX the raw-Lisp parts above.

## 7. What would strengthen it

Cheapest first.

1. An opcode census of the TeX run: which rules it executes, so the
   gaps that matter for the demo are known (in particular `call_ref`).
2. A DVI comparison: the same deck through the same e-TeX revision
   natively, byte for byte. The only test that would cover the host
   functions.
3. Lockstep on a sample of the TeX run between host calls.
4. The fast machine's invariant across a step, then `fast-run` refines
   the list machine's run.
5. C2 for the clock-1 steps of the integer core (E11), then the
   end-to-end theorem by functional instantiation of 3.1.
