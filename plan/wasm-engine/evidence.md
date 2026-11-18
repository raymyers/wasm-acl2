# Evidence that the engine runs the generated WASM 3.0 semantics

First written 2026-11-17 for the ACL2 Workshop; rewritten 2026-11-18
after V0 to V8 of [plan2.md](plan2.md). It gathers what the certified
books, the notes and the recorded data show about one question: when the
engine runs a module, does it compute what the generated semantics
(`translate/gen/wasm-3.0`, `W3T::STEP`) defines? Whether that semantics
is the WebAssembly spec is a separate question, answered in
[../wasm3-translation/evidence.md](../wasm3-translation/evidence.md).

The proof facts were checked on 2026-11-18 (`make -C engine check`
passes: 36 books, no `skip-proofs`, no `defaxiom`; none of the 67 books
under the theorems has a trust tag). The test figures are those of the
last run of each test, with its date. To check the theorems yourself:
[engine/THEOREM.md](../../engine/THEOREM.md).

**In one paragraph.** There is an end-to-end theorem. For a
configuration of the specification with a memory, run by the function
the drivers call (`engine-run`): however the run ends, the engine is in
a configuration that `W3T::STEP` reaches from the start, and if it ends
with a result, that is the result of the specification's own run
function. No instruction is excluded by a hypothesis; where the engine
cannot follow the semantics (an instruction without rules, a host call)
it stops. The slide renderer runs inside this theorem. TeX does not:
it calls host functions, the engine stops at each, and the driver
resumes it with Lisp code that no theorem covers; what is proved there
is each stretch between two host calls. Not proved anywhere: that the
engine gets to the end, and that the specification also stops where the
engine stops without a result.

## 1. The claim, in layers

```
W3T::STEP                 the generated semantics (spec configurations)
   ^   (A) machine-abs: a list-machine step is CLOCK spec steps
list machine              engine/machine/machine.lisp   MACHINE-STEP
   ^   (B) fm->ms: a fast-machine step is a list-machine step, or is refused
fast machine              engine/fast/fast.lisp         FAST-STEP (stobj, byte array)
   ^   (C) engine-run: load a configuration, run
the engine as called      engine/run.lisp               ENGINE-RUN
   ^   (D) the driver
a run of a module         engine/slides, engine/tex
```

| Layer | Proved | Tested only | Neither |
|---|---|---|---|
| Run-level theorem for any machine | all of it (`ENGINE-RESULT-IS-SPEC-RESULT`, `M-RUN-SIMULATES`) | | |
| (A) list machine | all of it: T1, `machine-result-is-spec-result`, for every running state with the invariant | | |
| (B) fast machine | all of it: one step, the invariant across a step and a run, T2 `fast-result-is-spec-result`; a refused step changes only the status | | |
| (C) the engine as called | all of it: the loader, T3 `engine-run-is-spec-run`, `engine-run-is-spec-steps` | | |
| (D) slides driver | it calls `engine-run` and reads `engine-config` (by reading one file); the hypotheses of T3 are evaluated on each run | pixels equal to V8's, 7 of 7 | decoding and instantiation are the spec's own functions, in program mode |
| (D) TeX driver | each stretch of instructions between two host calls, from the invariant | the invariant at the start of every stretch (checked at run time); the DVI equal to V8's with the original host functions | the 18 host functions, TeX's loader, the `data.drop` shortcut, the run as a whole |

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
  tests. The proofs still found two bugs the tests had not (§4).

Loading uses the spec, not the engine: the generated decoder and the
generated `$instantiate`/`$invoke` build the initial configuration.

## 3. What is proved

All in certified books; `make -C engine check` fails if a book does not
certify or contains `skip-proofs` or `defaxiom`.

### 3.1 The engine as it is called

`engine/run.lisp`. `engine-run n c fm` loads the configuration `c` into
the stobj and runs the fast machine for at most `n` steps;
`engine-config` is the configuration a stobj stands for.

```lisp
(defthm engine-run-is-spec-steps                  ; follows the specification or stops
  (implies (and (config-shape-p c) (fmp fm))
           (equal (stepn (engine-steps n c fm) c)
                  (list (engine-config (engine-run n c fm))))))

(defthm engine-run-is-spec-run                    ; T3
  (implies (and (config-shape-p c) (fmp fm)
                (engine-result-p (engine-run n c fm))
                (natp fuel) (< (engine-clocks n c) fuel))
           (equal (w3t::steps/%fuel fuel c)
                  (list (engine-config (engine-run n c fm))))))
```

- `stepn k c` is exactly `k` steps of `W3T::STEP`. The first theorem has
  no hypothesis about how the run ends: a result, the fuel used up,
  `:stuck`, `:unsupported`.
- The hypotheses about the input: `config-shape-p`, executable, which
  the driver evaluates (the shape `((s; f); instr*)`, a store with every
  field, a memory 0 with a byte list), and `fmp`, which ACL2 guarantees
  of the live stobj.
- `engine-invoke-is-spec-run`: T3 for the configuration the spec's
  `$invoke` builds.

### 3.2 The layers under it

| | Book | Theorem |
|---|---|---|
| Any machine with four properties | `theorem/simulation.lisp` | `engine-result-is-spec-result`, `m-run-simulates` |
| (A) the invariant is kept (C1) | `machine/ok.lisp` | `machine-step-preserves-ok` |
| (A) a result does not step (C3) | `machine/terminal-ok.lisp`, `rules/terminal.lisp` | `machine-result-is-terminal` |
| (A) a step is `clock` spec steps (C2) | `machine/clock0.lisp`, `rules/*`, `machine/op-context.lisp`, `machine/exit-steps.lisp`, `machine/spec-result.lisp` | `machine-step-simulates`, for a symbolic opcode and a symbolic control stack |
| (A) T1 | `machine/spec-result.lisp` | `machine-result-is-spec-result` |
| (A) the supported opcodes | `machine/opcodes.lisp` | `*proved-opcodes*` (48); outside it the machine ends `:unsupported` |
| (B) one step | `fast/refine*.lisp`, `fast/call-ref.lisp` | `fast-step-is-machine-step`: a step that is not refused is the list machine's step |
| (B) no host rule fires | `fast/call-ref.lisp` | `fast-step-refuses-host-call`, `host-rule-fails-on-op-redex` |
| (B) the invariant | `fast/inv.lisp` | `fast-step-keeps-fm-inv`, `fast-run-keeps-fm-inv` |
| (B) T2 | `fast/spec-result.lisp` | `fast-result-is-spec-result` |
| (B) a refused step | `fast/stretch.lisp` | `fast-step-when-refused`: it changes the status and nothing else |
| (B) a run that did not end with a result | `fast/stretch.lisp` | `fast-run-is-spec-steps-or-refused`, `fast-stretch-is-spec-steps` |
| (C) the loader | `fast/inv.lisp` | `fm-inv-of-fm-load-ms`, `machine-abs-of-ms-of-config` |

The fast paths and the fallback, under the step theorem: `frame.lisp`
(a rule that is neither pure nor a memory rule ignores the bytes),
`memory.lisp` and `refine-mem.lisp` (the fast versions of the memory
rules equal the rules on the full store), `refine.lisp` (the fallback is
exact), `refine-hot.lisp` (the six fast paths equal the general path),
`refine-step.lisp` (one statement per rule).

Generated lemma families end with a check that the rules without a lemma
are exactly the recorded ones. What is recorded as without a lemma: the
two host rules of `call_ref` and their place, with the theorems that the
fast machine does not fire them; and the rules without a frame lemma,
which take the fallback, which is proved exact.

### 3.3 What is not proved

- **Progress.** `engine-run-is-spec-steps` is satisfied by an engine
  that stops at once. That the engine reaches the end of a program is
  observed (§4).
- **The other direction.** Where the engine stops `:stuck` or
  `:unsupported`, nothing says the specification stops there (plan2.md
  P2, V10).
- **Host calls.** The engine stops at a `call_ref` of a host function
  (plan2.md P1). Nothing is proved about a host step.
- **A store with no memory** does not meet `config-shape-p`.
- **From the bytes of a module.** `$instantiate` and the decoder are in
  program mode; the theorems start from a configuration.

## 4. What is tested

| Test | Compares | Result of the last run | Record |
|---|---|---|---|
| 1 | At every step of every benchmark: `(machine-abs (machine-step s))` against the spec stepped `(machine-clock s)` times | 10 runs, 0 disagreements (2026-11-18, after the last change of the list machine) | [V4-exits](notes/V4-exits.md) |
| 2 | List machine against the generated semantics, per command of the 258 spec-test-3 scripts | 32,706 commands with the same result and store; 24,722 `:unsupported`; none with another result (24 end at the machine's own fuel) (2026-11-18) | [V4-exits](notes/V4-exits.md) |
| Lockstep | Fast machine against list machine at every step of the benchmarks | 8 runs, 0 disagreements (2026-11-18, after the last change of the fast machine) | [V7-call-ref](notes/V7-call-ref.md) |
| 3 | Fast machine against list machine, final states with memory, per command of the 258 scripts | 32,659 equal, 24,726 `:unsupported` on both in equal states, 0 different; 7 scripts stopped at 900 s (2026-11-18) | [V7-call-ref](notes/V7-call-ref.md) |
| Slides | Engine's framebuffer against V8's on the same module | 7 of 7 slides identical (2026-11-18) | [V8-engine-run](notes/V8-engine-run.md) |
| DVI | The engine's DVI against V8's with TikZJax's own host functions, same `tex.wasm` and `core.dump` | `input.tex` (860 bytes) and the 33-page deck (20,992 bytes) identical, byte for byte (2026-11-18) | [V8-engine-run](notes/V8-engine-run.md) |
| One instance | Both sides of the two theorems of §3.1, evaluated on `fac-1.wasm` at 14 step counts | equal on each (2026-11-18, `engine/inspect.lsp`) | [engine/THEOREM.md](../../engine/THEOREM.md) |

What each one is for, now that tests 1 to 3 and lockstep are theorems:

- **Tests 1, 2, 3 and lockstep** compare the machines with the
  semantics and with each other on concrete runs. Each is now a
  consequence of a theorem for the states it reaches. They stay as
  checks of a change to a machine before its books certify again, and
  they show progress: which commands of the suite the engine finishes.
- **The slides and the DVI** are the comparisons with an independent
  implementation, V8. They also depend on the translation being right,
  which the theorems do not address. The DVI comparison is the only
  evidence for the host functions of TeX.

What the tests and the proofs found in each other:

- Test 3 found that the memory fast paths assumed one memory (E7). The
  refinement lemmas had that as a hypothesis; the machine now checks it.
- The proofs found two bugs no test had reached. A handler whose catch
  clauses are not a true list was entered, where the specification does
  not step (V3: a failed checkpoint that was a state of the machine).
  `throw_ref` under a null reference tested a head no value has, and the
  machine ended `:stuck` where the specification traps (V4: found by
  reading the rule for its lemma). Both are fixed and the tests were run
  again.

## 5. The two demos

### Slides (`engine/slides`)

A renderer compiled to WebAssembly: the integer core only, no host
functions, one memory. **Inside the proved subset.** The driver calls
`engine-run` and reads every pixel from `engine-config`. For each of
its 12 runs it evaluates the hypotheses of T3 (`config-shape-p`, `fmp`,
a result), and all hold. So the pixels are those of the configuration
that `STEPS/%FUEL` returns. Beside the theorem: pixel equality with V8,
7 of 7.

### TeX (`engine/tex`)

`tex.wasm` on the fast machine: 606,866,720 instructions and 63,681 host
calls for the 33-page deck. **Outside the proved subset**: it calls host
functions.

- **Proved**: each stretch of instructions between two host calls. The
  driver calls `fast-run` once per stretch; for a stretch that starts
  with the invariant, the configuration it stops in is the one `STEP`
  reaches in a stated number of steps, and the invariant holds again
  (`fast-stretch-is-spec-steps`). There is no Lisp loop over
  instructions.
- **Checked at run time**: the invariant at the start of every stretch,
  63,712 of 63,712 for the deck.
- **Trusted**: the 18 host functions (raw Lisp, a port of TikZJax's
  `library.js`; they write the memory array and the operand stack and do
  not go through the spec's `$hostcall`); TeX's loader (the memory
  filled from a core dump); the `data.drop` shortcut, taken 40 times in
  the instantiation stretch and never in `main`.
- **Evidence for the trusted parts**: the DVI is identical, byte for
  byte, to the one V8 writes with the original `library.js`, for
  `input.tex` and for the deck. This is not a comparison with a native
  TeX: that `tex.wasm` is TeX is not tested here.
- `f32` instructions are covered like any other: no theorem is limited
  to the integer core.

## 6. Threats to validity

- **The theorem is about the generated semantics.** A translation error
  would be faithfully executed. Evidence there is the spec test suite
  and, for the demos, V8.
- **The theorem does not say the engine finishes.** A change that made
  the engine stop early would keep every book certified. The tests and
  the demos would show it.
- **Hypotheses are evaluated by the driver, not proved of it.** The
  slides driver prints `config-shape-p` for each configuration; a driver
  that did not would run outside the theorem without saying so.
- **For TeX, the claim is per stretch.** The stretches are not composed
  into a statement about the run, and the host step between them is
  trusted. The invariant after a host step is checked, not proved.
- **Trusted throughout**: ACL2 and SBCL (including the execution of a
  stobj in place), the translator and SpecTec, and the drivers' own
  code: reading a file, reading a configuration, writing a PBM.

## 7. What would strengthen it

1. V9 of plan2.md: one book that restates the theorems of §3.1, and a
   gate that fails if a statement drifts or a certificate records a
   skipped proof, an axiom or a trust tag.
2. Host calls inside the theorem (P1 (a)): the host step as a function
   in logic, so that a TeX run is one statement.
3. The other direction (P2, V10): the specification does not step where
   the engine is stuck.
4. A native e-TeX built from the sources of `tex.wasm`, for a DVI
   comparison that does not share the module.
5. A frame lemma for `data.drop` (V7b), which removes the TeX driver's
   shortcut.
6. A statement from the bytes of a module: needs `$instantiate` and the
   decoder in logic mode.
