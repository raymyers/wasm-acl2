# V8: `engine-run` and T3; the drivers call the functions in the theorems

- Milestone: V8 (plan2.md: `engine/run.lisp` and T3, the slides driver calls `engine-run`, the TeX driver calls `fast-run` between host calls, the modes of `$instantiate` and `$invoke`, the DVI comparison)
- Date: 2026-11-18
- Repo commit: 9873ec9 plus this note's commit
- Status: final
- Feeds engine plan: V9 (T3 is the third statement `top.lisp` restates, with the hypothesis `(fmp fm)`, §1; `evidence.md` is rewritten from §3 and §5), V7b (the `data.drop` shortcut is now counted per stretch, §3)
- Incorporated in engine plan: yes (plan2.md V8, §1, "Current state")

## Summary

- **V8 is complete. T3 certifies**, in the new book `engine/run.lisp`
  (2.5 s):

  ```lisp
  (defthm engine-run-is-spec-run                  ; 4,622 prover steps
    (implies (and (config-shape-p c)
                  (fmp fm)
                  (engine-result-p (engine-run n c fm))
                  (natp fuel)
                  (< (engine-clocks n c) fuel))
             (equal (w3t::steps/%fuel fuel c)
                    (list (engine-config (engine-run n c fm))))))
  ```

  It has **one hypothesis more than plan2.md §1 stated**: `(fmp fm)`,
  that `fm` is a stobj of the machine (§1). The invariant `fm-inv` is no
  longer a hypothesis. F4 of plan2.md §1 is met.
- **The slides driver calls `engine-run` and nothing else of the fast
  machine** (§2). 12 runs, the hypotheses of T3 true on each, 7 of 7
  slides identical to V8. The module is inside D5 (S0 only) and its runs
  are inside T3.
- **The TeX driver has no Lisp loop over instructions any more** (§3). A
  run is a sequence of stretches, each one call of `fast-run`; the driver
  makes the host step between two. What a stretch stands for is proved in
  the new book `engine/fast/stretch.lisp` (8.0 s, 26 theorems with §8): for a
  stretch that starts with `fm-inv`, the configuration it stops in is the
  one the specification reaches in a stated number of steps. The driver
  checks `fm-inv` at the start of every stretch: 63,712 of 63,712 for the
  deck. **TeX stays outside the proved subset** (host calls, P1): the host
  step, TeX's own loader and the `data.drop` shortcut have no theorem.
- **The DVI comparison is done against V8, not against a native e-TeX**
  (§5): the same `tex.wasm` and `core.dump` in node with TikZJax's own
  `library.js`. `input.tex`: 860 bytes, identical. The deck: 20,992
  bytes, 33 pages, identical.
- **`$invoke` is in logic mode, `$instantiate` is not** (§4): T3 is
  restated for the configuration `$invoke` builds
  (`engine-invoke-is-spec-run`); there is no statement from a module.
- **No machine changed**: `fast.lisp`, `machine.lisp` and every book
  under them are as they were, so no differential test was run again.
  The gate certifies 36 books (34 before), no `skip-proofs`, no
  `defaxiom`, no trust tag.
- The two deferred items of V8 (the TeX loop as `fast-run` alone with a
  host step in logic; P1 (a)) stay deferred with P1.
- No failed checkpoint was a state of the machine (§6).

## Findings

All prover steps are from the certification output
(`data/v8-engine-run/measure.txt`, every `defthm` of the two books).

### 1. `engine/run.lisp` and the hypothesis `(fmp fm)`

```lisp
(defun engine-run (n c fm)                        ; guard (natp n), guards verified
  (declare (xargs :stobjs fm :guard (natp n)))
  (let ((fm (fm-load-ms (ms-of-config c) fm)))
    (fast-run n fm)))
(defun engine-result-p (fm) (fast-result-p fm))   ; :done, :trap or :throw
(defun engine-config (fm) (machine-abs (fm->ms fm)))
(defun engine-clocks (n c) (machine-clocks n (ms-of-config c)))
```

All four are in logic mode with guards verified and are disabled after
T3. T3 is T2 for the loaded stobj with the loader lemmas of `inv.lisp`
(`fm-inv-of-fm-load-ms`, `fm->ms-of-fm-load-ms`,
`machine-abs-of-ms-of-config`, `fm-loadable-p-of-ms-of-config`): one
`:use`, no other hint.

- **`(fmp fm)`.** `fm-inv-of-fm-load-ms` asks it
  ([V6-inv](V6-inv.md) §5), and nothing in `engine-run` can discharge it:
  in a theorem `fm` is any object, and `fm-load-ms` of a list that is not
  a stobj (say, of length 9) is not one. For the live stobj ACL2
  guarantees it: `fmp` is in the guard of every function that takes
  `fm`. The slides driver also evaluates `(fmp fm)` before each run and
  prints it. The statement of plan2.md §1 is changed to this one. Not
  tried: a version with a local stobj (`with-local-stobj`), which would
  have no stobj argument and so no such hypothesis, but a different
  signature from the plan's and no stobj left for a driver to resume.
- `engine-clocks` is executable (it runs the list machine); the drivers
  do not call it. As in T1 and T2 it only bounds the fuel of the
  specification: for every run some fuel is large enough.
- `engine-result-p` excludes `:stuck`, `:unsupported` and a run that used
  up its fuel `n`: T3 says nothing of those.

### 2. The slides driver

`engine/slides/render.lsp` includes `engine/run` and, on the fast
machine, calls four functions of the engine: `config-shape-p` and `fmp`
(the two hypotheses it can check), `engine-run`, `engine-result-p` and
`engine-config`. Everything it reads afterwards (the store for the next
`$invoke`, the module instance, the result values, the framebuffer
bytes) is read from the configuration `engine-config` returns, which is
the right side of T3. It no longer calls `fm-load-ms`, `fast-run`,
`fm-inv`, `fm->ms` or `fm-status`; the status it prints is computed from
the final configuration.

One line per run: `ENGINE-T3 config-shape <a> fmp <b> result <c>`.
`fm-inv` is not checked any more: for a loaded configuration it is a
theorem.

`make -C engine slides` (`data/v8-engine-run/slides-fast.txt`): 12 runs,
`T T T` on each; 7 of 7 slides identical to V8; 110 to 437 ms per slide.
The caption of the viewer reads "inside the proved subset: theorem T3
(engine-run-is-spec-run) holds for all 12 runs, its hypotheses checked at
run time".

`ENGINE=list` still runs the list machine with the hypotheses of T1
checked (`data/v8-engine-run/slides-list.txt`): 12 runs, the hypotheses
true on each, 7 of 7 identical to V8, 41.2 to 117.8 s per slide.

What is between the theorem and the pixels, and is not the engine's: the
decoder and `$instantiate` and `$invoke` of the specification, run as
they are; the driver's own reading of a configuration (`cadr`, `caddr`,
`%get-field`) and its writing of the PBM file; ACL2 and SBCL.

### 3. TeX: stretches of `fast-run` (V8 item 3)

**What the driver does now** (`engine/tex/texrun.lisp`, `run-engine`):

1. check `(fm-inv-check fm)` and count it;
2. call `(fast-run-fuel chunk fm)`: the fast machine runs until it stops
   or the chunk ends (a chunk ends at the next progress line: 20 or 100
   million steps);
3. if it stopped `:unsupported` with `call_ref` at the head and a
   reference that is `host-ref-p` in the store (the engine's own test,
   which replaces the driver's vector lookup as the test), set the status
   to `:run` and make the host step in Lisp; any other `:unsupported`
   ends the run;
4. repeat while the status is `:run`.

The refused step uses one unit of fuel, which is the step the old loop
counted for the host call: the step counts are comparable with the
earlier ones, and for `input.tex` equal.

**What is proved about a stretch** (`engine/fast/stretch.lisp`).
[V7-call-ref](V7-call-ref.md) §6 left this open: T2 has a result as
hypothesis, and the run lemmas ask "does not end `:unsupported`".

| Section | Statements | Largest proof |
|---|---|---|
| 1. A rule that does not fire, or is refused, leaves the stobj | `fast-apply-fallback-stobj-when-not-fired`, `fast-apply-rule-stobj-when-not-fired`, `fast-try-rules-stobj-when-refused` | 10,406 |
| 2. A step that ends `:unsupported` changes only the status | `fast-op-step-when-refused`, `fast-exit-step-when-refused`, `fast-anyprefix-step-when-refused`, `fast-enter-step-is-not-refused`, `fast-step-when-refused` | 876,167 |
| 3. The steps of a run before the refused one | `fast-supported-steps` (not executable), `fast-run-is-refused-step-after-supported-steps`, `fast-supported-run-is-machine-run`, `fast-run-when-refused` | 33,104 |
| 4. The stretch | `fast-run-resumed`, `machine-run-is-spec-steps`, `fast-stretch-is-spec-steps`, `fast-run-is-spec-steps` | 13,082 |
| 5. `fast-run` with the fuel that is left | `fast-run-fuel`, `fast-run-fuel-is-fast-run`, `fuel-left-of-fast-run-fuel` | 9,375 |
| 6. The invariant without the list state | `fm-inv-check`, `fm-inv-is-fm-inv-check` | 25,659 |

```lisp
(defthm fast-step-when-refused                    ; 876,167
  (implies (and (fmp fm) (ctrl-kinds-ok (fm-ctrl fm))
                (equal (fm-status fm) :run)
                (equal (fm-status (fast-step fm)) :unsupported))
           (equal (fast-step fm) (update-fm-status :unsupported fm))))

(defthm fast-stretch-is-spec-steps                ; 2,674
  (implies (and (fm-inv fm)
                (not (equal (fm-status fm) :unsupported))
                (equal (fm-status (fast-run n fm)) :unsupported))
           (and (fm-inv (update-fm-status :run (fast-run n fm)))
                (equal (stepn (machine-clocks (fast-supported-steps n fm) (fm->ms fm))
                              (machine-abs (fm->ms fm)))
                       (list (machine-abs (fm->ms (update-fm-status :run (fast-run n fm)))))))))

(defthm fast-run-is-spec-steps                    ; 2,797
  (implies (and (fm-inv fm)
                (not (equal (fm-status (fast-run n fm)) :unsupported)))
           (equal (stepn (fast-clocks n fm) (machine-abs (fm->ms fm)))
                  (list (machine-abs (fm->ms (fast-run n fm)))))))
```

- `stepn k c` (`theorem/simulation.lisp`) is exactly `k` steps of
  `W3T::STEP`. So a stretch claims more than T2 in one respect and less
  in another: it holds for a run that did not end with a result, and it
  says "the specification reaches this configuration after so many
  steps", not "`STEPS/%FUEL` returns it" (the configuration at a host
  call is not final).
- `(update-fm-status :run (fast-run n fm))` is what the driver has in the
  stobj before the host step. By `fast-run-resumed` it is the stobj after
  the `fast-supported-steps` steps the run took before the refused one.
- **The refusal lemma is general.** It does not say "a host call": any
  step that ends `:unsupported` (an opcode without rules, a fallback
  result the machine cannot hold, a store write the fast path refuses, a
  host `call_ref`) leaves every field but the status. A rule that is
  refused, or does not fire, returns the stobj it was given (section 1),
  and the fast paths either decline or compute the op step.
- `machine-run-is-spec-steps` is `m-run-simulates` of
  `theorem/simulation.lisp` for the list machine, by functional instance,
  as T1 is `engine-result-is-spec-result`.
- `fm-inv-check` is `fm-inv` without `fm->ms`: `machine-ok` does not read
  the store (`machine-ok-of-ms`, `ok.lisp`), so the 72 MB of memory are
  not copied to test it. `(implies (fmp fm) (equal (fm-inv fm)
  (fm-inv-check fm)))`.
- Hypotheses of the stretch theorems: `fm-inv` at the start, and the two
  facts about the status that the driver sees. None is about an
  instruction.

**What is not proved for a TeX run**, so that it stays outside the
proved subset (plan.md D8, P1):

| Part | State |
|---|---|
| the host step (18 Lisp functions; they write the memory array, the operand stack and the instruction list) | trusted; evidence: §5 |
| `fm-inv` after a host step | checked at every stretch, not proved |
| TeX's loader (`prepare`: host functions put into the store, memory 0 set to 1,100 pages, the array filled from `core.dump`, `fm-set`) | trusted; it is not `engine-run`'s loader. `fm-inv` holds for the state it builds (checked) |
| `data.drop` (40 at instantiation) | the driver's shortcut, assumed (V7b). Counted per stretch since V8: 40 in the instantiation stretch, 0 in `main` |
| the composition of the stretches into one statement about the run | not stated: it needs the host step as a function in logic (P1 (a)) |

**Measured** (2026-11-18, `data/v8-engine-run/tex-*.txt`; every run is
outside the proved subset):

| Run | Steps | Time | Host calls | Stretches, with `fm-inv` at the start |
|---|---|---|---|---|
| instantiation | 7,306 | 0.0 s | 0 | 1, 1 (40 `data.drop` shortcuts) |
| `input.tex`, `main` | 55,065,266 | 17.6 s (3.12 M steps/s) | 3,717 | 3,720, 3,720 |
| the deck, `main` | 606,866,720 | 188.3 s (3.22 M steps/s) | 63,681 | 63,712, 63,712 |
| the deck, `main`, `TEXNOCHECK=1` | 606,866,720 | 188.7 s | 63,681 | 63,712, not checked |
| the deck, from the image, quiet (`acl2-wasm-tex`) | 606,866,720 | 197.5 s; 3 min 29 s wall clock | 63,681 | not printed |

- `input.tex`: the same 860 bytes of DVI and the same 55,065,266 steps as
  with the raw loop (17.4 s then, [V7-call-ref](V7-call-ref.md) §7).
- The risk "the logic-mode run loop is slower than the raw one for TeX"
  (plan2.md §5) did not happen: the raw loop made 606,084,354 steps in
  195.4 s on 2026-11-16 (3.10 M steps/s; `deck.tex` has changed since, so
  the step counts differ). The check of the invariant costs nothing
  measurable (188.3 s with, 188.7 s without).
- The quiet run was made while another process was running; its time is
  not a rate.
- A stretch is cut at a progress line too, so there are more stretches
  than host calls: 63,681 + 30 + 1.

### 4. `$instantiate` and `$invoke` (V8 item 6)

`data/v8-engine-run/modes.txt` (`modes.lsp`):

| Function | Mode |
|---|---|
| `W3T::GRAM/BMODULE` (the decoder) | `:program` |
| `W3T::$INSTANTIATE` | `:program`; it reaches 96 program-mode functions, itself included: `Module_ok` and the relations under it (`Instr_ok`, `Expr_ok`, `Global_ok`, ...), the `$free_*` functions, `$evalexprss` |
| `W3T::$INVOKE` | `:logic` (ideal); it reaches no program-mode function |
| `W3T::STEP`, `W3T::STEPS/%FUEL` | `:logic` (ideal) |

So:

```lisp
(defthm engine-invoke-is-spec-run                 ; 219, T3 with c := ($invoke s a vals)
  (implies (and (config-shape-p (w3t::$invoke s a vals)) (fmp fm)
                (engine-result-p (engine-run n (w3t::$invoke s a vals) fm))
                (natp fuel) (< (engine-clocks n (w3t::$invoke s a vals)) fuel))
           (equal (w3t::steps/%fuel fuel (w3t::$invoke s a vals))
                  (list (engine-config (engine-run n (w3t::$invoke s a vals) fm))))))
```

T3 stated from a decoded module and an export name is **recorded as
outside**: `$instantiate` cannot appear in a theorem. Nothing is lost for
a run: the driver applies T3 to the configuration `$instantiate`
returned, whatever it is. What cannot be said in ACL2 is a statement
about every module.

### 5. The DVI comparison (V8 item 7)

Plan2.md asked for "a native e-TeX of the same revision, byte for byte".
**That was not done; what was done is a comparison with V8**:

- `engine/tex/v8ref.cjs` runs the same `tex.wasm` and `core.dump` in node
  with `library.js` of npm `node-tikzjax` 1.0.5, the JavaScript host
  functions that `texrun.lisp` is a port of. The file is not modified; it
  is fetched by `fetch.sh` with its sha256 and was read before it was run
  (an in-memory file table, no file or network access of its own).
- The harness sets two things from outside, as the driver does: the date
  (2026-01-01, 0 minutes: it is in the DVI preamble) and the font
  metrics as files (a stub stands in for the library's
  `@prinsss/dvi2html`).
- `engine/tex/ref.sh INPUT.tex ENGINE.dvi [DIR ...]` runs it and compares.

| Input | Engine | V8 with `library.js` | |
|---|---|---|---|
| `input.tex` | 860 bytes, sha256 `91c83590acd0...` | 860 bytes, `91c83590acd0...` | identical |
| `deck/deck.tex`, 33 pages | 20,992 bytes, `b95d451fcf68...` | 20,992 bytes, `b95d451fcf68...` | identical |

(`data/v8-engine-run/ref-input.txt`, `ref-deck.txt`.)

- **What it tests**: the 18 host functions of `texrun.lisp` against their
  original, and the engine against another implementation of WebAssembly,
  on 606,866,720 steps of a real program. It is the test for what P1
  leaves trusted.
- **What it does not test**: that `tex.wasm` is TeX. A native e-TeX and a
  LaTeX format built from the sources of this `tex.wasm` (web2js's
  translation of `tex.web` with the e-TeX changes, LaTeX 2020-02-02 in
  `core.dump`) would be needed; a TeX Live `latex` has another LaTeX
  kernel and would not give the same bytes. Not tried.
- Where a file is missing, `library.js` unwinds and rewinds the module
  (asyncify) and the driver answers at once, so the two runs can execute
  different instructions. `input.aux` is the only missing file of the
  `input.tex` run, and the library answers at once for `.aux`.
- Both runs read `engine/tex/deck/deck.aux` (8 bytes, left by an earlier
  run, not checked in).

### 6. What failed on the way

None of these is a state of the machine.

| Attempt | What happened | What was done |
|---|---|---|
| `fast-apply-fallback-stobj-when-not-fired` with every definition the session had open | proved in 535,468 prover steps: `fallback-shape-ok`, `put-z-bytes` and `mem0-of-store` opened | those three disabled (locally): 3,469 |
| `fast-op-step-when-refused` with `fm-set` enabled | more than 2,000,000 steps, no checkpoint | `fm-set` closed (`nth-of-fm-set` of `inv.lisp` gives the status) |
| the same, `fm-set` closed | proved in 1,911,777 steps. `accumulated-persistence`: 927,472 frames in `redex-arity-when-head-not-supported` (`machine/opcodes.lisp`), tried at every `redex-arity`, which opens `member-equal`, `vals-p`, `vn-list-p` | that rule disabled (locally): 40,543 |
| `fast-step-when-refused`, first try | checkpoint `(equal (fast-enter-step fm) (update-nth *fm-status* :unsupported fm))` under `(equal (nth *fm-status* (fast-enter-step fm)) :unsupported)`: the lemma "entering is never refused" was stated with `fm-status`, which is open, so it did not match | restated with `(nth *fm-status* ...)`, the normal form of `inv.lisp` |
| `fast-run-when-refused` with `fm-inv` enabled | checkpoint with `(not (fmp (fast-run (fast-supported-steps n fm) fm)))`: the instance of the run lemma was opened to its parts and no longer matched | `fm-inv` closed; `fmp-when-fm-inv` and `ctrl-kinds-ok-when-fm-inv` as rewrite rules |
| `fast-stretch-is-spec-steps` in one step | checkpoint `(equal (update-nth *fm-status* :run (fast-step (fast-run k fm))) (fast-run k fm))`: `fast-run-is-refused-step-after-supported-steps`, a rewrite rule, had turned `(fast-run n fm)` into the step before the equality with the status update could be used | that lemma has no rule class; the resuming is its own lemma, `fast-run-resumed` |
| a lemma `machine-ok-of-ms` in `stretch.lisp` | redundant: `ok.lisp` has it with the same statement | removed |

The theory block of `stretch.lisp` is `local`, as that of
`call-ref.lisp` is ([V7-call-ref](V7-call-ref.md) §8): it closes one rule
and three definitions of older books for its own proofs only.

Hints: `run.lisp` 1 `:use`; `stretch.lisp` 7 `:use`, 6 `:induct`, no
`"Subgoal"`.

### 7. F4 and F5 after V8

- **F4** (the loader is inside the theorem): met. T3 has the shape of the
  configuration and `(fmp fm)` as its hypotheses about the input.
- **F5** (the code that runs is the function in the theorem): met for the
  slides: the driver calls `engine-run`. For TeX, **met for the
  instructions and not for the run**: every instruction is executed by
  `fast-run`, and the stretch theorems are about `fast-run`; the
  exceptions are the three trusted parts of §3 (the host step, TeX's
  loader, the `data.drop` shortcut in the instantiation stretch). The
  README of `engine/tex` lists them.

### 8. Added the same day: "follows the specification or stops" as one theorem

Asked by the user after the commit of V8: has it been shown that the
fast engine matches the semantics or stops? The parts were there (§3)
but not composed for `engine-run`. Now, in `run.lisp`:

```lisp
(defthm engine-run-is-spec-steps                  ; 2,259 prover steps
  (implies (and (config-shape-p c) (fmp fm))
           (equal (stepn (engine-steps n c fm) c)
                  (list (engine-config (engine-run n c fm))))))
```

- No hypothesis about how the run ends. `engine-steps` (not executable)
  is `machine-clocks` over `fast-run-steps`: the `n` steps, or, for a run
  that ends `:unsupported`, the steps before the refused one.
- From `fast-run-is-spec-steps-or-refused` (`stretch.lisp`, 15,172), the
  two stretch theorems as one, with
  `machine-abs-of-fm->ms-of-update-fm-status` (15): the abstraction does
  not read the status, so the refused step is not seen in the
  configuration. `run.lisp` now includes `fast/stretch`.
- **It does not say the engine makes progress** (0 steps satisfy it),
  and it is one direction: where the engine stops without a result the
  specification may step on (P2).
- `engine/THEOREM.md` is a guide for a reader who wants to inspect the
  two theorems; `engine/inspect.lsp` is its script: the statements
  printed from the logical world, 67 books under `run` with none flagged
  for a skipped proof, an axiom or a trust tag, and both sides of both
  theorems evaluated on `fac-1.wasm`, `run(5)`, at 14 values of `n`
  (`data/v8-engine-run/inspect.txt`: `same T` on every line; 89 engine
  steps are 46 spec steps; the result is 120 after 60).
- The gate still certifies 36 books; the slides were run again, 7 of 7.

## Open questions

- V9 restates T3 "verbatim": the statement is the one of §1, with
  `(fmp fm)`. If a statement without it is wanted, `engine-run` needs a
  local stobj (§1).
- `fm-inv` after a host step is checked, not proved. A proof needs the
  host step in logic (P1 (a)); what it would have to show is small:
  values on the operand stack, a true list of instructions, the store
  untouched.
- The `data.drop` shortcut is the one place where the code of a stretch
  is not the engine's (V7b).
- No comparison with a native TeX (§5).

## Data

`engine/run.lisp` (new), `engine/fast/stretch.lisp` (new),
`engine/Makefile` (`run` among the books), `engine/slides/render.lsp`,
`engine/slides/check.mjs`, `engine/slides/run.sh`,
`engine/tex/texrun.lisp`, `engine/tex/run.sh`, `engine/tex/fetch.sh`,
`engine/tex/v8ref.cjs` (new), `engine/tex/ref.sh` (new),
`engine/tex/README.md`; `data/v8-engine-run/`: `measure.sh`,
`measure.txt` (prover steps of every theorem, times, hints,
certificates), `gate.txt` (`make -C engine check`, 36 books),
`modes.lsp`, `modes.txt`, `slides-fast.txt`, `slides-list.txt`,
`tex-input.txt`, `tex-deck.txt`, `tex-deck-nocheck.txt`,
`tex-deck-quiet.txt`, `ref-input.txt`, `ref-deck.txt`, `inspect.txt`;
`engine/THEOREM.md`, `engine/inspect.lsp` (§8).
