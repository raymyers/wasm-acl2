# A verified WebAssembly 3.0 engine

> **Goal**: an engine written in ACL2 that runs WebAssembly 3.0 modules
> much faster than the generated semantics, with a theorem, checked by
> ACL2, that it computes what the generated semantics computes. The
> generated books (`translate/gen/wasm-3.0`) stay the specification. The
> engine is a second, faster definition, and the theorem connects the two.
>
> **Target workload**: MuPDF (the PDF renderer of the `mupdf` npm package),
> rebuilt with 3.0 exception handling, rendering the pages of a slide deck
> outside the browser: ACL2 on SBCL computes the pixels and a viewer on the
> same machine shows them.
>
> **Litmus test (set by the user, 2026-11-15)**: the plan has worked when
> both of these hold for the same engine and the same MuPDF module:
> 1. **View**: a page of a PDF, rendered by the engine and shown outside
>    the browser, with pixels identical to V8's render (E9, E10).
> 2. **Certify**: the engine's books certify with the theorem against the
>    generated 3.0 semantics, with no `skip-proofs` and no `defaxiom`, for
>    every instruction that module uses (E11, all groups).
>
> View alone is a demo of a tested engine. The plan is done only with
> both. §4 "Litmus milestones" says which items each half needs.
>
> **What the theorem says, and what it does not**: it relates the engine to
> the generated ACL2 semantics, for the instructions in the proved subset
> and for any host functions. It says nothing about the translator
> (`il2acl2`), SpecTec, the loader, or what the host functions do. Those
> stay trusted or tested.
>
> **Non-interference**: the engine lives in `engine/`. Nothing under
> `translate/` changes except through the translator (`il2acl2/`, `rt/`,
> config), and only for an item this plan marks as approved by the user.
> Generated code is never edited by hand. Everything that certified or
> passed before must still certify and pass.
>
> **Status: in execution. E0, E2 (go), E3, E5, E6 and E4 items 1 and 2
> complete; E1 (item 5) and E11 (S0) in progress** (written 2026-11-15, at `d845f70`; revised the same day for
> 3.0 and MuPDF). Per-session procedure: [step.md](step.md). Prompts behind
> this plan: [seed.md](seed.md).

---

## Current state

- **Last updated**: 2026-11-15
- **Milestones complete**: E2 (**go**: `STEP`, `STEP_READ`, `STEPS/%FUEL`
  are `:logic`; [E2-step-logic](notes/E2-step-logic.md)), E5 (machine
  design; [E5-machine](notes/E5-machine.md)) and E0 (baseline: 23,000 to
  40,000 spec steps/s on flat code; [E0-baseline](notes/E0-baseline.md))
- **Also complete**: E6 (the list machine; C1 and C3 proved; test 1: 0
  disagreements; test 2: 14,303 S0 commands, none differs;
  [E6-list-machine](notes/E6-list-machine.md)). E3 (the theorem for any machine, its run level, and
  the spec facts behind C3; [E3-theorem](notes/E3-theorem.md)). For the
  list machine, C1 and C3 are proved; C2 is E11
- **In progress**: E1, every item but 5 done (census, reference renders,
  imports, build script that reproduces the module bit for bit, small
  target; [E1-mupdf-target](notes/E1-mupdf-target.md)). Item 5: the small
  target passes the generated decoder and `Module_ok` (73 min and 85 s);
  the full module's parse was still running after more than 100 CPU
  minutes. E11 (S0) started: C2 for every clock-0 step is proved
  (`engine/machine/clock0.lisp`); for the clock-1 steps the first test
  shows that an `append`/`take`/`nthcdr` library comes first. E4 items 1
  and 2 done
- **`engine/` exists**: `make -C engine check` is a gate from now on. It
  needs `translate/gen/wasm-3.0` certified (`make -C translate check-3.0`)
- **Who did what (user's instruction, 2026-11-15)**: the session of
  2026-11-15 did the items where a wrong early choice costs most (E2, the
  E5 design, the E3 statement, D4 (a)). The remaining items follow written
  designs and are for later sessions
- **Litmus test set by the user (2026-11-15)**: view a PDF with the engine,
  and the engine certifies against the semantics (top of this file, and
  §4 "Litmus milestones")
- **Decided by the user (2026-11-15)**: D1, the engine is for 3.0. The
  target is MuPDF, forked and rebuilt with 3.0 exceptions. The display is
  outside the browser
- **Decided by the user (2026-11-15)**: D2 checked engine; D4 (a), the
  translator may emit one function per rule; E2 approved (a headless
  session may change `translate/` to admit the 3.0 step group in
  `:logic`); E5 runs headless and the user reviews the note later; the
  fork lives at `raymyers/mupdf`
- **Waiting for the user**: nothing. Two points of the E5 design touch
  what is trusted and are listed for review in the note ("For the user to
  review"): the fast host layer enters under a trust tag in the view
  driver, and the first theorem is one direction (a machine that is stuck
  claims nothing). Neither blocks a session
- **Spec runs with large memories**: the generated `$ALLOCMEM/ITER2`
  recurses once per byte; SBCL's default stack ends near 32 pages. Run
  with `SBCL_USER_ARGS='--control-stack-size 1000'` (64 pages) or `4000`
  (MuPDF's 352 pages) ([E0-baseline](notes/E0-baseline.md))
- **Next action**: record the full module's decode when it ends (E1
  item 5); then E7 (the stobj machine: the memory rules need array fast
  paths, see "What this means for E7" in
  [E6-list-machine](notes/E6-list-machine.md)), and on the proof track
  the list library and dispatch lemmas for C2's clock-1 steps (E4 item 4,
  E11 S0) (the list machine of
  [E5-machine](notes/E5-machine.md), S0 first, written over primitives so
  that E7 can put a stobj under it), then E4 items 1, 3 and 4
- **Changed by E2, for every later session**: a relation function is now
  a chain of calls of rule functions `FN/R-<RULE-ID>`
  (`STEP_PURE/R-IF-TRUE`, `STEP/R-CTXT-LABEL`), in all three spec
  versions. `gen/wasm-1.0` and both mode manifests were regenerated
- **Theorem hypotheses so far** (step.md asks for them here):
  `(m-ok s)`, `(m-result-p (m-run n s))`, `(natp fuel)`,
  `(< (m-clocks n s) fuel)`; reasons in [E3-theorem](notes/E3-theorem.md).
  The spec lemma `step-of-uncaught-exception` has the hypothesis that the
  exception reference is a `VAL-P`; for the machine `machine-ok` gives it,
  so the machine theorem C3 has no extra hypothesis
- **Machine design refinement (E6, 2026-11-15)**: the machine applies the
  spec's rule functions to the redex instead of restating each row of the
  E5 table. Same states, same clock, same `abs`; E7 makes the rules that
  touch memory fast with `mbe`. Recorded in
  [E6-list-machine](notes/E6-list-machine.md)

---

## 1. Decisions

All decisions below are settled. A new one that only the user can make
is added here marked *(for the user)* and listed in "Current state".

- **D1 (decided by the user, 2026-11-15): the engine and its theorem are
  for 3.0.** MuPDF needs exceptions, bulk memory and sign extension, none
  of which is in 1.0. The 1.0 books are used only as a proof rehearsal if
  E2 is no-go.
- **D2 (decided by the user, 2026-11-15): a checked engine.** A checked engine keeps the dynamic checks the spec
  rules make (operand tags, bounds). It gets stuck exactly where the spec
  gets stuck, so the theorem needs no typing hypothesis. An unchecked
  engine is faster but its theorem needs `Module_ok` as a hypothesis and a
  preservation proof. `MODULE_OK` and `INSTR_OK` are in `:program`, so
  that hypothesis cannot be stated today. Unchecked is deferred.
- **D3: two layers.** A machine over lists is proved against the spec. A
  stobj machine is proved against the list machine. The hard proof never
  sees a stobj, and the fast code never sees the spec. *E5 (2026-11-15)*:
  the two layers are one step function over an abstract stobj
  (`defabsstobj`); the list state is its logical side and the proof
  against it is the correspondence of the primitives.
- **D4 (decided by the user, 2026-11-15): option (a), the translator
  emits one function per rule.**
  Today each rule is one clause inside a large `DEFUN` (`STEP_PURE` is a
  chain of `(LET ((%R clause)) (IF %R %R ...))`). A lemma about one rule
  has to dig its clause out of that body. Options:
  - **(a)** *(chosen)* the translator emits each rule as its own function
    (`STEP_PURE/R-<rule-id>`) and the relation calls them in order. Lemmas
    attach to small functions. Generated output changes for every version,
    under the same conditions as W7 of the demo plan: the three gates, the
    mode manifests, `check-gen` determinism and identical per-command spec
    results. The demo extractor (`demo/extract`) must still pass its check.
  - **(b)** *(not chosen)* no translator change. `engine/` holds a tool that copies each
    clause out of the certified book into a local function and proves it
    equal to its place in the relation. More proof work per rule, and the
    copies must be regenerated when the translator changes.
- **D5: the subset is what MuPDF uses, reached in groups.** The census of
  the rebuilt module (E1 item 4) is the definition. Expected groups, from
  the census of the published binary:
  - **S0** integer core: `const`, integer numeric ops, `drop`, `select`,
    `nop`, `unreachable`, `local.*`, `global.*`, `block`, `loop`, `if`,
    `br`, `br_if`, `br_table`, `return`, `call`, integer `load`/`store`,
    `memory.size`, `memory.grow`
  - **S1** floats, the table, `call_indirect`
  - **S2** `memory.copy`, `memory.fill`, sign-extension ops
  - **S3** exceptions: `try_table`, `throw`, `throw_ref`
  - **H** calls of host functions

  On any other instruction the engine stops with `:unsupported`.
- **D6: numerics and type checks are shared.** The engine calls the same
  `$binop_`, `$unop_`, ... functions as the generated rules (`rt/`), and
  the same subtype check where a rule makes one (`call_indirect`). No
  arithmetic is re-implemented, so none needs a proof.
- **D7: test before proving.** A differential run against the generated
  semantics comes before each proof. A proof attempt on a machine with a
  bug is wasted time.
- **D8: running comes before proving, and the two are reported apart.**
  The machine is built and tested for all of D5 first (E6 to E9), so that
  MuPDF renders. The proof then covers one group at a time (E11). Every
  run reports whether the module is inside the proved subset. A page is
  "rendered by the verified engine" only when it is.
- **D9: the spec's memory stays a list.** A store in the generated
  semantics rebuilds the byte list (`APPEND` of `TAKE` and `NTHCDR` in
  `$WITH_MEM`), and a list cannot be updated faster. The fix is the
  engine's stobj memory with its refinement theorem (E7), not a change of
  the specification's representation. Consequence: MuPDF never runs on the
  generated semantics; the two are compared on small programs only.

---

## 2. Starting point (2026-11-15)

| Fact | Value | Source |
|---|---|---|
| Cost of one 3.0 step, counting loop | 0.011 ms, with or without memory | [M3-execution](../wasm3-translation/notes/M3-execution.md) |
| The same with `i32.store` + `i32.load` per iteration | 0.029 ms at 1 page, 0.059 ms at 4 pages | same |
| 3.0 defun-modes, before E2 | `:guards` 429, `:logic` 692, `:program` 288 | [M9-logic-mode](../wasm3-translation/notes/M9-logic-mode.md) |
| 3.0 defun-modes, after E2 | `:guards` 607, `:logic` 1,402, `:program` 132 (2,141 functions; 732 are the new rule functions) | [E2-step-logic](notes/E2-step-logic.md) |
| 3.0 step group, before E2 | `STEP_PURE` `:logic`; `STEP_READ`, `STEP`, `STEPS` `:program` | manifest at `78d1584` |
| 3.0 step group, after E2 | `STEP_PURE`, `STEP_READ`, `STEP`, `STEPS/%FUEL`, `STEPS`, `EVAL_EXPR` `:logic` | `translate/tests/sem-3.0/modes-3.0.lsp` |
| Why it was `:program` | no measure for the type substitution group, no common measure for the fuel group, `$concatn_`; then the size of the `REF_OK` termination proof with the rules inline (55.88 s, 37,894,051 prover steps) | [E2-step-logic](notes/E2-step-logic.md) |
| 3.0 typing | `INSTR_OK`, `MODULE_OK` `:program` (unchanged by E2) | manifest |
| 1.0 step group | all four step functions `:logic` | `translate/gen/wasm-1.0/modes.lsp` |
| 3.0 reduction rules | 218 | [M3-execution](../wasm3-translation/notes/M3-execution.md) |
| 3.0 exceptions in the spec tests | `assert_exception` 18 of 18 | [M4-conformance](../wasm3-translation/notes/M4-conformance.md) |
| Host calls in the spec | `$hostcall` goes through `%hostcall-hook`, a constrained function with an attachment | `translate/rt/builtins-3.0.lisp` |
| One rule proved equal to a hand-written form | `Step_pure/if-true`: a 7-line `case-match` function, two lemmas about `len` | `talk/figures/snippets/if-true.handwritten-proof.lisp` (not checked in; E4 item 1 moves it) |
| `mupdf` 1.28.6 binary (npm) | 10.4 MB; 7,410 functions; 22 imports; memory 352 pages initial; 2,492 `try`, 1,290 `delegate`, 1,202 `catch` (legacy encoding); 710 `memory.copy`, 662 `memory.fill`; 3,267 `call_indirect`; no SIMD, no GC | `wasm-objdump`, [E1-mupdf-target](notes/E1-mupdf-target.md) |
| The 3.0 parser and legacy exceptions | `:TRY_TABLE`, `:THROW`, `:THROW_REF` present; `:DELEGATE`, `:RETHROW` absent | `translate/gen/wasm-3.0/5_3-binary_instructions.lisp` |
| Where MuPDF sets its exception mode | `platform/wasm/tools/build.sh`: `-fwasm-exceptions -sSUPPORT_LONGJMP=wasm`, Emscripten 4.0.8 | MuPDF 1.28.6 source |

Why the generated semantics is slow, as read from the generated code (E0
measures the shares):

- A configuration is a term `(:|%;%| state instrs)`. A step under a label
  or frame recurs through `Step/ctxt-*` rules and rebuilds the term.
- A relation tries its rule clauses in order. Nothing dispatches on the
  instruction.
- Memory is a list of bytes. A store rebuilds it (D9).

Measured by E0 ([E0-baseline](notes/E0-baseline.md)): on flat code the
rules that are tried and fail cost most, by allocation (about 9 KB a
step). Context recursion costs little by itself, but the termination
check before each recursive premise makes a step at depth d cost d². Every
load and store walks the whole byte list, in the out-of-bounds rules,
which come first.

Prior art to read in E5: x86isa (logic and executable definitions of one
machine in ACL2), WasmRef-Isabelle (a fast interpreter proved against the
WasmCert-Isabelle semantics).

---

## 3. Architecture

```
translate/gen/wasm-3.0/      the specification (generated, certified)
        |   rule lemmas (E4): each rule in a clean form, proved equal
        v
engine/rules/                one small function + one theorem per rule
        |   simulation (E11): each machine step is one or more spec steps
        v
engine/theorem/              the theorem for any machine (E3), proved at run level
engine/machine/              list machine (D3): operand stack, control stack,
        |                    continuations as pointers into the instruction tree (E5)
        |   refinement (E7): the same step function over an abstract stobj
        v
engine/fast/                 the concrete stobj and its correspondence: what runs
        |   host functions (E9), outside the theorem
        v
engine/host/ , engine/view/  MuPDF's 22 imports; pixels to a viewer (E10)
```

- **Abstraction function** `abs`: machine state to spec configuration. It
  rebuilds the nested `LABEL_`/`FRAME_`/`HANDLER_` term from the control
  stack and turns the memory array back into a byte list. It is only
  reasoned about. It never runs on the fast path.
- **Theorem shape** (fixed by E3, `engine/theorem/simulation.lisp`): for
  a machine state `s` with `(m-ok s)` that is running,
  `(stepn (m-clock s) (m-abs s))` equals `(list (m-abs (m-step s)))`:
  one machine step is exactly `(m-clock s)` spec steps. The clock can be
  0 (the machine moved a value to its operand stack and `abs` is
  unchanged). The run-level theorem `ENGINE-RESULT-IS-SPEC-RESULT` is
  proved from this for any machine; E11 instantiates it.
- **Host functions**: the spec side already calls a constrained function
  (`%hostcall-hook`). The engine calls the same one, so the theorem holds
  for every host. What MuPDF's imports actually do is engine/host code
  under an attachment, tested and not proved.
- **Stuck and trap**: with D2 checked, the machine reports `:stuck` when
  no spec rule applies and `:trap` when the spec steps to `TRAP`. The
  theorem covers `:done` and `:trap`. `:stuck` and `:unsupported` carry no
  claim in the first version (E3).
- **Package** `WE` (`engine/package.lsp`). Spec functions are written
  with their package prefix (`w3t::step`).
- **Gate**: `make -C engine check` certifies every engine book and runs
  the differential tests. It joins the existing gates.

---

## 4. Milestones

### E0: Baseline and profile

- [x] Benchmark set in `engine/bench/`: the M3 counting loop, a loop with
      a store and a load, nested blocks 8 deep, a recursive call chain, a
      `try_table` that catches a `throw`, the factorial of the demo. Each
      as WAT and as a configuration, run on the generated 3.0 semantics
      (through the generated decoder, `$instantiate` and `$invoke`;
      results checked, 2026-11-15)
- [x] Steps per second for each, with memory at 1, 16 and 64 pages: flat
      code 23,000 to 40,000, independent of memory; the memory loop
      20,652 / 4,366 / 1,261 (each load and store walks the byte list);
      the call chain 5,036 at depth 10, 80 at depth 100 (a step costs d²).
      64 pages need a 1,000 MB control stack (`$ALLOCMEM/ITER2` recurses
      once per byte) (2026-11-15)
- [x] Profile of the counting loop and the nested-block loop (and the
      memory loop and the call chain): rule matching by allocation (about
      9 KB a step, 45% to 59% of the time, with 30% to 37% more in the
      relation functions), the termination check (15% nested, 69% at call
      depth 50), the store (51% in the out-of-bounds load and store rules
      at 16 pages), contexts' own time 0.5% to 2.3% (2026-11-15)
- [x] Record what `STEP` returns: `NIL` or a list of exactly one
      configuration; a trap is `((:TRAP))`, an uncaught exception
      `((:REF.EXN_ADDR a) (:THROW_REF))`, and neither steps (2026-11-15)

**Exit**: a table of measured rates and a ranked list of costs, in
`notes/E0-baseline.md` (met: [E0-baseline](notes/E0-baseline.md)).

### E1: MuPDF as a 3.0 module

- [x] Fork MuPDF on GitHub: `raymyers/mupdf`, fork of
      `ArtifexSoftware/mupdf` (2026-11-15)
- [x] Branch with 3.0 exception handling: `wasm3-exceptions` at `3eae43d`
      adds `-sWASM_LEGACY_EXCEPTIONS=0` to the compile and link flags.
      Built with Emscripten 4.0.8: 2,492 `try_table`, 1,201 `throw_ref`,
      no `try`, `catch` or `delegate`
      ([E1-mupdf-target](notes/E1-mupdf-target.md), 2026-11-15)
- [x] The rebuilt module still works: one test PDF renders in node to
      the same 1,454,112 RGB samples (sha256 equal) as the published
      `mupdf` 1.28.6, and two MuPDF errors are caught the same way
      (2026-11-15; one PDF only, item 6 adds more)
- [x] Census of the rebuilt module: every opcode with its count
      (`notes/data/e1-mupdf/fork-3eae43d-opcodes.txt`), the imports with
      their signatures, memory and table sizes
      (`fork-3eae43d-census.txt`). This fixes D5: 165 instructions, S0 97,
      S1 59, S2 6, S3 3, none outside; `memory.grow` and `nop` do not
      occur (memory grows through the import `emscripten_resize_heap`)
      (2026-11-15)
- [ ] The module through the generated 3.0 decoder and `Module_ok`:
      result and time, or the reason it does not finish
- [x] Reference renders from node (V8): three PDFs, one of them a slide,
      as raw pixel files with checksums. These are what E9 compares with.
      `test1.pdf`, `slide.pdf` (960 x 540), `text.pdf`; `ref-render.mjs`
      writes the PPM files and prints the sha256 of the samples
      (`ref-render.out`); the files themselves are regenerated, not
      checked in (2026-11-15)
- [x] What each of the 22 imports must do for "open a PDF from memory,
      render page n to a pixmap", read from the Emscripten glue and traced
      in node: six are called (environment, time zone, `date_now`,
      `gmtime`, and the font loader through `asm_const_ptr`, which returns
      0); the export call sequence is in `exports-called.txt` (2026-11-15)
- [x] The build as a script in `engine/mupdf/` that takes the fork commit
      and produces the module with a recorded checksum, run from Nix
      (Emscripten 4.0.8, the version MuPDF tests with):
      `engine/mupdf/build.sh` reproduces the hand build bit for bit
      (sha256 `e3c67c2e...af14`) (2026-11-15)
- [x] A smaller build if the census allows it (features off, fonts out),
      recorded as a second target: `engine/mupdf/build-small.sh`, 4.5 MB,
      4,470 functions, 288 pages, sha256 `97239ccb...1f97`; same pixels as
      the full build except CMYK (no ICC) (2026-11-15)

**Exit**: a 3.0 module of MuPDF with no legacy exception opcode, proved to
render the same pixels as the published one in V8, with its census.

### E2: The 3.0 step group in logic mode (go/no-go)

- [x] From the M9 logs: for `STEP`, `STEP_READ`, `STEPS` and each function
      they call that is `:program`, the attempt that failed and why. The
      logs do not keep failed attempts, so the causes were found by probes
      on the certified books: three roots (type substitution, the fuel
      group, `$concatn_`) (2026-11-15)
- [x] The call graph from `STEP` down to `:program` functions: 76
      functions; D5 reaches the first two roots (`block` and
      `call_indirect`), and `STEP_READ` as one function needs the third
      (2026-11-15)
- [x] Admit them in `:logic`: a ranked size measure for type substitution
      (config `:size-rank`), one lexicographic measure for every fuel
      group, a lemma and a measure for `$concatn_` (config
      `:termination`). `REF_OK` then still failed by proof size, which
      one function per rule (D4 (a)) removed (2026-11-15)
- [x] Gates, mode manifest updated, spec results identical per command:
      the three translate gates pass; no function's mode got worse in
      the 1.0 or 3.0 manifest; spec-test-3 and spec-test-1 give the same
      result for every command that ran in both runs (64,778 and
      11,992) (2026-11-15)

Result and evidence: [E2-step-logic](notes/E2-step-logic.md).

**Exit (go)**: `STEP`, `STEP_READ` and `STEPS/%FUEL` are `:logic` in the
manifest. **No-go**: recorded with the evidence; then the proof milestones
(E3, E4, E11) run on the 1.0 books as a rehearsal, the 3.0 engine is
covered by differential tests only, and the user decides how to go on.
This item changes `translate/` (config and possibly the translator).
Approved by the user on 2026-11-15, under the usual conditions: the
gates, `check-gen` determinism, identical per-command spec results. The
mode manifest changes and is committed with the reason.

### E3: Theorem statement and spec-side lemmas

- [x] Write the top-level theorem as an ACL2 form over `STEP` and
      `STEPS/%FUEL` and certify the book that states it:
      `engine/theorem/simulation.lisp`. The machine is six constrained
      functions with four constraints (C1 to C4), and the run-level
      theorem is proved from them, so no `skip-proofs` is used
      (certified in 2.2 s, 2026-11-15)
- [x] Prove the facts about the spec that the simulation needs and that
      do not depend on the machine: a value sequence does not step, and
      `TRAP` alone does not step (constraint C3). "At most one result" is
      no longer needed. Done, with the uncaught exception as the third
      case: `engine/rules/terminal.lisp` (130 s, one generated lemma per
      rule function and per search function), and C3 for the list machine,
      `machine-result-is-terminal` in `engine/machine/terminal-ok.lisp`
      (2.5 s) ([E3-theorem](notes/E3-theorem.md), 2026-11-15)
- [x] Decide and record the fuel relation: `(< (m-clocks n s) fuel)`,
      where `m-clocks` sums the clock over the run (2026-11-15)

**Exit**: the statement certifies (met, with no `skip-proofs` at all) and
item 2 is proved (met, 2026-11-15). [E3-theorem](notes/E3-theorem.md) holds the statement
and the reason for each hypothesis.

### E4: Rule lemmas (needs D4)

- [x] Move the `if-true` proof into `engine/rules/` as the first test.
      `engine/rules/first-lemmas.lisp` has the clean form and the
      dispatch lemma of `if-true`, written against the rule function
      `STEP_PURE/R-IF-TRUE`, and a whole `STEP` under a label for any
      state ([E4-first-lemmas](notes/E4-first-lemmas.md)).
      `engine/rules/if-true.lisp` has the hand-written `case-match` form
      of the talk snippet, proved equal to the generated rule function
      itself (2.5 s) (2026-11-15)
- [x] D4 (a): translator emits one function per rule
      (`FN/R-<RULE-ID>`), for every relation and spec version; gates as in
      D4. Done with E2, which needed it
      ([E2-step-logic](notes/E2-step-logic.md), 2026-11-15)
- [ ] Generator for the clean form of a rule: a `case-match` function and
      the theorem that it equals the rule function. S0 rules first, then
      S1, S2, S3
- [ ] Dispatch lemma per relation: for an instruction list whose head has
      opcode `k`, only the rules for `k` can fire
- [ ] Optional: `STEP-INDEXED`, the relation entered through a `case` on
      the head opcode, proved equal to `STEP`; its rate on the E0 set

**Exit**: every D5 rule has a certified clean-form theorem, and each
relation has its dispatch lemma. Rules covered and certification time
recorded.

### E5: Machine design

- [x] Read the prior art (§2) and record what carries over. Recorded
      from memory of the two papers, without a fetch; the note says so
      (2026-11-15)
- [x] Design note: a context-stack machine that keeps the spec's data and
      mirrors its intermediate forms, so that a machine step is 0 or 1
      spec steps (bulk memory excepted). No flat bytecode: a continuation
      is a pointer into the instruction tree (2026-11-15)
- [x] Hand simulation of four programs in the note (2026-11-15). They
      were not run; E6's differential test 1 checks them

**Exit**: `notes/E5-machine.md` written, with the chosen design, the
alternatives rejected and why. Headless (decided by the user,
2026-11-15): the session takes its recommended design and goes on. The
user reviews the note when they choose; a change they ask for becomes a
new item.

### E6: List machine

- [x] `engine/machine/`: state as lists, `machine-step`, `machine-run`
      with fuel, loader from a decoded module, in `:logic` with guards
      verified. S0 first. Follow the step table of
      [E5-machine](notes/E5-machine.md). Write the step function over a
      small set of primitives (push, pop, local, memory, control entry),
      not over the state's list structure, so that E7 changes only the
      primitives. Done as `machine.lisp` (3.7 s): the machine picks the
      redex by the head instruction and applies the spec's own rule
      functions to it, in `STEP`'s order (a table of 212 rules made by
      `make-event` from the relation bodies); spec functions through
      `ec-call`. The loader takes the configuration of the spec's
      `$instantiate`/`$invoke` (2026-11-15)
- [x] Constraint C1 of E3 for this machine: a step keeps `machine-ok`
      (`ok.lisp`, `machine-step-preserves-ok`, 19 s) (2026-11-15)
- [x] `abs` as an executable function (`machine-abs`, guard-verified)
- [x] Differential test 1: at every step of every E0 benchmark,
      `(abs (machine-step s))` equals the spec stepped `(clock s)` times:
      0 disagreements in 10 runs (10,050 machine steps), including a trap
      and an uncaught exception (2026-11-15)
- [x] Differential test 2: the spec test scripts whose modules are inside
      the machine's subset, per-command results compared with the
      generated semantics. Run on all 258 scripts: 33,113 commands agree
      (14,303 in S0, 17,991 in S1, 176 in S2, 66 in S3), 24,773 stop at
      instructions outside D5, none differs in S0. Two S1 lines reported
      different were printed after the time limit signalled the session
      (re-runs of commands that had agreed); every replay agrees
      (2026-11-16)

**Exit**: both differential tests pass with zero disagreements for S0.
Scripts and commands inside S0 recorded
([E6-list-machine](notes/E6-list-machine.md)). Met (2026-11-16).

### E7: Stobj machine

- [ ] `engine/fast/`: a concrete stobj (operand stack and locals in one
      array, control stack, memory as a byte array) and a `defabsstobj`
      whose logical side is the E6 state. The step function is E6's.
      Design consequence of E6 recorded in
      [E6-list-machine](notes/E6-list-machine.md) ("What this means for
      E7"): memory in an array, fast paths for about 12 memory rules,
      and a generated frame lemma for every other rule; the frame lemma
      for `local.get` and `local.set` was tried and proves with four
      record lemmas (2026-11-16). `engine/fast/frame.lisp`: the frame
      lemma for 81 of the 98 rules that are neither pure nor memory
      rules (184 s); the 17 left include `global.set` (S0), `throw` (S3)
      and the host calls (H)
- [ ] Refinement: the correspondence obligations of the `defabsstobj`
      primitives. `mbe` fast paths for the spec's numeric functions where
      the profile asks for them
- [ ] Rate on the E0 benchmarks at 1, 16, 64 and 352 pages

**Exit**: the refinement theorem certifies for S0. Rates recorded next to
E0's. **Go/no-go for the target**: from the measured rate and the E1
instruction counts, the time to render one page. If it is over an hour,
the user decides (smaller build of E1, a faster machine design, or stop).

### E8: Widen the machine to D5

- [ ] S1, S2, S3, one group per item, in both machines, each with
      differential tests 1 and 2 extended, and the stobj refinement
      theorem extended

**Exit**: every opcode of the E1 census is supported. The spec test
scripts inside D5 agree with the generated semantics per command.

### E9: Host layer and the first page

- [ ] `engine/host/`: the imports E1 lists, as an attachment of the host
      hook. Each with its reason and what it does
- [ ] Driver: load the module, put a PDF in memory, call the exports that
      open it and render page n, copy the pixmap out
- [ ] The three E1 PDFs: pixels equal to the V8 reference renders

**Exit**: one page rendered by the engine with pixels identical to V8's.
Time and step count recorded.

### E10: Display outside the browser

- [ ] The driver writes each page as an image file (PPM or PNG) from ACL2
- [ ] A viewer for presenting: pages pre-rendered to a folder and shown
      full screen, with a caption that names the engine and whether the
      module is inside the proved subset (D8)
- [ ] Optional, live: frames from the running SBCL image to a window or
      a local socket. This needs a trust tag; it is recorded and kept out
      of every certified engine book

**Exit**: the slide deck of the talk, rendered by the engine, shown from
the folder.

### E11: Simulation proofs

- [ ] S0: one simulation lemma per instruction from the E4 clean forms;
      (Started: C2 for every clock-0 step of the list machine, i.e. value
      pushes, entries into `LABEL_`/`HANDLER_`/`FRAME_` and stops, is
      proved for all groups: `engine/machine/clock0.lisp`,
      `machine-clock-0-simulates`, 4.2 s, 2026-11-16. What is left of C2
      is the clock-1 steps: a rule function on a subterm of `abs`, lifted
      through the contexts.)
      the operand-prefix and `ctxt-instrs` lemmas; the context lemma (a
      step inside the innermost label or frame of `(abs s)` is a `STEP`
      of the whole configuration), by induction on the control stack;
      then constraint C2 of E3 for the machine, and the theorem by
      functional instantiation of `ENGINE-RESULT-IS-SPEC-RESULT`
- [ ] S1, S2, S3 and H in turn. S3 adds the handler form to the context
      lemma

**Exit**: per group, the instantiated theorem certifies with no
`skip-proofs` and no `defaxiom`, with that group's instructions outside
the machine's `:unsupported` case (E3: this is how a subset is
expressed). When all groups are done, MuPDF is inside the proved subset.

### Litmus milestones

| | Needs | Checked by |
|---|---|---|
| **L1 View** | E1, E5 to E10 | `make -C engine view-check`: renders the three E1 PDFs on the stobj machine, compares each pixel file with the V8 reference checksum, and writes the image files the viewer shows |
| **L2 Certify** | E2, E3, E4, E11 for S0, S1, S2, S3 and H | `make -C engine check`: every engine book certifies; a test fails if any book contains `skip-proofs` or `defaxiom`, or if an opcode of the E1 census is outside the theorem's subset predicate |
| **Litmus** | L1 and L2 at the same commit, on the same module checksum | `make -C engine litmus` runs both and prints the module checksum, the fork commit, and the hypotheses of the top theorem |

What stays trusted when the litmus passes, and is printed with it: the
translator and SpecTec (evidence: the spec test suite), the engine's
loader (evidence: differential tests), the host functions (evidence: the
pixel comparison), ACL2 itself.

### Order and dependencies

```
E1 ------------------------------> E9 -> E10
E0 -> E5 -> E6 -> E7 -> E8 -------> E9
E2 -> E3 -> E4 -> E11 (needs E6, E7 for each group)
```

The run track (E0, E1, E5 to E10) does not wait for the proof track (E2,
E3, E4, E11). Every item runs headless. Suggested order of sessions: E1,
E0, E2, E5, E6, E3, E4, E7, E11 for S0, E8, E9, E10, E11 for the rest
(E2, E5, the E3 statement and E4 item 2 were done first, on 2026-11-15).
E11 for S0 comes before E8 on purpose: if the simulation proof forces a
change of the machine, it is cheaper before the machine is widened.

### Deferred

- Unchecked engine with a `Module_ok` hypothesis (D2).
- The engine through JSCL in the browser demo.
- SIMD, GC, tail calls, multi-memory: MuPDF uses none.
- A theorem about the decoder or the loader. The loader is compared by
  test only (E6).
- A different representation of memory in the generated semantics (D9).

### When a headless session stops

It stops, with the evidence in a note and "Current state" updated, only:

- at a go/no-go exit that says no-go (E2, E7);
- when a gate that was green cannot be made green again without
  weakening it;
- when a proof item has failed three distinct approaches, each recorded
  with its checkpoint;
- when a new decision is the user's (anything that changes what the
  litmus test means, what is trusted, or the non-interference rule).

It does not stop for a choice this plan settles, or for a long run: gates
and spec runs take minutes to tens of minutes and run in the background.

---

## 5. Risks and go/no-go points

| Risk | What decides it | If it happens |
|---|---|---|
| The 3.0 step group cannot be admitted in `:logic` | E2 | Proofs rehearse on 1.0; the 3.0 engine is tested, not proved; the user decides |
| The engine is too slow to render a page | E7 exit, from measured rate and instruction counts | Smaller MuPDF build; pre-render overnight; a faster machine design |
| The rebuilt MuPDF does not validate under `Module_ok`, or the decoder cannot handle 10 MB | E1 item 5 | The engine's own loader takes the binary; the disagreement is a finding about the generated validator and is reported |
| Proofs about the generated bodies are too slow for ACL2 | E4: certification time per rule lemma | D4 (a) is in place (E2); a rule lemma is about one small function |
| The spec's numeric functions are too slow for the fast machine (D6) | E7 rate | `mbe` fast paths, checked by guard verification (E5) |
| The `ctxt-*` recursion makes the context lemma hard | E11, tried on two instructions first. First evidence: a step under one label with a fixed instruction is proved in 10,141 prover steps ([E4-first-lemmas](notes/E4-first-lemmas.md)); symbolic lists are untested | Prove flat configurations first, then one nesting form at a time |
| Exceptions make `abs` and the invariant much larger | E5 design, E11 S3 | S3 stays tested and unproved; MuPDF is then outside the proved subset and every run says so (D8) |
| The host functions hide behaviour the comparison misses | E9 pixel comparison on three PDFs | More PDFs; the host layer is named as trusted in every claim |
