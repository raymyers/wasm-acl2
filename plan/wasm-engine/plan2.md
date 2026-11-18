# Plan 2: the engine fully verified against the semantics

> **Goal**: one theorem, checked by ACL2, that says: what the engine that
> runs the demos computes is what the generated WASM 3.0 semantics
> (`W3T::STEP`, `W3T::STEPS/%FUEL`) computes, for every instruction the
> engine executes, with every hypothesis discharged for the states the
> loader builds. No `skip-proofs`, no `defaxiom`, no trust tag in any
> book the theorem depends on, and no code between the theorem and the
> run that the theorem does not cover.
>
> **Relation to [plan.md](plan.md)**: plan.md built the engine and its
> first proofs; its decisions D1 to D10 stand. This plan starts from the
> gaps that [evidence.md](evidence.md) lists (2026-11-17) and closes
> them. It replaces plan.md's E11, the rest of E7 Phase B, and E4 items
> 3 to 5. Per-session procedure and tech guidelines: [step2.md](step2.md);
> proof practice in full: [practices.md](practices.md).
>
> **What the theorem will not say** (unchanged): that the generated
> semantics is the WebAssembly specification (translator and SpecTec;
> see [../wasm3-translation/evidence.md](../wasm3-translation/evidence.md)),
> and what a host function does. ACL2 and SBCL stay trusted.
>
> **Status**: written 2026-11-17 at `4f18f50`. V0 to V6 are complete
> (V5 and V6 on 2026-11-18): T1 certifies, and T2 with one hypothesis
> that V7 removes (no `call_ref`). P1 and P3 are decided; P2 is now
> the user's to decide (§2).

---

## Current state

- **Last updated**: 2026-11-18 (V6)
- **Milestones complete**: V0 (ground work;
  [V0-ground](notes/V0-ground.md)), V1 (dispatch lemmas;
  [V1-dispatch](notes/V1-dispatch.md)), V2 (the flat block;
  [V2-flat](notes/V2-flat.md)), V3 (contexts;
  [V3-contexts](notes/V3-contexts.md)), V4 (exits and propagation;
  [V4-exits](notes/V4-exits.md)), V5 (T1;
  [V5-t1](notes/V5-t1.md)) and V6 (the fast machine's invariant,
  loader and run; [V6-inv](notes/V6-inv.md)). The gate certifies 33
  books
- **T1 certifies**: `machine-result-is-spec-result`
  (`engine/machine/spec-result.lisp`), the statement of §1 word for
  word. F1 is met
- **T2 certifies with one hypothesis more than §1**:
  `fast-result-is-spec-result` (`engine/fast/spec-result.lisp`) has
  `(no-call-ref-run n (fm->ms fm))`, "the run has no `call_ref` at the
  head of its instructions". V7 removes it. F2 and F3 are not met yet
- **Next action**: V7 (no excluded instruction). Its frame lemmas are
  now V7b, optional (user, 2026-11-18): V7 is `call_ref` only
- **From V6, for later milestones**:
  - `fm-inv` (`fast/inv.lisp`) is `fmp`, `fast-inv-store` of the store
    and `machine-ok` of `fm->ms`. `fast-step-keeps-fm-inv` has two
    hypotheses besides it: the head is not `call_ref`, and the step does
    not end `:unsupported`. `fast-run-is-machine-run` and
    `fast-run-keeps-fm-inv` have `no-call-ref-run` and "the run does not
    end `:unsupported`"
  - V7 has to remove the `call_ref` hypothesis from three lemmas:
    `fast-step-refines` (`refine-op.lisp`), `fast-op-step-keeps-fmp` and
    `fast-op-step-keeps-inv-store` (`inv.lisp`). The last two need only
    the place lemma of `(:op :call_ref)`; "a rule that fires and is not
    refused leaves a fast store" is already proved for every rule
    (`fast-apply-rule-keeps-inv-store`)
  - the loader: `fm-inv-of-fm-load-ms` and `fm->ms-of-fm-load-ms` for a
    list state with `fm-loadable-p`; `machine-ok-of-ms-of-config`,
    `machine-abs-of-ms-of-config` and `fm-loadable-p-of-ms-of-config`
    for a configuration with `config-shape-p`, which is defined in
    `inv.lisp` (executable, guard `t`). V8's `engine-run` is
    `fast-run` of `fm-load-ms` of `ms-of-config`
  - **a store with no memory is outside T2's loader and T3**:
    `config-shape-p` asks that memory 0 is a record with a byte list
    (`fast-inv-store` needs a memory). A store with several memories is
    inside ([V6-inv](notes/V6-inv.md) §4)
  - `fast-clocks n fm` is `(machine-clocks n (fm->ms fm))`, not
    executable. It is a bound on the specification's fuel only
  - **the machines did not change**; `fallback-shape-ok` was not
    strengthened. One old book changed: the generator `length-lemma` of
    `rules/shape.lisp` is `not-length-lemma`, so that the books of the
    two machines' proofs load together
  - the slides on the fast machine: `config-shape-p`, `fm-inv` and a
    result on each of 12 runs (checked at run time), 7 of 7 identical
    to V8. They are not inside T2 until V7: every call is a `call_ref`
- **From V5, for later milestones**:
  - T1 has no hypothesis about an opcode: C2
    (`machine-step-simulates`) holds for every running state with
    `machine-ok`. `machine-clocks` is defined in `spec-result.lisp`
    (the model for `fast-clocks`)
  - **the machine did not change.** The proved set is the supported
    set: `*proved-opcodes*` (`machine/opcodes.lisp`, 48 opcodes,
    computed from the rule table and `redex-arity`) with
    `op-step-outside-proved-opcodes` and
    `machine-step-outside-proved-opcodes`. It has the 33 opcodes of D5
    that head an `op-step` redex, `memory.init`, `data.drop`,
    `ref.null` and 12 more; `*d5-opcodes*` of `fast/frame.lisp` is
    smaller, which is V7's to settle
    ([V5-t1](notes/V5-t1.md) §4, open questions)
  - bulk memory is clock 1, as every instruction that is not a value
    and not an administrative term; `machine-clock` did not change
  - the slides driver on the list machine (`ENGINE=list`) checks at
    run time that the loaded state has `machine-ok` and abstracts to
    the configuration; V6's loader lemma makes that a theorem
- **From V4, for later milestones**:
  - C2 holds for every clock-1 case of `machine-step`:
    `exit-step-simulates` (hypotheses besides `machine-ok`: `ctrl` not
    empty, the step ends `:run`), `anyprefix-step-simulates` (the head
    is `TRAP` or `THROW_REF`, the step ends `:run`),
    `op-step-simulates-throw_ref-null` (the head is `THROW_REF`, the
    top of the stack has the head `:ref.null_addr`, `op-step` ends
    `:run`) and V3's `op-step-simulates`. Each hypothesis is a test
    `machine-step` makes before the call
  - `block-step-simulates` (`machine/exit-steps.lisp`): a step of the
    innermost block that keeps the control stack is C2 for the two
    states
  - every pure and every read rule returns a true list (182 of 182
    `<R>-INSTRS-TRUE-LISTP`); `*instrs-not-yet*` of `rules/flat.lisp`
    is covered by `rules/exits.lisp`
  - **the machines changed** (a bug, [V4-exits](notes/V4-exits.md) §6):
    `machine-step` and `fast-step` test the head `:ref.null_addr` (it
    was `:ref.null`, which no value has) before they give `throw_ref`
    to `op-step`. `machine-ok` did not change. Tests 1, 2, 3, lockstep
    and the slides were run again (V4 below)
  - "a block at `br` or `return` does not step" is not used by C2 (the
    rules of an administrative term come before the context rules in
    `STEP`); it is there for V10
- **From V3, for later milestones**:
  - `op-step-simulates` is C2 for `op-step` under any control stack. Its
    hypotheses besides `machine-ok`: the head is not administrative, not
    `TRAP`, not `THROW_REF`, and `op-step` ends `:run` (those of V2
    without the empty `ctrl`)
  - `step-under-ctrl` asks of the innermost block `b`: a true list, it
    steps, the state of the step has the shape `(s; f)`, and
    `(not (exit-body-p b))`. For a block that is values, an instruction
    whose head is not a value's, and a rest, the last follows from the
    step (`not-exit-body-p-when-block-steps`); for values, an
    administrative term and a rest it holds always. These are the blocks
    of `anyprefix-step` and of the entry around an `exit-step`
  - the 24 rules whose redex is an administrative term are all pure or
    read: none comes after a context rule in `STEP`. So V4 item 1 has no
    case where "the context rule must fail first"; what it needs is what
    each rule returns and that `try-rules` picks it
  - `step-of-vals-exit-instr-rest`: `(z; vals ++ (i) ++ r)` does not
    step when the head of `i` is `br`, `return` or `return_call_ref`
  - **the machine changed** (a bug, [V3-contexts](notes/V3-contexts.md)
    §6): `enterable-p` and `entry-ok` ask that the catch clauses of a
    handler are a true list, as `Step/ctxt-handler` does. `machine-ok` is
    stronger by that conjunct. Tests 1, 2, 3, lockstep and the slides
    were run again (V3 below)
- **From V2, for later milestones**:
  - `op-step-simulates-flat` is C2 for `op-step` with an empty control
    stack. Its hypotheses besides `machine-ok`: the head is not
    administrative, not `TRAP`, not `THROW_REF`, and `op-step` ends
    `:run`. `throw_ref` under `ref.null` is V4 item 3
  - for the induction step of V3's context lemma:
    `step-of-admin-term-in-flat-block` (`STEP` of `v ++ (term) ++ r`
    from `STEP` of the term alone, `v` or `r` not empty) and
    `step/r-ctxt-{label,handler,frame}-fails-when-not-shape`
  - `Step/ctxt-instrs` is `flat-search` on `x ++ (i) ++ r`
    (`step/r-ctxt-instrs-becomes-flat-search`); V4 uses it to show that
    a block does not step
  - 12 rules have no `<R>-INSTRS-TRUE-LISTP` lemma (`*instrs-not-yet*`
    in `rules/flat.lisp`): the pure and read rules that return what a
    search found. Their redex is an administrative term or a whole
    block, so V3's exit rules and V4 need the fact for them
  - `machine-ok` did not change: a function reference among values names
    a natural number, which is what `call_ref` needed from V1
- **From V1, for later milestones**:
  - on a redex of head `kw`, `try-rules` over the pure, read and own
    rules of `(rules-for (head-place kw))` is `STEP_PURE`,
    `STEP_READ/SPLIT` and `step-own` (the rest of `STEP`'s body);
    `try-rules-of-rules-for` splits the table's list into the three
  - excluded there: head `TRAP` (pure) and head `THROW_REF` (read), where
    a rule on a whole block can fire. They are V4's, with `throw_ref-null`
  - `<R>-ARITY` for 89 rules: `redex-arity` of the last element is the
    number of elements before it. The 51 heads without one are the heads
    `redex-arity` refuses: V5 item 4's table
  - the three `call_ref` arity lemmas for a function reference have the
    hypothesis `(natp a)` for `(:ref.func_addr a)`: the rules match the
    reference by shape, `redex-arity` asks a natural number. V2 gets it
    from the operand being a value; if `machine-ok` does not say that
    operands are values, the invariant gets that fact
    ([V1-dispatch](notes/V1-dispatch.md) §5)
- **From V0, for later milestones**: the demos apply 37 rule functions.
  `memory.init`, `data.drop` and `ref.null` run at every instantiation
  and are outside `*d5-opcodes*`: V5's table of proved opcodes must
  contain them. Every call is a `call_ref` of a wasm function (V7 item
  3). A generated lemma about a rule function is proved in a theory with
  no other definition of the specification (`spec-definitions` of
  `rules/step-basics.lisp` disabled); a step limit does not stop the
  preprocessing otherwise. New books may use only the system books the
  Nix ACL2 has certified (no `std/lists/top`)
- **Decided by the user (2026-11-17)**: P1, host calls stay outside the
  theorem for now (the easy option); P2 is decided after V5
- **Decided by the user (2026-11-17)**: P3, the theorem covers D5
  (S0 to S3; H waits with P1)
- **Waiting for the user**: P2 (should `:stuck` carry a claim, V10).
  It was left for after V5; what is known about its cost is in
  [V5-t1](notes/V5-t1.md) §6. It blocks nothing: V6 to V9 do not
  depend on it
- **Theorem hypotheses so far**: those of plan.md "Current state",
  which for T1 are `(machine-ok s)`,
  `(machine-result-p (machine-run n s))`, `(natp fuel)` and
  `(< (machine-clocks n s) fuel)`. V1
  to V5 added none to a theorem of §1. V6 added one to T2,
  `(no-call-ref-run n (fm->ms fm))`: `fast-step-refines` excludes
  `call_ref` (its two host rules have no (U) lemma); V7 removes it.
  T2's other hypotheses are those of §1: `(fm-inv fm)`,
  `(fast-result-p (fast-run n fm))`, `(natp fuel)`,
  `(< (fast-clocks n fm) fuel)`. The loader lemmas ask
  `(config-shape-p c)` and `(fmp fm)`; the first excludes a store with
  no memory. The lemma hypotheses of V1 to V5 are
  listed in [V1-dispatch](notes/V1-dispatch.md) §4,
  [V2-flat](notes/V2-flat.md) §6,
  [V3-contexts](notes/V3-contexts.md) §4 and §5 and
  [V4-exits](notes/V4-exits.md) §5. `machine-ok`, the
  hypothesis of T1, got one conjunct in V3: the third component of a
  handler entry is a true list (it was asked of a label entry only).
  Reason: `Step/ctxt-handler` does not step the body otherwise, so C2
  was false for such a state. The loader's states have an empty control
  stack, so T3 is not affected

---

## 1. What "fully verified" means here

Three theorems, each built on the one before. The names are the ones
the gate (V9) will look for.

**T1, the list machine** (instance of `ENGINE-RESULT-IS-SPEC-RESULT`):

```lisp
(defthm machine-result-is-spec-result
  (implies (and (machine-ok s)
                (machine-result-p (machine-run n s))
                (natp fuel)
                (< (machine-clocks n s) fuel))
           (equal (w3t::steps/%fuel fuel (machine-abs s))
                  (list (machine-abs (machine-run n s))))))
```

**T2, the fast machine**, the one that runs:

```lisp
(defthm fast-result-is-spec-result
  (implies (and (fm-inv fm)
                (fast-result-p (fast-run n fm))
                (natp fuel)
                (< (fast-clocks n fm) fuel))
           (equal (w3t::steps/%fuel fuel (machine-abs (fm->ms fm)))
                  (list (machine-abs (fm->ms (fast-run n fm)))))))
```

No hypothesis about `:unsupported` and none about `call_ref`: a run
that ends with a result never refused, and `:unsupported` is not a
result.

**T3, the engine as it is called**: for a spec configuration `c` of
the shape the spec's `$invoke` returns,

```lisp
(defthm engine-run-is-spec-run
  (implies (and (config-shape-p c)
                (engine-result-p (engine-run n c fm))
                (natp fuel)
                (< (engine-clocks n c) fuel))
           (equal (w3t::steps/%fuel fuel c)
                  (list (engine-config (engine-run n c fm))))))
```

`engine-run` loads `c` into the stobj and calls `fast-run`. It is the
function the drivers call. `fm-inv` has become a fact proved about the
loader, so the only hypothesis about the input is its shape, which is
executable and which the driver checks.

**"Fully" then means all of**:

| | Condition | Today (evidence.md) |
|---|---|---|
| F1 | T1 holds for every rule the machine can apply, not for a group | C2 open for clock-1 steps. **Met in V5 (2026-11-18)** |
| F2 | T2 holds; the invariant is proved, not assumed | step theorem only. **V6 (2026-11-18)**: the invariant is proved (step, run, loader); T2 holds with a `call_ref` hypothesis |
| F3 | No instruction is excluded by hypothesis | `call_ref` excluded |
| F4 | The loader is inside the theorem (T3) | not proved |
| F5 | The code that runs is the function in the theorem | TeX: raw-Lisp loop, `data.drop` shortcut, host functions outside the hook |
| F6 | A gate fails if any of F1 to F5 stops holding | `no-skips` only |

Instantiation and decoding are the spec's own functions, run as they
are; they need no theorem. Whether `$instantiate` and `$invoke` are
`:logic` only decides whether T3 can also be stated from module bytes
(V8 item 5); T3 from a configuration does not need it.

---

## 2. Decisions for the user

- **P1 (decided by the user, 2026-11-17): host calls are not a concern
  now; do what is easy.** So: option (c) below. The fast machine stops
  `:unsupported` at a `call_ref` of a host function, which makes T2 and
  T3 unconditional without any fact about the hook. The slides are
  inside T3. The TeX driver keeps its own host step and loop, outside
  the theorem, and every TeX run says so (plan.md D8). Options (a) and
  (b) stay written here for when host calls matter. The question was:
  how host calls enter the theorem. The spec's
  `$hostcall` is the constrained `%hostcall-hook (hf s vals)`. T1 to T3
  hold for every such function. But `tex.wasm`'s 18 host functions are
  raw Lisp with their own state (open files, positions), they change
  the memory array directly, and the run loop steps over the
  `call_ref` itself. Options:
  - **(a) recommended.** The fast machine gets a host step in logic:
    its logical side calls `%hostcall-hook` on the full store, as the
    list machine does (proved, slow, exact). The TeX driver replaces
    the executable side by the fast host functions under a trust tag,
    in the driver only (the design of
    [E5-machine](notes/E5-machine.md) "Host calls"). The theorem then
    covers every instruction and the run loop; what stays trusted for
    TeX is one sentence: "the 18 Lisp functions behave as some function
    of (hostfunc, store, arguments)". Evidence for that sentence: the
    DVI comparison (V8 item 6).
  - **(b)** Host functions written in ACL2 over the spec store, with
    the files as data in the host function object, attached to the
    hook with `defattach`. Nothing trusted beyond ACL2, but file
    positions are state that must live somewhere in `(hf s vals)`, and
    each call builds the store from the array (72 MB for TeX). Likely
    too slow to typeset the deck; to be measured before choosing.
  - **(c)** Leave TeX outside: T3 is claimed for the slides only.
- **P2 (user, 2026-11-17: decide later, after V5; V5 is complete,
  so this is open for the user now; see
  [V5-t1](notes/V5-t1.md) §6): should `:stuck`
  carry a claim?** Today the
  theorem is one direction: a result of the machine is a result of the
  spec. `STEPS/%FUEL` also returns a configuration on which `STEP`
  fails, so "the machine is stuck, hence the spec stops there too"
  would make the two agree on every run that ends. It costs the
  failure of all 212 rules on the machine's stuck states (V10).
  Recommendation: decide after V5, when the dispatch lemmas exist and
  the cost can be measured.
- **P3 (decided by the user, 2026-11-17): D5.** The theorem covers the
  groups S0 to S3 of plan.md D5; H waits with P1. Every opcode outside
  the proved set stops the machine `:unsupported` (V5 item 4). The
  question was: scope. "Every rule the machine can apply"
  (212) or "the rules of D5" (S0 to S3 and H). Recommendation: prove
  D5, and make every opcode outside the proved set stop the machine
  with `:unsupported` (a generated table, V5 item 4). The theorem is
  then unconditional and the subset is visible in the code.

---

## 3. The proof, in outline

Layers as in evidence.md §1. What each milestone adds:

```
W3T::STEP
   ^  V1 dispatch: which rule functions can fire on a list
   ^  V2 flat block: STEP of (z; v ++ w ++ (i) ++ r)
   ^  V3 contexts: STEP under LABEL_/HANDLER_/FRAME_, by induction on ctrl
   ^  V4 exits and TRAP/THROW_REF among instructions
   ^  V5 C2, functional instantiation                      => T1
list machine
   ^  V6 invariant across a step, loader, run
   ^  V7 call_ref (V7b, optional: frame lemmas)            => T2
fast machine
   ^  V8 engine-run, the drivers call it, host step        => T3
the drivers
      V9 the gate
```

**Why C2 for a clock-1 step is three facts.** `STEP` tries `pure`,
`read`, `ctxt-instrs`, `ctxt-label`, `ctxt-handler`, `ctxt-frame`, then
its own rules, and returns the first result. The machine applies a rule
function `R` to a redex inside `machine-abs s`. So for each kind of
step:

1. *Dispatch*: no rule before `R` in `STEP`'s order fires on the redex,
   and no rule fires on the enclosing lists except through the context
   rules.
2. *Flat lift* (`ctxt-instrs`): `STEP/R-CTXT-INSTRS` computes the
   length `p` of the value prefix (`STEP/PREFIX7`) and searches `k`
   from `p` down to 0 (`STEP/SEARCH21`), calling `STEP` on the last
   `p - k` values and the instruction. So the redex with `j` operands
   is found only if `STEP` fails with fewer than `j`: the
   *operand-prefix* fact.
3. *Context lift*: a step of the block inside the innermost control
   entry is a step of the whole configuration. Each context rule first
   checks that the inner configuration is smaller (`%SIZE`); the check
   has to be proved true.

---

## 4. Milestones

Each item is done when its book certifies under `make -C engine
check`. Test before proving (D7) is already satisfied for V1 to V7 by
tests 1 to 3; an item that changes a machine re-runs the test named in
it.

### V0: ground work

- [x] Opcode census of the TeX run and of the slides: which rule
      functions each executes, with counts (a counter in the driver).
      Fixes the set V5 and V7 must cover, and says whether `call_ref`
      of a host function and `data.drop` occur (evidence.md §7 item 1).
      **Done**: 28 rule functions (slides, 3,626,696 applications), 34
      (`input.tex`, 27,946,273) and 34 (the deck, 305,651,715); 37 in
      the union. Host `call_ref`: 0, 3,717 and 63,681. `data.drop`: 1,
      40 and 40, at instantiation
      ([V0-ground](notes/V0-ground.md) §1)
- [x] `engine/lib/`: `lists.lisp` (the machine's `take-n`, `drop-n`,
      `app`, `rev-onto`, `len-t`, `nth-t` equal to `take`, `nthcdr`,
      `append`, `revappend`, `len`, `nth` under `true-listp`; then
      `len`, `car`, `cdr`, `take`, `nthcdr`, `true-listp` of `append`
      and of each other, from `std/lists` included locally) and
      `records.lisp` (the seven `put-assoc-equal` lemmas now in
      `frame.lisp`). Existing books include them instead of restating.
      **Done**: both books certify (2.0 s, 35 lemmas; 0.3 s).
      `frame.lisp` includes `records`. No old book includes `lists`: it
      would add its rules to their theories (next item but one); the
      three lemmas they restate keep their names there
      ([V0-ground](notes/V0-ground.md) §3)
- [x] One `ctrl-ok`. `machine/ok.lisp` and `fast/refine-op.lisp` define
      `WE::CTRL-OK` with different bodies, so the two books cannot be
      included together, and V6 must include both. The fast one becomes
      `ctrl-kinds-ok`, proved to follow from the machine's. **Done**:
      `fast/ctrl-kinds.lisp` includes both books and proves
      `ctrl-kinds-ok-when-ctrl-ok` ([V0-ground](notes/V0-ground.md) §4)
- [x] The existing books are not rewritten. Their proofs depend on the
      theory they have (in `refine-step.lisp` moving two lemmas after
      the generated ones cost a 6-hour run that did not come back), so
      [practices.md](practices.md) applies to new books, and to an old
      book only where a new book needs it: then the definitions it
      exports are disabled at its end, in a new last event, and the
      books that include it are certified again. Recorded per book,
      with certification times before and after. **Done**: no proof of
      an old book changed and none needed a disabling event yet; the
      changes are the `LICENSE` line, the include in `frame.lisp` and
      the rename in `refine-op.lisp`; times per book in
      [V0-ground](notes/V0-ground.md) §6
- [x] `stepn`, `step-opener` and the `%SIZE` facts in
      `engine/rules/step-basics.lisp`: `STEP` opened one level as a
      rewrite rule with a `syntaxp` guard, `STEP` returns `nil` or a
      one-element list of a well-shaped configuration, `%SIZE` of a
      proper sublist and of a subterm is smaller. **Done** (2.7 s):
      `step-opener`, `step-result-shape` (72,317 prover steps),
      `%size-check-of-admin-body`, `%size-check-of-sublist`, and the
      theory `spec-definitions`. Left to V2: that the state of the
      result has the shape `(:|%;%| s f)`
      ([V0-ground](notes/V0-ground.md) §5)

- [x] Spike, before the rest of V1 is built: the V1 exit statement for
      `nop` alone ("`STEP/R-PURE` and `STEP/R-READ` return `nil` on
      `v ++ (nop) ++ r`"), by hand in a session, with the library of
      item 2. It is the plan's largest risk (§5, first row); if it
      does not go through in three approaches, the session stops with
      the checkpoints in a note. **Done, go, first approach**: 8.3 s
      for the script, 722,354 prover steps in all, the rule functions
      closed ([V0-ground](notes/V0-ground.md) §2)

**Exit**: `make -C engine check` passes with the same theorems as
before; the census and the spike's result are in a note.

### V1: dispatch lemmas (plan.md E4 item 4)

- [x] `first-nonval`: the index of the first element that is not a
      value, proved equal to `STEP/PREFIX7`; its value on
      `v ++ (i) ++ r` is `(len v)` when `v` are values and `i` is not.
      **Done** in `rules/shape.lisp`: `step/prefix7-becomes-first-nonval`
      (446 prover steps), `first-nonval-of-append-of-vals-and-instr`
      ([V1-dispatch](notes/V1-dispatch.md) §1)
- [x] Per rule function, generated (the generator of
      `rules/terminal.lisp`): "if `R` fires on `(z; l)` then `l` has
      `R`'s shape": for a fixed-shape rule, `l` is `k` values and one
      instruction with `R`'s opcode, so `(len l)` is `k + 1`. Stated as
      a forward-chaining rule and as the rewrite "`R` returns `nil`
      when the last element's head is not `K`". **Done**: 201 rules,
      three lemmas each (`-FAILS-WHEN-NOT-SHAPE`,
      `-FAILS-WHEN-NOT-LENGTH`, `-SHAPE`), 1.7 s of proof time for the
      603; the length is read from the rule's body
      ([V1-dispatch](notes/V1-dispatch.md) §2)
- [x] The rules without a fixed shape, by hand: `trap-instrs` and
      `throw_ref-instrs` (their searches stop at the first non-value),
      the rules whose list is one administrative term, `block`, `loop`,
      `try_table`, `call`, `call_ref`, `throw` (operand count from a
      type). **Done**: the shape lemma for the nine rules with a count
      from a type, with no hint; two facts each for the two block rules;
      `<R>-ARITY` in `rules/arity.lisp` for 89 rules, of which
      `block`, `loop`, `try_table`, `throw` (2,471 to 2,738 prover
      steps) and the four `call_ref` rules (2,337 to 326,226) by hand:
      `redex-arity` is the rule's own count, so `redex-arity` does not
      change. `call` and the rules on an administrative term have a
      fixed shape and are generated
      ([V1-dispatch](notes/V1-dispatch.md) §3 to §5)
- [x] Per relation: `STEP_PURE` and `STEP_READ` on a list are the
      result of the rules of the last element's opcode, tried in order
      (`try-rules` over `rules-for`). This is the statement that the
      machine's table is `STEP`'s order. **Done** in
      `rules/dispatch.lisp`, for a symbolic head: `try-rules-of-pure-rules`
      (293,675 prover steps), `try-rules-of-read-rules` (995,909) and,
      for `STEP`'s own rules, `try-rules-of-own-rules` (411,019), from
      104 generated lemmas, one per relation and head; excluded: head `TRAP`
      (pure) and `THROW_REF` (read)
      ([V1-dispatch](notes/V1-dispatch.md) §6)
- [x] Census: every rule function of `*step-rules*` has its lemma.
      **Done**: each family ends with a check that fails its book: 212
      rules, 210 shape lemmas (the other two are the block rules), 201
      length lemmas, 89 arity lemmas (none for 97 rules of the 51 heads
      `redex-arity` refuses and for 26 on an administrative term or a
      block)

**Exit**: for a symbolic `v ++ (i) ++ r` with `r` or the extra values
not empty, "`STEP/R-PURE` and `STEP/R-READ` return `nil`" certifies for
`nop`, `binop` and `local.get` (the test plan.md §5 asks for first),
with prover steps recorded. **Met**: six theorems
`step/r-{pure,read}-of-vals-{nop,binop,local.get}-rest`, 254 to 5,098
prover steps each; the three books certify in 4.5 s, 7.4 s and 3.9 s
([V1-dispatch](notes/V1-dispatch.md) §7).

### V2: the flat block

- [x] *Operand prefix*: for an instruction with arity `k`
      (`redex-arity`), `STEP` of `(z; u ++ (i))` is `nil` for every
      value list `u` shorter than `k`. From V1's shape lemmas. For the
      type-dependent arities, by the same spec function the machine
      calls. **Done** in `rules/flat.lisp`: `no-step-below-arity`
      (5,685 prover steps), by induction on the number of operands,
      from "a rule that fires has `redex-arity` operands" per relation
      (`step_pure-arity` 88,197, `step_read/split-arity` 94,638,
      `step-own-arity` 45,866). `u` is the top of the machine's stack,
      `(operands j vals)` ([V2-flat](notes/V2-flat.md) §2, §4)
- [x] *`ctxt-instrs`*: for values `v`, `w` with `(len w) = k`, `i` not
      a value, `v` or `r` not empty, if `STEP` of `(z; w ++ (i))` is
      `(list (z'; is'))` then `STEP` of `(z; v ++ w ++ (i) ++ r)` is
      `(list (z'; v ++ is' ++ r))`. By induction on the search
      (`STEP/SEARCH21` counts down from the prefix length), with the
      size check from V0. **Done**: `step-of-flat-block` (31,917),
      also for `v` and `r` empty; the search is rewritten once to
      `flat-search` (`step/search21-becomes-flat-search`, 63,187)
      ([V2-flat](notes/V2-flat.md) §1, §5)
- [x] The same when the middle is one administrative term (arity 0).
      **Done**: `step-of-admin-term-in-flat-block` (1,673)
- [x] `op-step` at the top level (`ctrl` empty): C2 for a state whose
      head is an instruction with rules. **Done** in
      `machine/op-flat.lisp`: `op-step-is-step-of-flat-block` (155,593,
      any `ctrl`) and `op-step-simulates-flat` (2,653). Needed two
      generated families: the instructions of a pure or read rule are a
      true list (170 of 182 rules; the other 12 are not rules of an
      opcode) and the state of an own rule has the shape `(s; f)` (30
      of 30) ([V2-flat](notes/V2-flat.md) §3, §6)

**Exit**: `op-step-simulates-flat` certifies for every opcode with
rules, not per opcode: the opcode enters only through V1's per-relation
lemma. **Met**: one theorem for a symbolic head; hypotheses besides
`machine-ok` and the empty `ctrl`: the head is not administrative, not
`TRAP`, not `THROW_REF` (V4), and `op-step` ends `:run`. The two books
certify in 6.2 s and 2.6 s; the largest proof is 200,185 prover steps
(`try-rules-on-redex-is-step`).

### V3: contexts

- [x] One entry: if `STEP` of `(z_in; b)` is `(list (z_in'; b'))` and
      no exit rule fires on the term, then `STEP` of
      `(z; (list (admin-term k n x b)))` is the term with `b'`, for
      `:l`, `:h` and `:f` (`:f` changes the frame: `z_in` is the store
      with the entry's frame). Needs: the pure and read rules fail on a
      one-element list holding an administrative term whose body steps
      (V1), `ctxt-instrs` fails on it (no value, no rest), the size
      check. **Done** in `rules/context.lisp`: `step-of-admin-term`
      (1,641 prover steps) and, with values before and a rest after,
      `step-of-admin-term-in-block` (4,250); the three context rules on
      a body that steps in 1,746 to 3,997 steps each, the size check by
      linear arithmetic ([V3-contexts](notes/V3-contexts.md) §4)
- [x] *Exit rules do not fire on a body that steps*: `label-vals`,
      `br-label-*`, `trap-label`, `frame-vals`, `return-frame`, the
      handler rules, each need a body of a shape that does not step
      (values alone: `step-of-vals`; `TRAP` alone; values then `br` or
      `return`). So: a body that steps has none of those shapes.
      **Done**: 24 rules, 24 generated lemmas
      `<R>-FAILS-WHEN-NOT-EXIT-BODY` (4,127 to 7,842 steps) from 10
      lemmas about their searches (4,317 to 52,018);
      `step-of-vals-exit-instr-rest` (a block at `br`, `return` or
      `return_call_ref` does not step); `not-exit-body-p-when-block-steps`
      (2,009), for a block that is values, an instruction whose head is
      not a value's, and a rest
      ([V3-contexts](notes/V3-contexts.md) §1 to §3)
- [x] *Context lemma*: by induction on `ctrl`, with `abs-ctrl`
      generalized over `cur` and the frame: if `STEP` of the innermost
      block is `(list (z'; cur'))` then `STEP` of
      `(abs-of store frame vals is ctrl)` is the abstraction with
      `cur'` and the store and frame of `z'`. Each induction step is
      the one-entry lemma followed by V2's `ctxt-instrs`. **Done** in
      `machine/op-context.lisp`: `step-under-ctrl` (14,313 steps, no
      hint but `:induct`); its hypothesis besides the step is that the
      block is not the body of an exit
      ([V3-contexts](notes/V3-contexts.md) §5)
- [x] `op-step` under any control stack: C2. **Done**:
      `op-step-simulates` (64,282 steps)
- [x] Found on the way, a machine bug: a handler whose catch clauses
      are not a true list was entered, and the specification does not
      step under it. `enterable-p` and `entry-ok` changed; one old proof
      (`enter-step-keeps-abs`) got a hint. Tests after the change:
      test 1, 0 disagreements in 10 runs; test 2, 32,707 commands
      agree and none has another result (24 end at the machine's own
      fuel, where the spec, with the fuel it has since 2026-11-16,
      finishes); lockstep, 0 disagreements in 8 runs; test 3, 32,659
      commands equal, 0 different; slides 7 of 7 ([V3-contexts](notes/V3-contexts.md) §6, §8)

**Exit**: `op-step-simulates` certifies for any `ctrl` with
`ctrl-ok`. S3's handler form is in the same induction, not a later
case. **Met**: one theorem for a symbolic head and a symbolic control
stack; label, handler and frame entries in one induction. The two books
certify in 4.3 s and 2.6 s; the largest proof is 74,636
prover steps (`step_read/split/search118-shape`).

### V4: exits and propagation

- [x] `exit-step`: the redex is the administrative term itself. For the
      exit rules that are pure, V1 gives it. For those that come after
      the context rules in `STEP` (they read the store), the context
      rule must fail first: the body does not step. (V3 found that
      there are none: all 24 are pure or read.) Needs
      "`(z; vals ++ (br l) ++ r)`, `(z; vals ++ (return) ++ r)` and
      `(z; (ref.exn_addr a) (throw_ref))` do not step", by the
      generator of `terminal.lisp` on those shapes. **Done** in
      `rules/exits.lisp`: `step-of-admin-term-when-rule-fires` (6,322
      prover steps) and, with values before and a rest after,
      `step-of-exit-term` (16,250). The three "do not step" facts are
      not needed: `STEP` tries the pure and the read rules before every
      context rule, so a rule of the term that fires is `STEP`'s
      whatever the body is. What was needed instead: the 12 rules that
      return what a search found return a true list (12 of 12, 50 to
      404 steps, from 13 search lemmas of 2,326 to 10,427); all 182
      pure and read rules have that lemma now
      ([V4-exits](notes/V4-exits.md) §1, §2)
- [x] `anyprefix-step`: `trap-instrs` and `throw_ref-instrs` on the
      whole block; both are pure, so they are first in `STEP`.
      **Done**: `step-of-block-rule` (27,225). `throw_ref-instrs` is a
      read rule and `throw_ref-null` stands before it in the relation;
      where the first fires the second fails, since the first needs an
      exception reference before the `THROW_REF`
      (`step_read/split/search134-fails-when-not-exn-before-throw`,
      44,042) ([V4-exits](notes/V4-exits.md) §3)
- [x] `THROW_REF-NULL` (the one `op-step` reached through
      `throw_ref`). **Done**: `step-of-null-throw_ref-block` (5,626),
      V2's flat block for the head V2 excludes, with V2's search lemmas
      as they are ([V4-exits](notes/V4-exits.md) §4)
- [x] Both lifted by V3's context lemma. **Done** in
      `machine/exit-steps.lisp`: `block-step-simulates` (13,545) lifts a
      step of the innermost block; `exit-step` lifts the step of the
      block around the innermost entry through the rest of the control
      stack ([V4-exits](notes/V4-exits.md) §5)
- [x] Found on the way, a machine bug: `machine-step` and `fast-step`
      tested the head `:ref.null` on the operand stack, which no value
      has (a null reference is `(:ref.null_addr)`), so `throw_ref-null`
      was never applied and the machine ended `:stuck` where the
      specification steps to `TRAP`. One token changed in each machine;
      no old proof changed. Tests after the change:
      test 1, 0 disagreements in 10 runs; test 2, 32,706 commands agree
      and none has another result (24 end at the machine's own fuel);
      lockstep, 0 disagreements in 8 runs; test 3, 32,648 commands
      equal, 0 different; slides 7 of 7; the three configurations of
      the bug end `:trap` as the specification
      ([V4-exits](notes/V4-exits.md) §6, §8)

**Exit**: `exit-step-simulates`, `anyprefix-step-simulates`. **Met**:
`exit-step-simulates` (43,762 prover steps; hypotheses besides
`machine-ok`: `ctrl` not empty, the step ends `:run`),
`anyprefix-step-simulates` (93,769; the head is `TRAP` or `THROW_REF`,
the step ends `:run`) and `op-step-simulates-throw_ref-null` (69,546;
the head is `THROW_REF`, the top of the stack has the head
`:ref.null_addr`, the step ends `:run`). The two books certify in
2.9 s and 2.4 s; the largest proof is 197,944 prover
steps (`first-nonval-when-vals-then-exn-throw`).

### V5: T1

- [x] `machine-step-simulates`: C2 for every running state with
      `machine-ok`, from `machine-clock-0-simulates`, V3 and V4, by the
      case split of `machine-step` (each case a lemma, definitions
      closed). **Done** in `machine/spec-result.lisp`:
      `machine-step-clock-1-cases` (7,473 prover steps; four disjuncts,
      each a step function with the tests made before it),
      `machine-clock-1-simulates` (31,884), `machine-step-simulates`
      (927) ([V5-t1](notes/V5-t1.md) §1)
- [x] The instance: `machine-result-is-spec-result` by
      `:functional-instance` of `ENGINE-RESULT-IS-SPEC-RESULT` with C1
      (`ok.lisp`), C2, C3 (`terminal-ok.lisp`), C4. **Done**: 551
      prover steps, no hint but the instance; C4 is
      `machine-result-not-running` (51); `machine-clocks` defined with
      its guard verified ([V5-t1](notes/V5-t1.md) §2)
- [x] Bulk memory: check that `memory.fill`, `memory.copy` and
      `memory.init` are clock 1 in this machine (the rule functions
      rewrite to smaller instructions; E5 expected a larger clock). If
      not, `machine-clock` is corrected and test 1 re-run. **Done**:
      clock 1; their 10 rules are read rules and C2 is proved with no
      hypothesis about the head. `machine-clock` did not change
      ([V5-t1](notes/V5-t1.md) §3)
- [x] P3: the generated table of proved opcodes; an opcode outside it
      stops the machine `:unsupported` before any rule is tried. Test 2
      re-run: the agreeing commands do not change for D5. The table
      must contain `memory.init`, `data.drop` and `ref.null`, which
      every instantiation runs ([V0-ground](notes/V0-ground.md) §1).
      **Done, without a change of the machine** in
      `machine/opcodes.lisp`: `*proved-opcodes*`, 48 opcodes, by
      `make-event` from the rule table and `redex-arity`;
      `op-step-outside-proved-opcodes` (8,793 prover steps) and
      `machine-step-outside-proved-opcodes` (219,009); the book's last
      event fails unless the table has 48 opcodes, D5's and the three
      of instantiation. C2 was proved for a symbolic head, so the
      proved set is the supported set and the machine already refused
      the rest; test 2 was not run again, no machine function changed
      ([V5-t1](notes/V5-t1.md) §4)
- [x] The slides: `render.lsp` on the list machine is inside T1; say so
      in the viewer caption (plan.md D8). **Done**: `ENGINE=list sh
      engine/slides/run.sh`: 12 runs, the hypotheses of T1 true on
      each (checked at run time), 7 of 7 slides identical to V8, 40.5
      to 115.8 s per slide; the caption says which machine ran and
      whether its runs are inside a theorem
      ([V5-t1](notes/V5-t1.md) §5)

**Exit**: T1 certifies. F1 met. The slide deck is rendered by a
machine with an end-to-end theorem (the list machine; the fast one
after V6). **Met**: the two books certify in 2.3 s and 3.0 s; the
largest proof is 219,009 prover steps
(`machine-step-outside-proved-opcodes`). "End-to-end" for the slides
is T1 with its `machine-ok` hypothesis checked on each run; the
loader lemma that removes the check is V6's.

### V6: the fast machine's invariant, loader and run

- [x] `fm-inv`: `fmp`, `fast-inv-store`, `machine-ok (fm->ms fm)` (which
      gives `ctrl-kinds-ok`). One predicate, executable, guard `t`.
      **Done** in `fast/inv.lisp`: a function of the stobj, guards
      verified ([V6-inv](notes/V6-inv.md) §1)
- [x] *A step keeps it*, when the step does not refuse. Parts: the
      array stays a byte list (proved); `fast-inv-store` after a
      frame-safe rule (proved), after a memory rule (the store is
      unchanged or has its own bytes field empty), after the fallback
      (the machine already refuses a result it cannot hold:
      `fallback-shape-ok`; prove that what it accepts satisfies
      `fast-inv-store`); `machine-ok` from `fast-step-refines` and C1.
      **Done**: `fast-step-keeps-fm-inv` (742 prover steps), with "the
      head is not `call_ref`" besides. The store part is one lemma for
      any rule, `fast-apply-rule-keeps-inv-store` (440), from 9
      generated per-rule lemmas (the 5 frame-safe rules that return a
      configuration, 513 to 180,753; the 4 store rules of the fast
      path, 133,211 to 439,049), `fast-apply-fallback-keeps-inv-store`
      (3,399) and "a pure or read rule returns its state" (6,035). What
      `fallback-shape-ok` accepts is enough
      ([V6-inv](notes/V6-inv.md) §2, §3)
- [x] `:unsupported`, `:stuck`, `:done`, `:trap`, `:throw` are
      absorbing for `fast-step`. **Done**: `fast-step-when-not-running`
      (116) and `fast-run-when-not-running` (123), for every status but
      `:run`
- [x] *Run*: `(fm->ms (fast-run n fm))` is
      `(machine-run n (fm->ms fm))` when the fast run does not end
      `:unsupported`; by induction on `n`. **Done**:
      `fast-run-is-machine-run` (984) and `fast-run-keeps-fm-inv`
      (856), from two inductions (1,313 and 6,803); hypotheses `fm-inv`,
      `no-call-ref-run`, and the run does not end `:unsupported`
- [x] *Loader*: `(fm-inv (fm-load-ms s fm))` and
      `(fm->ms (fm-load-ms s fm)) = s` for a list state `s` whose store
      has memory 0 a record with a byte list and all fields
      (`list-to-mem` then `mem-to-list` is the identity on a byte
      list). `ms-of-config`: `machine-ok` and
      `(machine-abs (ms-of-config c)) = c` under `config-shape-p`.
      **Done**: `fm-inv-of-fm-load-ms` (365; it asks `(fmp fm)` and
      `(fm-loadable-p s)`), `fm->ms-of-fm-load-ms` (175),
      `machine-ok-of-ms-of-config` (1,495),
      `machine-abs-of-ms-of-config` (1,600),
      `fm-loadable-p-of-ms-of-config` (835); `config-shape-p` is defined
      here ([V6-inv](notes/V6-inv.md) §5)
- [x] Stores with no memory, or several: either the invariant covers
      them (the run-time check `fast-one-memory-p` already sends them
      to the fallback) or the loader refuses them. Decide by what the
      proof of the previous item needs; record it. **Decided**: several
      memories are inside (the invariant asks of memory 0 only; the
      memory rules take the fallback, which is covered). No memory is
      outside: `fast-inv-store` needs a memory, and `config-shape-p`,
      the executable hypothesis the driver checks, says so; `fm-load-ms`
      did not change ([V6-inv](notes/V6-inv.md) §4)
- [x] T2 with `call_ref` still a hypothesis of the step, carried as
      "the run executes no `call_ref`" (removed by V7). **Done** in
      `fast/spec-result.lisp`: `fast-result-is-spec-result` (2,080),
      from T1 for `(fm->ms fm)` and the run lemma; the hypothesis is
      `(no-call-ref-run n (fm->ms fm))`. `fast-clocks` is
      `machine-clocks` of `fm->ms`
- [x] The slides on the fast machine print, per run, `config-shape-p`
      of the configuration, `fm-inv` of the loaded stobj and
      `fast-result-p` of the last one: true on each of 12 runs; 7 of 7
      identical to V8. The caption says that the runs are not inside a
      theorem until V7 ([V6-inv](notes/V6-inv.md) §8)

**Exit**: T2 certifies with that one hypothesis. Lockstep and test 3
re-run if `fast.lisp` changed. **Met**: the two books certify in 9.1 s
and 2.2 s; the largest proof is 439,049 prover steps
(`fast-apply-rule-of-step/r-store-pack-val-keeps-inv-store`).
`fast.lisp` did not change, so lockstep and test 3 were not run again.

### V7: no excluded instruction

- [ ] P1 as decided: `fast-step` stops `:unsupported` when the
      instruction is `call_ref` and the reference is a host function
      (the test the TeX driver's loop already makes), so the two host
      rules are never applied by the fast machine and need no lemma.
      Lockstep and test 3 re-run. The next item is then not done; it
      is kept for when host calls matter
- [ ] (Deferred with P1.) The two `call_ref` host rules (`*u-not-yet*`): they call
      `$hostcall` on the store, so nothing can be said about the hook's
      result. They go through the exact fallback (bytes put back, the
      rule on the full store, the result copied out). The fallback is
      proved in general; what is missing is the per-rule fact
      `<rule>-FAILS-PLAINLY` for these two (`*fallback-not-yet*` in
      `refine.lisp`). First item of work: read why that fact is
      needed and state it about the hook as an unknown function; if it
      is false for some hook, the host step calls the fallback
      unconditionally (P1 (a)'s host step) and the fact is not needed
- [ ] `call_ref` of a wasm function: its place lemma, now that the
      place no longer holds an unproved rule
- [ ] `no-call-ref-run` is removed from `fast-step-refines`,
      `fast-op-step-keeps-fmp`, `fast-op-step-keeps-inv-store`, the run
      lemmas and T2 ([V6-inv](notes/V6-inv.md) §7)
- [ ] `*fallback-not-yet*`, `*u-not-yet*` and `*places-not-yet*` are
      settled and their checks say so: each is empty, or what is left
      is the two host rules together with a theorem that the fast
      machine does not apply them. `*frame-not-yet*` is not part of
      this: a rule on it takes the fallback, which is proved exact (V7b)

**Exit**: T2 as written in §1. F2 and F3 met.

### V7b (optional, not on the path to T2 or T3): frame lemmas

Changed 2026-11-18 (user): these were items of V7. They are not needed
for a theorem. A rule without a frame lemma takes the fallback, and the
fallback is proved exact; a frame lemma makes the rule faster and, for
`data.drop`, removes a shortcut of the TeX driver. To be done after V7,
at any time, or not at all.

- [ ] Frame lemmas for `data.drop`, `elem.drop` and `ref.cast-succeed`
      (the driver's shortcut for `data.drop` becomes a theorem and the
      `sb-int:encapsulate` in `texrun.lisp` is deleted), with the
      record lemmas they need; the slow ones (`table.grow` 1,152 s)
      stay on the fallback, which is proved exact
- [ ] `*frame-not-yet*` holds only rules that are left on the fallback
      on purpose, each with its reason

**Exit**: the TeX driver has no `data.drop` shortcut. Until then F5 for
TeX has that shortcut as one more exception, and the README of
`engine/tex` says so (V8).

### V8: the engine that runs is the engine in the theorem

- [ ] `engine/run.lisp`: `engine-run` (load, `fast-run`), `engine-config`
      (the abstraction of the final stobj), `engine-clocks`; logic
      mode, guards verified. T3 from T2 and V6's loader lemmas
- [ ] The slides driver calls `engine-run` and nothing else of the
      engine. `make -C engine slides` still 7 of 7
- [ ] TeX with P1 as decided: the driver's loop calls `fast-run` between
      host calls (it resumes after each `:unsupported` stop at a host
      `call_ref`), so every stretch of wasm instructions is a run T2
      covers; the host steps and the resuming are outside. The README
      of `engine/tex` says this. The next two items are deferred with
      P1
- [ ] (Deferred.) The TeX driver's loop becomes `fast-run` (or
      `engine-run`) alone: no Lisp loop. Its rate measured against the
      195 s of the raw loop
- [ ] (Deferred.) Host step per P1 (a): `fast-host-step` in `fast.lisp`
      (logic: the list machine's step; exec: the fallback), the driver
      installs the fast host functions under a trust tag in
      `texrun.lisp`, and the README of `engine/tex` states the one
      trusted sentence
- [ ] If `$instantiate` and `$invoke` are `:logic` (check the mode
      manifest): T3 stated from a decoded module and an export name.
      If not, recorded as outside, with the functions that are
      `:program`
- [ ] DVI comparison with a native e-TeX of the same revision, byte
      for byte (evidence.md §7 item 2): the test for what P1 leaves
      trusted

**Exit**: T3 certifies; both drivers run through it. F4 and F5 met
(F5 for TeX up to the sentence of P1).

### V9: the gate

- [ ] `engine/top.lisp` includes the proof books and restates T1, T2,
      T3 verbatim (redundant events: certification fails if a
      statement drifts)
- [ ] `make -C engine check` also fails if: a book under `top.lisp`
      has a trust tag (`cert.pl` flags, `:ttags`); a `*-not-yet*`
      constant is not as V7 settled it (`*frame-not-yet*` excepted: it
      lists rules on the proved fallback, V7b); `top.lisp` does not
      certify. The existing
      `no-skips` grep stays, and is joined by a check of the
      certificates themselves (`skip-proofs` and `defaxiom` recorded
      by ACL2 in the `.cert`), since a macro can hide either from a
      grep
- [ ] evidence.md rewritten from the new state: its table of §1 with
      "Proved" in every row that is the engine's
- [ ] plan.md "Milestones for the test": L2 points here

**Exit**: F6 met.

### V10 (only if P2 says yes): the stuck direction

- [ ] For each way the machine reports `:stuck`, `STEP` of the
      abstraction is `nil`: all rules fail (V1's shape lemmas, the
      operand-prefix lemma for too few operands, a rule's own premise
      failing)
- [ ] `m-result-p` widened to `:stuck`; C3 for it; T1 to T3 restated

### Order and dependencies

```
V0 -> V1 -> V2 -> V3 -> V4 -> V5 (T1)
V0 -> V6 -> V7 (T2)        V6's last step needs nothing from V1..V5
V5, V7 -> V8 (T3) -> V9
V7 -> V7b                  optional; nothing depends on it
```

V1 to V5 and V6 to V7 are independent after V0 and can be worked in
separate sessions; they touch different directories (`rules/`,
`machine/` against `fast/`).

---

## 5. Risks

| Risk | What decides it | If it happens |
|---|---|---|
| Proofs over a symbolic `v ++ (i) ++ r` blow up (the 35-minute lemma of E6). **Did not happen in V1**: the largest such proof is 31,304 prover steps | V1 exit: three opcodes, prover steps recorded | Keep every rule function closed and reason only through V1's shape lemmas; never open `STEP` with rule definitions enabled ([E3-theorem](notes/E3-theorem.md), attempt 2: 359 s of preprocessing) |
| The `%SIZE` check in the context rules is hard to discharge for a symbolic body. **Did not happen in V3**: linear arithmetic after `%size-of-cons` | V0 item 5, tried on one label first | Prove `%SIZE` monotone for the three administrative forms only, not in general |
| The machine's choice of redex differs from `STEP`'s on some state the tests never reached. **Did not happen in V2**: no failed checkpoint was a machine state. **Happened once in V3**: a handler whose catch clauses are not a true list; fixed, tests re-run. **V4**: no failed checkpoint was a machine state; one bug of the other direction was found by reading a rule (the machine was stuck at `throw_ref` under a null reference, where the spec steps); fixed, tests re-run | V2's operand-prefix lemma and V4's "body does not step" lemmas fail with a checkpoint that is a real state | That is a machine bug: fix the machine, re-run tests 1 and 2, record it (as test 3 did for several memories) |
| A type-dependent arity (`block`, `call_ref`, `throw`) cannot be related to the rule's own count. **Settled in V1**: it is related, for all eight rules; a function reference needs `(natp a)` | V1 item 3 | The machine computes the arity by the rule's own subterm; `redex-arity` changes, test 1 and 2 re-run |
| The fallback's accepted results do not imply `fast-inv-store`. **Did not happen in V6**: `fast-apply-fallback-keeps-inv-store`, with `fallback-shape-ok` as it was | V6 item 2 | Strengthen the run-time check (`fallback-shape-ok`); the machine refuses more, the theorem is unchanged |
| The logic-mode run loop is slower than the raw one for TeX | V8 item 3, measured | `fast-run` is already guard-verified and tail recursive; if the host check per step costs, dispatch on `call_ref` inside `fast-step` |
| P1 (b) is too slow | measured on one host call with the 72 MB store | P1 (a) |

A headless session stops in the cases of plan.md "When a headless
session stops", read for this plan.

## 6. What stays trusted when V9 passes

ACL2 and SBCL; the translator and SpecTec (the semantics is the
specification by decision); the spec's decoder and instantiation as
implementations of the standard (they are the semantics, so not the
engine's to prove); for TeX with P1 (a), that the 18 host functions
are a function of their arguments and the store. Nothing else of the
engine.
