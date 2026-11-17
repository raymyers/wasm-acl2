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
> 3 to 5. Per-session procedure: [step2.md](step2.md).
>
> **What the theorem will not say** (unchanged): that the generated
> semantics is the WebAssembly specification (translator and SpecTec;
> see [../wasm3-translation/evidence.md](../wasm3-translation/evidence.md)),
> and what a host function does. ACL2 and SBCL stay trusted.
>
> **Status**: written 2026-11-17 at `4f18f50`. Nothing started. P1 and
> P3 are decided, P2 is decided after V5 (§2).

---

## Current state

- **Last updated**: 2026-11-17
- **Milestones complete**: none
- **Next action**: V0
- **Decided by the user (2026-11-17)**: P1, host calls stay outside the
  theorem for now (the easy option); P2 is decided after V5
- **Decided by the user (2026-11-17)**: P3, the theorem covers D5
  (S0 to S3; H waits with P1)
- **Waiting for the user**: nothing
- **Theorem hypotheses so far**: those of plan.md "Current state"

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
| F1 | T1 holds for every rule the machine can apply, not for a group | C2 open for clock-1 steps |
| F2 | T2 holds; the invariant is proved, not assumed | step theorem only |
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
- **P2 (user, 2026-11-17: decide later, after V5): should `:stuck`
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

## 3. Proof practice

From the ACL2 documentation topic `BEST-PRACTICES` and its subtopics
(`theory-management`, `naming-rewrite-rules`,
`conventional-normal-forms`, `working-with-packages`), read from
`books/doc/practices.lisp` of our ACL2 8.7. The file on the `master`
branch of `acl2/acl2` was compared on 2026-11-17: it differs in one
cross-reference and in no recommendation. All ten subtopics were read;
`file-names` is already followed, and `finite-reasoning` (GL for
bounded values) has no use here while the engine calls the spec's own
numeric functions (plan.md D6). Each rule below names what it changes
in `engine/`.

| Practice (the topic's words, shortened) | In `engine/` today | Rule for this plan |
|---|---|---|
| "`include-book` and `in-theory` events should be `local` where possible"; top-level ones "at the top of the book" | 3 local theory events in 15 books; `ok.lisp`, `clock0.lisp` and `refine-op.lisp` disable definitions non-locally in mid-book | A book has one header: includes, then one theory block. Library includes (`std/lists`, arithmetic) are always `local`; the lemmas a later book needs are restated in `engine/lib/` |
| "Most functions (especially non-recursive) should be disabled by default" | Definitions stay enabled; proofs then carry disable lists of 20 to 30 names (`fast-step-refines`) | Every machine definition is followed by its lemmas and then disabled, in the defining book. A proof enables what it opens |
| "Try to avoid subgoal hints... consider factoring out a subgoal into an auxiliary lemma" | None found; keep it so | No `"Subgoal"` hint. A case that needs one becomes a lemma |
| "The less hints the better. Consider whether `:use` or `:expand` hints may suggest good general-purpose rules" | `refine-op.lisp`: seven `:use` hints with hand-built instances | Before a `:use`, try the fact as a rewrite rule with the right free variables. Recursive spec functions get one `:expand`-style rewrite rule each, stated once (`step-opener`), not an `:expand` per proof |
| "Avoid short proof timeout windows... use step limits instead" | `set-prover-step-limit` in `refine-op.lisp` | Every proof book sets a step limit. No time limits |
| Rule names: `f-of-g`, `-when-hyp`, `-under-equiv`; no `lemma1`, `crock` | Mostly followed (`machine-abs-of-ms`); some not (`car-t-is-car`) | New lemmas follow it; generated lemmas are `<rule>-<property>` |
| "Write lemmas in terms of `(mv-nth n ...)`"; include `tools/mv-nth` | Lemmas use `cadddr` of an `mv` (`fast-try-rules-keeps-bytes`) | New lemmas use `mv-nth`; `mv-nth` disabled. Old ones are converted when their book is next touched |
| A widget library should not change how one reasons about built-ins | `machine.lisp` defines its own `take-n`, `app`, `len-t`, `rev-onto` | Keep them (guard `t` is why they exist), but V1 proves each equal to the built-in under the invariant and normalizes to the built-in, so one list library serves both |
| "A book should use either `defun` or `define`, not both" | `defun`/`defthm` everywhere | Stay with `defun`/`defthm`. No `std/util` conversion |
| "Sets of rules known to loop should be declared incompatible" (`theory-invariant`) | None | When V1 adds an opener and its inverse, a `theory-invariant` goes with them |
| Packages: `package.lsp`, empty `portcullis.lisp`, `cert.acl2` | Followed | No change |
| Certifiable books `.lisp`, scripts `.lsp` | Followed | No change |
| "Avoid introducing new Makefiles", use `cert.pl` | One Makefile that calls `cert.pl` | No change |
| Whitespace, comment and header rules | No license header in the books | V0 adds the header line pointing at `LICENSE` |

Three rules of our own, from what the notes record:

- **Generated lemma families end with an exact census.** `frame`,
  `refine` and `refine-step` already fail if the set of rules without
  a lemma is not the recorded one. Every new generated family does the
  same, and the recorded set must be empty when its milestone closes.
- **A generator never runs silently.** The 35-minute run of
  [E6-list-machine](notes/E6-list-machine.md) lost which lemmas had
  proved. Generators print one line per lemma and each lemma has a step
  limit.
- **Constants first, both orientations.** Rewrite rules about a head
  keyword are stated as `(equal (car x) kw)` and `(equal kw (car x))`
  ([E3-theorem](notes/E3-theorem.md)).

---

## 4. The proof, in outline

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
   ^  V7 call_ref, the last frame lemmas                   => T2
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

## 5. Milestones

Each item is done when its book certifies under `make -C engine
check`. Test before proving (D7) is already satisfied for V1 to V7 by
tests 1 to 3; an item that changes a machine re-runs the test named in
it.

### V0: ground work

- [ ] Opcode census of the TeX run and of the slides: which rule
      functions each executes, with counts (a counter in the driver).
      Fixes the set V5 and V7 must cover, and says whether `call_ref`
      of a host function and `data.drop` occur (evidence.md §7 item 1)
- [ ] `engine/lib/`: `lists.lisp` (the machine's `take-n`, `drop-n`,
      `app`, `rev-onto`, `len-t`, `nth-t` equal to `take`, `nthcdr`,
      `append`, `revappend`, `len`, `nth` under `true-listp`; then
      `len`, `car`, `cdr`, `take`, `nthcdr`, `true-listp` of `append`
      and of each other, from `std/lists` included locally) and
      `records.lisp` (the seven `put-assoc-equal` lemmas now in
      `frame.lisp`). Existing books include them instead of restating
- [ ] One `ctrl-ok`. `machine/ok.lisp` and `fast/refine-op.lisp` define
      `WE::CTRL-OK` with different bodies, so the two books cannot be
      included together, and V6 must include both. The fast one becomes
      `ctrl-kinds-ok`, proved to follow from the machine's
- [ ] Theory pass over the existing books by the table of §3: header,
      local includes, definitions disabled after their lemmas. No
      statement changes; `make -C engine check` before and after, with
      certification times recorded
- [ ] `stepn`, `step-opener` and the `%SIZE` facts in
      `engine/rules/step-basics.lisp`: `STEP` opened one level as a
      rewrite rule with a `syntaxp` guard, `STEP` returns `nil` or a
      one-element list of a well-shaped configuration, `%SIZE` of a
      proper sublist and of a subterm is smaller

**Exit**: `make -C engine check` passes with the same theorems as
before; the census is in a note.

### V1: dispatch lemmas (plan.md E4 item 4)

- [ ] `first-nonval`: the index of the first element that is not a
      value, proved equal to `STEP/PREFIX7`; its value on
      `v ++ (i) ++ r` is `(len v)` when `v` are values and `i` is not
- [ ] Per rule function, generated (the generator of
      `rules/terminal.lisp`): "if `R` fires on `(z; l)` then `l` has
      `R`'s shape": for a fixed-shape rule, `l` is `k` values and one
      instruction with `R`'s opcode, so `(len l)` is `k + 1`. Stated as
      a forward-chaining rule and as the rewrite "`R` returns `nil`
      when the last element's head is not `K`"
- [ ] The rules without a fixed shape, by hand: `trap-instrs` and
      `throw_ref-instrs` (their searches stop at the first non-value),
      the rules whose list is one administrative term, `block`, `loop`,
      `try_table`, `call`, `call_ref`, `throw` (operand count from a
      type)
- [ ] Per relation: `STEP_PURE` and `STEP_READ` on a list are the
      result of the rules of the last element's opcode, tried in order
      (`try-rules` over `rules-for`). This is the statement that the
      machine's table is `STEP`'s order
- [ ] Census: every rule function of `*step-rules*` has its lemma

**Exit**: for a symbolic `v ++ (i) ++ r` with `r` or the extra values
not empty, "`STEP/R-PURE` and `STEP/R-READ` return `nil`" certifies for
`nop`, `binop` and `local.get` (the test plan.md §5 asks for first),
with prover steps recorded.

### V2: the flat block

- [ ] *Operand prefix*: for an instruction with arity `k`
      (`redex-arity`), `STEP` of `(z; u ++ (i))` is `nil` for every
      value list `u` shorter than `k`. From V1's shape lemmas. For the
      type-dependent arities, by the same spec function the machine
      calls
- [ ] *`ctxt-instrs`*: for values `v`, `w` with `(len w) = k`, `i` not
      a value, `v` or `r` not empty, if `STEP` of `(z; w ++ (i))` is
      `(list (z'; is'))` then `STEP` of `(z; v ++ w ++ (i) ++ r)` is
      `(list (z'; v ++ is' ++ r))`. By induction on the search
      (`STEP/SEARCH21` counts down from the prefix length), with the
      size check from V0
- [ ] The same when the middle is one administrative term (arity 0)
- [ ] `op-step` at the top level (`ctrl` empty): C2 for a state whose
      head is an instruction with rules

**Exit**: `op-step-simulates-flat` certifies for every opcode with
rules, not per opcode: the opcode enters only through V1's per-relation
lemma.

### V3: contexts

- [ ] One entry: if `STEP` of `(z_in; b)` is `(list (z_in'; b'))` and
      no exit rule fires on the term, then `STEP` of
      `(z; (list (admin-term k n x b)))` is the term with `b'`, for
      `:l`, `:h` and `:f` (`:f` changes the frame: `z_in` is the store
      with the entry's frame). Needs: the pure and read rules fail on a
      one-element list holding an administrative term whose body steps
      (V1), `ctxt-instrs` fails on it (no value, no rest), the size
      check
- [ ] *Exit rules do not fire on a body that steps*: `label-vals`,
      `br-label-*`, `trap-label`, `frame-vals`, `return-frame`, the
      handler rules, each need a body of a shape that does not step
      (values alone: `step-of-vals`; `TRAP` alone; values then `br` or
      `return`). So: a body that steps has none of those shapes
- [ ] *Context lemma*: by induction on `ctrl`, with `abs-ctrl`
      generalized over `cur` and the frame: if `STEP` of the innermost
      block is `(list (z'; cur'))` then `STEP` of
      `(abs-of store frame vals is ctrl)` is the abstraction with
      `cur'` and the store and frame of `z'`. Each induction step is
      the one-entry lemma followed by V2's `ctxt-instrs`
- [ ] `op-step` under any control stack: C2

**Exit**: `op-step-simulates` certifies for any `ctrl` with
`ctrl-ok`. S3's handler form is in the same induction, not a later
case.

### V4: exits and propagation

- [ ] `exit-step`: the redex is the administrative term itself. For the
      exit rules that are pure, V1 gives it. For those that come after
      the context rules in `STEP` (they read the store), the context
      rule must fail first: the body does not step. Needs
      "`(z; vals ++ (br l) ++ r)`, `(z; vals ++ (return) ++ r)` and
      `(z; (ref.exn_addr a) (throw_ref))` do not step", by the
      generator of `terminal.lisp` on those shapes
- [ ] `anyprefix-step`: `trap-instrs` and `throw_ref-instrs` on the
      whole block; both are pure, so they are first in `STEP`
- [ ] `THROW_REF-NULL` (the one `op-step` reached through
      `throw_ref`)
- [ ] Both lifted by V3's context lemma

**Exit**: `exit-step-simulates`, `anyprefix-step-simulates`.

### V5: T1

- [ ] `machine-step-simulates`: C2 for every running state with
      `machine-ok`, from `machine-clock-0-simulates`, V3 and V4, by the
      case split of `machine-step` (each case a lemma, definitions
      closed)
- [ ] The instance: `machine-result-is-spec-result` by
      `:functional-instance` of `ENGINE-RESULT-IS-SPEC-RESULT` with C1
      (`ok.lisp`), C2, C3 (`terminal-ok.lisp`), C4
- [ ] Bulk memory: check that `memory.fill`, `memory.copy` and
      `memory.init` are clock 1 in this machine (the rule functions
      rewrite to smaller instructions; E5 expected a larger clock). If
      not, `machine-clock` is corrected and test 1 re-run
- [ ] P3: the generated table of proved opcodes; an opcode outside it
      stops the machine `:unsupported` before any rule is tried. Test 2
      re-run: the agreeing commands do not change for D5
- [ ] The slides: `render.lsp` on the list machine is inside T1; say so
      in the viewer caption (plan.md D8)

**Exit**: T1 certifies. F1 met. The slide deck is rendered by a
machine with an end-to-end theorem (the list machine; the fast one
after V6).

### V6: the fast machine's invariant, loader and run

- [ ] `fm-inv`: `fmp`, `fast-inv-store`, `machine-ok (fm->ms fm)` (which
      gives `ctrl-kinds-ok`). One predicate, executable, guard `t`
- [ ] *A step keeps it*, when the step does not refuse. Parts: the
      array stays a byte list (proved); `fast-inv-store` after a
      frame-safe rule (proved), after a memory rule (the store is
      unchanged or has its own bytes field empty), after the fallback
      (the machine already refuses a result it cannot hold:
      `fallback-shape-ok`; prove that what it accepts satisfies
      `fast-inv-store`); `machine-ok` from `fast-step-refines` and C1
- [ ] `:unsupported`, `:stuck`, `:done`, `:trap`, `:throw` are
      absorbing for `fast-step`
- [ ] *Run*: `(fm->ms (fast-run n fm))` is
      `(machine-run n (fm->ms fm))` when the fast run does not end
      `:unsupported`; by induction on `n`
- [ ] *Loader*: `(fm-inv (fm-load-ms s fm))` and
      `(fm->ms (fm-load-ms s fm)) = s` for a list state `s` whose store
      has memory 0 a record with a byte list and all fields
      (`list-to-mem` then `mem-to-list` is the identity on a byte
      list). `ms-of-config`: `machine-ok` and
      `(machine-abs (ms-of-config c)) = c` under `config-shape-p`
- [ ] Stores with no memory, or several: either the invariant covers
      them (the run-time check `fast-one-memory-p` already sends them
      to the fallback) or the loader refuses them. Decide by what the
      proof of the previous item needs; record it
- [ ] T2 with `call_ref` still a hypothesis of the step, carried as
      "the run executes no `call_ref`" (removed by V7)

**Exit**: T2 certifies with that one hypothesis. Lockstep and test 3
re-run if `fast.lisp` changed.

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
- [ ] Frame lemmas for `data.drop`, `elem.drop` and `ref.cast-succeed`
      (the driver's shortcut for `data.drop` becomes a theorem and the
      `sb-int:encapsulate` in `texrun.lisp` is deleted), with the
      record lemmas they need; the slow ones (`table.grow` 1,152 s)
      stay on the fallback, which is proved exact
- [ ] `*frame-not-yet*`, `*fallback-not-yet*`, `*u-not-yet*`,
      `*places-not-yet*` are empty and their checks say so

**Exit**: T2 as written in §1. F2 and F3 met.

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
      constant is not `nil`; `top.lisp` does not certify. The existing
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
```

V1 to V5 and V6 to V7 are independent after V0 and can be worked in
separate sessions; they touch different directories (`rules/`,
`machine/` against `fast/`).

---

## 6. Risks

| Risk | What decides it | If it happens |
|---|---|---|
| Proofs over a symbolic `v ++ (i) ++ r` blow up (the 35-minute lemma of E6) | V1 exit: three opcodes, prover steps recorded | Keep every rule function closed and reason only through V1's shape lemmas; never open `STEP` with rule definitions enabled ([E3-theorem](notes/E3-theorem.md), attempt 2: 359 s of preprocessing) |
| The `%SIZE` check in the context rules is hard to discharge for a symbolic body | V0 item 5, tried on one label first | Prove `%SIZE` monotone for the three administrative forms only, not in general |
| The machine's choice of redex differs from `STEP`'s on some state the tests never reached | V2's operand-prefix lemma and V4's "body does not step" lemmas fail with a checkpoint that is a real state | That is a machine bug: fix the machine, re-run tests 1 and 2, record it (as test 3 did for several memories) |
| A type-dependent arity (`block`, `call_ref`, `throw`) cannot be related to the rule's own count | V1 item 3 | The machine computes the arity by the rule's own subterm; `redex-arity` changes, test 1 and 2 re-run |
| The fallback's accepted results do not imply `fast-inv-store` | V6 item 2 | Strengthen the run-time check (`fallback-shape-ok`); the machine refuses more, the theorem is unchanged |
| The logic-mode run loop is slower than the raw one for TeX | V8 item 3, measured | `fast-run` is already guard-verified and tail recursive; if the host check per step costs, dispatch on `call_ref` inside `fast-step` |
| P1 (b) is too slow | measured on one host call with the 72 MB store | P1 (a) |

A headless session stops in the cases of plan.md "When a headless
session stops", read for this plan.

## 7. What stays trusted when V9 passes

ACL2 and SBCL; the translator and SpecTec (the semantics is the
specification by decision); the spec's decoder and instantiation as
implementations of the standard (they are the semantics, so not the
engine's to prove); for TeX with P1 (a), that the 18 host functions
are a function of their arguments and the store. Nothing else of the
engine.
