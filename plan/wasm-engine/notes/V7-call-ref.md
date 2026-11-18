# V7: `call_ref` on the fast machine; T2 as stated

- Milestone: V7 (plan2.md: the fast machine stops at a host `call_ref`, the place lemma of `call_ref`, `no-call-ref-run` removed, the `*-not-yet*` constants settled)
- Date: 2026-11-18
- Repo commit: 9c100a0 plus this note's commit
- Status: final
- Feeds engine plan: V8 (`engine-run`; the TeX driver's loop can resume `fast-run` after each `:unsupported` stop at a host call, §6), V9 (T2 is the second statement `top.lisp` restates; the check of the `*-not-yet*` constants is the last event of `fast/call-ref.lisp`, §5), V7b (not started; nothing here depends on it)
- Incorporated in engine plan: yes (plan2.md V7, "Current state")

## Summary

- **V7 is complete. T2 certifies as plan2.md §1 states it**, with no
  hypothesis about an instruction:

  ```lisp
  (defthm fast-result-is-spec-result              ; fast/spec-result.lisp, 2,454 prover steps
    (implies (and (fm-inv fm)
                  (fast-result-p (fast-run n fm))
                  (natp fuel)
                  (< (fast-clocks n fm) fuel))
             (equal (w3t::steps/%fuel fuel (machine-abs (fm->ms fm)))
                    (list (machine-abs (fm->ms (fast-run n fm)))))))
  ```

  `no-call-ref-run` is deleted; no engine book mentions it. F2 and F3 of
  plan2.md §1 are met.
- **The fast machine changed** (P1 as decided): `fast-step` stops
  `:unsupported` when the head is `call_ref` and the top of the operand
  stack is a reference to a host function (`host-ref-p`, new in
  `fast.lisp`). One `cond` clause, before the last one. The list machine
  did not change.
- One new book, `engine/fast/call-ref.lisp` (2.8 s, 29 theorems, largest
  proof 112,302 prover steps). The gate certifies 34 books (33 before),
  no `skip-proofs`, no `defaxiom`, no trust tag.
- **No old proof changed.** `refine.lisp`, `refine-mem.lisp`,
  `refine-step.lisp`, `refine-hot.lisp` and `refine-op.lisp` were
  certified again as they are, because `fast.lisp` changed (136 s, 40 s,
  339 s, 3 s, 7 s). `refine-step.lisp` and `refine-op.lisp` were not
  edited.
- **The step theorem without the exclusion** is a new theorem,
  `fast-step-is-machine-step` (`call-ref.lisp`), not a change of
  `fast-step-refines`: that one stays in `refine-op.lisp` with its
  `call_ref` hypothesis and is used for every other head (§3).
- **The two host rules stay without a (U) lemma**, and that is settled:
  `*fallback-not-yet*`, `*u-not-yet*` and `*places-not-yet*` keep their
  values, the last event of `call-ref.lisp` fails unless they are exactly
  the two host rules and the place `(:op :call_ref)`, and two theorems
  say that no host rule fires in a step of the fast machine (§5).
- **Tests after the change** (§7; none is a claim about the proved
  subset, they compare machines): lockstep, 8 runs, 0 disagreements,
  every line equal to V4's; test 3, 32,659 commands with equal final
  states and 0 different, but no command of the suite reaches a host
  call, so the new clause is tested by a theorem and one hand-made state
  (§7); the slides 7 of 7 identical
  to V8, and **inside T2** now (S0 only, inside D5; hypotheses checked on
  each of 12 runs); TeX on `input.tex` (outside the proved subset: host
  calls, P1) the same 860 bytes of DVI in the same 55,065,266 steps.
- No failed checkpoint was a state of the machine (§8).

## Findings

All prover steps are from the certification output
(`data/v7-call-ref/measure.txt`, every `defthm` of the three books).

### 1. The change of the machine

```lisp
(defun host-ref-p (ref store)             ; fast.lisp, guard t
  (and (eq (entry-kind ref) :ref.func_addr)
       (eq (entry-kind (wrt::%get-field (nth-t (entry-n ref) (wrt::%get-field store :funcs)) :code))
           :_hostfunc)))

; in FAST-STEP, the clause before the last:
((and (eq (entry-kind i) :call_ref) (host-ref-p (car-t vals) (fm-store fm)))
 (update-fm-status :unsupported fm))
```

- The test is the one the two host rules make (`Step/call_ref-hostfunc-res`
  and `-div`): the redex ends `(ref.func_addr a) (call_ref y)` and the
  code of function `a` is `(:_hostfunc hf)`. It reads the fast store; the
  functions of the full store are the same
  (`host-ref-p-of-put-mem0-bytes`).
- It is not the TeX driver's test (a vector of host addresses filled by
  the driver), but it agrees with it on TeX's store, by reading `texrun.lisp` (not run): the
  driver gives each host function the code `(:_hostfunc name)`. The driver tests
  before it calls `fast-step`, so this clause never fires in a TeX run;
  the driver did not change.
- The clause is in `fast-step`, not in `fast-op-step` or
  `fast-apply-rule`: those two are opened by the proofs of
  `refine-hot.lisp`, `refine-op.lisp` and the 212 (U) lemmas of
  `refine-step.lisp`. `fast-step` is opened by `fast-step-refines` only,
  under "the head is not `call_ref`", where the new clause is false at
  once: 132,297 prover steps after the change.
- Cost: one `eq` on the general path (not on the six hot instructions,
  not on a value). Not measured apart; the slides' times are in §7.
- At a `call_ref` whose reference is not a host function the machine
  goes on as before: the place function `fast-try-op-call_ref` tries the
  four rules in `STEP`'s order. The host rules are still in that chain
  (the generated dispatch did not change); they fail there (§5).

### 2. What is proved about `call_ref` (`call-ref.lisp`)

| Section | Statements | Largest proof |
|---|---|---|
| 1. A host rule fails unless the reference is a host function | `step/r-call_ref-hostfunc-{res,div}-fails-when-not-host-ref`, `apply-rule-of-host-rule-when-not-host-ref`, `host-ref-p-of-put-mem0-bytes` | 3,396 |
| 2. (U) for a rule of the fallback that does not fire on the full store | `u-holds-when-fallback-rule-fails`, `u-holds-of-host-rule-when-not-host-ref` | 15,602 |
| 3. The place `(:op :call_ref)` | `fast-try-op-call_ref-is-try-rules`, `all-u-holds-of-call_ref`, `fast-try-op-is-try-rules-for-any-op`, `all-u-holds-of-any-op` | 10,110 |
| 4. The reference of the op step's redex is the top of the stack | `redex-ref-of-op-redex`, `redex-arity-of-call_ref-is-positive` | 653 |
| 5. The op step at `call_ref` | `fast-op-step-refines-call_ref` | 112,302 |
| 6. The step | `fast-step-at-call_ref`, `machine-step-at-call_ref`, `fast-step-refines-call_ref`, `fast-step-is-machine-step` | 25,617 |
| 7. No host rule fires | `fast-step-refuses-host-call`, `host-rule-fails-on-op-redex` | 1,185 |
| 8. The recorded gaps | one `make-event` | |

- `redex-ref l` is the last element but one of `l`
  (`(car (nthcdr (- (len l) 2) l))`), the term the two rules test.
- **Why (U) holds for a host rule without a fact about the hook.** (U)
  (`u-holds`, `refine-step.lisp`) compares `apply-rule` on the full store
  with `fast-apply-rule` on the fast store. A host rule takes the
  fallback, which runs `apply-rule` on the full store. If that does not
  fire, the fallback returns "not fired" with the stobj as it was, which
  is (U). `u-holds-when-fallback-rule-fails` says this for any rule of
  the fallback; it needs neither `<rule>-FAILS-PLAINLY` nor
  `-NEEDS-ITS-OPCODE` (`*fallback-not-yet*`), which is what the deferred
  item of V7 was going to state about the hook. So `$hostcall` stays
  closed in every proof.
- **The place lemma** has the hypothesis
  `(not (host-ref-p (redex-ref redex) s))`; with it all four rules have
  (U): `call_ref-null` and `call_ref-func` by their `-U-HOLDS` lemmas of
  `refine-step.lisp`. "The generated place function is `fast-try-rules`
  on the place's rules" has no hypothesis and is proved with the hints of
  the generator of `refine-step.lisp` (10,110 steps); it was missing only
  because the generator proves it in one event with the unconditional
  (U) of the place.
- `fast-op-step-refines-call_ref` is the proof of `fast-op-step-refines`
  with the same `:use` of `fast-try-rules-refines`.

### 3. The step theorem and what changed above it

```lisp
(defthm fast-step-is-machine-step                ; call-ref.lisp, 2,819
  (implies (and (fmp fm) (fast-inv-store (fm-store fm)) (ctrl-kinds-ok (fm-ctrl fm))
                (not (equal (fm-status (fast-step fm)) :unsupported)))
           (equal (fm->ms (fast-step fm)) (machine-step (fm->ms fm)))))
```

By cases on the head: not `call_ref`, `fast-step-refines`; `call_ref`,
`fast-step-refines-call_ref` (a host reference makes the step
`:unsupported`, against the hypothesis).

Plan2.md V7 item 4 says the hypothesis "is removed from
`fast-step-refines`". It is not removed there: the guideline of
step2.md forbids a new lemma or a changed statement in
`refine-op.lisp`. The theorem without it has the new name above, and
`inv.lisp` uses it in place of `fast-step-refines`.

`inv.lisp` (9.3 s, 9.1 s in V6):

- the hypothesis `(not (equal (entry-kind (car (fm-is fm))) :call_ref))`
  is gone from `fast-op-step-keeps-fmp`, `fast-op-step-keeps-inv-store`,
  `fast-step-keeps-fmp`, `fast-step-keeps-inv-store`,
  `machine-ok-of-fast-step`, `fast-step-keeps-fm-inv` and
  `fm->ms-of-fast-step`; no hint changed but the name of the step
  theorem. The first two needed only
  `fast-try-op-is-try-rules-for-any-op`, as [V6-inv](V6-inv.md) §7 said;
- `no-call-ref-run` and `no-call-ref-run-when-running` are deleted, and
  the hypothesis is gone from `fast-run-is-machine-run-when-supported`,
  `fast-run-is-machine-run` and `fast-run-keeps-fm-inv`;
- `entry-kind-when-hot` is deleted (unused); `fast-step-when-not-running`
  moved to `call-ref.lisp`.

`spec-result.lisp`: the hypothesis is gone from
`machine-result-p-of-machine-run-of-fm->ms` and from T2.

### 4. The hypotheses of T2 now

`(fm-inv fm)`, `(fast-result-p (fast-run n fm))`, `(natp fuel)`,
`(< (fast-clocks n fm) fuel)`: those of plan2.md §1 and no other. The
lemmas under it keep "the step (the run) does not end `:unsupported`";
a run that ends with a result did not.

What `:unsupported` covers after V7: an opcode without rules or outside
`redex-arity`, a fallback result the fast machine cannot hold
(`fallback-shape-ok`), a store write the fast path refuses, and a
`call_ref` of a host function. None is a result, so T2 says nothing of
such a run. For a module with host functions this means: T2 covers a run
up to its first host call only if the run ends before one. TeX is such a
module and stays outside (P1, plan.md D8).

### 5. The `*-not-yet*` constants: settled

| Constant | Book | Value after V7 | Why it is settled |
|---|---|---|---|
| `*fallback-not-yet*` | `refine.lisp` | the two host rules | their `-FAILS-PLAINLY` fact is not needed (§2) |
| `*u-not-yet*` | `refine-step.lisp` | the two host rules | (U) holds for them where the fast machine reaches them (`u-holds-of-host-rule-when-not-host-ref`) |
| `*places-not-yet*` | `refine-step.lisp` | `((:op :call_ref))` | the place has its lemma under "not a host reference" (`all-u-holds-of-call_ref`) |
| `*frame-not-yet*` | `frame.lisp` | unchanged | not V7's: those rules take the fallback, which is proved exact (V7b) |

The last event of `call-ref.lisp` fails certification unless the first
three are exactly these. The checks in the two old books did not change.

"A theorem that the fast machine does not apply them" (plan2.md V7, last
item) is two theorems, because the machine does call the host rules at a
`call_ref` that is not a host call (they are in the generated chain,
after `call_ref-null` and `call_ref-func`); what is true is that they do
not fire:

```lisp
(defthm fast-step-refuses-host-call               ; 1,185
  (implies (and (equal (fm-status fm) :run)
                (equal (entry-kind (car (fm-is fm))) :call_ref)
                (host-ref-p (car (fm-vals fm)) (fm-store fm)))
           (equal (fm-status (fast-step fm)) :unsupported)))

(defthm host-rule-fails-on-op-redex               ; 292
  (implies (and (sym-member fn *host-rules*)
                (fast-inv-store s)
                (not (host-ref-p (car vals) s))
                (natp k) (< 0 k) (<= k (len vals)))
           (not (car (apply-rule fn (list :|%;%| (put-mem0-bytes s b) f)
                                 (rev-onto (take-n k vals) (list i)))))))
```

The second is about the redex `fast-op-step` builds (`k` is
`redex-arity`, positive at `call_ref`:
`redex-arity-of-call_ref-is-positive`; with fewer than `k` values the
machine is `:stuck` and tries no rule) and about the store of the list
machine. So the list machine does not fire a host rule either in a step
that the fast machine does not refuse.

### 6. For V8

- The slides driver needs nothing more from V7: its runs meet T2's
  hypotheses (§7).
- TeX with P1: `fast-run` now stops `:unsupported` at each host call
  with the stobj as it was (`fast-step` only sets the status), so the
  driver can call `fast-run`, make the host step, set the status back to
  `:run` and call `fast-run` again. Each stretch between host calls is
  then a `fast-run` that ends `:unsupported`, which T2 does not cover
  (its hypothesis is a result); what covers a stretch is
  `fast-run-is-machine-run` and `fast-run-keeps-fm-inv`, which ask "does
  not end `:unsupported`". V8 has to state what it claims for a stretch:
  a run lemma for `n` steps that stops before the refused step would do
  it. This is an open point for V8 item 3, not a gap of T2.
- The driver's own test for a host call and `host-ref-p` agree on TeX's
  store (§1); V8 can replace the first by the second.

### 7. Tests

The machine changed, so the tests plan2.md names for V7 were run again,
and the slides. None is a claim about the proved subset except the
slides line.

| Test | Run | Result |
|---|---|---|
| lockstep, fast machine against list machine | `fast/fasttest-run.lsp`, `data/v7-call-ref/fasttest.out` | 8 lockstep runs, 0 disagreements, every line equal to V4's; 6 whole runs with equal final states |
| 3, fast machine against list machine over spec-test-3 | `fast/difftest3-all.sh`, 8 jobs, 900 s; `data/v7-call-ref/difftest3/` | 32,659 commands with equal final states, 24,726 `:unsupported` on both machines in equal states, 13 out of fuel on both in equal states, 11 not invocations, **0 different, 0 `:host-refused`**; 251 scripts finished, the same 7 stopped at 900 s as in V4, V3 and E7 (one full run, 26 min 55 s) |
| slides (S0 only, inside D5; **inside T2**) | `make -C engine slides`, `data/v7-call-ref/slides-fast.txt` | 12 runs, `config-shape T fm-inv T result T` on each; 7 of 7 identical to V8; 134 to 436 ms per slide on the lines kept (test 3 was running on the same machine) |
| TeX, `input.tex` (outside the proved subset: host calls) | `sh engine/tex/run.sh` | `:DONE` after 55,065,266 steps, 3,717 host calls, 0 fallbacks; `out.dvi` 860 bytes, identical to the file of the run before the change. 23.5 s with test 3 running beside it, so no rate is claimed |

Test 3 has a new class. `difftest3-one.lsp` counted a command as
different whenever the final states differ. A command that calls a host
function (the suite's `spectest` imports) now ends `:unsupported` on the
fast machine and with a result on the list machine. Such a command is
counted `:host-refused` when the lockstep walk finds the first
difference at a `call_ref` whose reference is `host-ref-p` in the list
machine's store, with the fast machine `:unsupported` there: the two
agreed at every step before. Any other difference is still `:differ`.

**No command of the suite reached a host call on the fast machine**
(0 `:host-refused`): the class is there so that a refusal is not
counted as a difference, and this run did not use it. So test 3 shows
that the change breaks nothing (32,659 equal, V3's number; V4 had
32,648 with one more script stopped), and does not test the new clause.
What tests it:

- the theorem `fast-step-refuses-host-call` (§5);
- `data/v7-call-ref/host-refusal.lsp`, a state made by hand with
  `call_ref` at the head and a reference to a function whose code is
  `(:_hostfunc "print")`: `fast-step` gives `:unsupported` and
  `fm->ms` of the result is the state with that status and nothing else
  changed; with a reference to a wasm function in the same store,
  `host-ref-p` is `nil` and the step is not refused
  (`host-refusal.out`).

The slides' caption (`slides/check.mjs`) now reads "inside the proved
subset: theorem T2 (fast-result-is-spec-result) holds for all 12 runs,
hypotheses checked at run time". Of T2's hypotheses the driver checks
`fm-inv` of the loaded stobj and the result; `config-shape-p` of the
configuration is the hypothesis of the loader lemmas that make `fm-inv`
a theorem (V8 composes them into T3). The fuel hypothesis is "some fuel
above `fast-clocks`", which exists for every run.

### 8. What failed on the way

None of these is a state of the machine.

| Attempt | What happened | What was done |
|---|---|---|
| `redex-ref` with the guard `(true-listp redex)` | guard conjecture `(<= 0 (+ -2 (len redex)))`, false for a short list | no guard: the function is used in statements only |
| `nthcdr-of-len-of-rev-onto` by induction on `rev-onto` | checkpoint `(nthcdr (len (cdr x)) (cdr (rev-onto (cdr x) (cons (car x) acc))))`: the induction hypothesis is about `nthcdr (len (cdr x))` of the list, not of its `cdr` | generalized to `(nthcdr (+ n (len x)) (rev-onto x acc))` with its own induction scheme (`rev-onto-count-induct`); the first is an instance |
| the host rules fail, with `car-t` open | checkpoint with `(not (consp (drop-n 1 (car (nthcdr ...)))))`: `entry-n` opened to a case on `drop-n` | `car-t` closed; `car-t-is-car` and `car-drop-n-is-cadr` of `refine-op.lisp` rewrite it |
| `redex-ref-of-op-redex-when-enough-operands` in the book | checkpoint `(redex-ref (rev-onto (take-n (+ -1 k) (cdr vals)) (list (car vals) i)))`: `take-n-open` and `rev-onto-cons` of `refine-hot.lisp` rewrote the redex before the lemma about it could match | both disabled in the book's (local) theory |
| `inv.lisp` after including the book | `fast-inv-store-of-put-mem0-bytes-nil` failed at `(put-mem0-bytes (put-mem0-bytes s nil) nil)`: the book's theory block had disabled `put-mem0-bytes` for the books above | the theory block of `call-ref.lisp` is `local` |

The last row is a departure from practices.md ("a definition is disabled
in the defining book"): `call-ref.lisp` closes definitions of older books
for its own proofs only, since `inv.lisp` was written against the theory
those books export.

## Open questions

- What V8 claims for a stretch of a TeX run between two host calls (§6).
- The host rules are still called by `fast-try-op-call_ref` when
  `call_ref-null` and `call_ref-func` fail (an ill-typed state, where
  both machines are then `:stuck`); each call copies the memory into the
  store (the fallback). It cannot happen in a validated module. Removing
  them from the chain would change the generator of `fast.lisp` and the
  place lemmas of `refine-step.lisp`.

## Data

`engine/fast/call-ref.lisp` (new), `engine/fast/fast.lisp` (`host-ref-p`,
one clause of `fast-step`), `engine/fast/inv.lisp`,
`engine/fast/spec-result.lisp`, `engine/fast/difftest3-one.lsp` (the
class `:host-refused`), `engine/slides/render.lsp`,
`engine/slides/check.mjs`; `data/v7-call-ref/`: `measure.sh`,
`measure.txt` (prover steps of every theorem, times, hints,
certificates), `gate-machine-change.txt` (the gate after the change of
`fast.lisp` alone, before any other edit: 33 books), `gate.txt`
(`make -C engine check`, 34 books), `fasttest.out`, `slides-fast.txt`,
`difftest3/` (`per-command.txt`, `D3-LINES.txt.gz`, `NAMES`),
`host-refusal.lsp`, `host-refusal.out`.
