# V3: contexts

- Milestone: V3 (plan2.md: one entry, exit rules do not fire on a body that steps, the context lemma, `op-step` under any control stack)
- Date: 2026-11-17
- Repo commit: 4e6e5b0 plus this note's commit
- Status: final
- Feeds engine plan: V4 (`step-under-ctrl` lifts `exit-step` and `anyprefix-step`; `step-of-vals-exit-instr-rest` is "a block at `br` or `return` does not step"; the 24 rules of an administrative term are listed with the body each needs), V5 (the hypotheses of `op-step-simulates`; `machine-ok` changed), V6 (`machine-ok` changed)
- Incorporated in engine plan: yes (plan2.md V3, "Current state", §5 row 3)

## Summary

- **V3 is complete.** Two new books, `engine/rules/context.lisp` (4.3 s)
  and `engine/machine/op-context.lisp` (2.6 s), certify under
  `make -C engine check`. The gate has 27 books (25 before), no
  `skip-proofs`, no `defaxiom`, no trust tag.
- **The exit theorem certifies, for any control stack and every opcode
  with rules at once**:

  ```lisp
  (defthm op-step-simulates
    (implies (and (machine-ok s)
                  (not (admin-kind (car-t (ms-is s))))
                  (not (sym-member (entry-kind (car-t (ms-is s))) '(:trap :throw_ref)))
                  (equal (ms-status (op-step s)) :run))
             (equal (stepn 1 (machine-abs s))
                    (list (machine-abs (op-step s))))))
  ```

  The hypotheses are those of V2's `op-step-simulates-flat` without the
  empty control stack. Label, handler and frame entries are in one
  induction (64,282 prover steps for the theorem, 14,313 for the context
  lemma).
- **A machine bug was found and fixed** (plan2.md §5 row 3 happened, once).
  The machine entered a `HANDLER_` term whose catch clauses are not a true
  list; `Step/ctxt-handler` asks for a true list before it steps the body,
  so the specification does not step under such a term and the machine
  did, with clock 1. `enterable-p` and `entry-ok` now ask it (as they did
  for a label's continuation). No decoded module has such a term; the
  state was reachable only from a configuration built by hand (§6).
  `machine-ok`, a hypothesis of T1, is stronger by that conjunct.
- **Tests after the machine change** (§8): test 1, 0 disagreements in 10
  runs, every line equal to E6's; test 2, 32,707 commands with the same result and store,
  none with another result (24 where the machine's own fuel ended);
  lockstep, 0 disagreements in 8 runs; test 3, 32,659 commands with equal final states, 0
  different; slides, 7 of
  7 identical to V8.
- **For V4**: `step-under-ctrl` asks only that the innermost block steps
  and is not the body of an exit, so it lifts `exit-step` and
  `anyprefix-step` as it is. `step-of-vals-exit-instr-rest` is the fact
  V4 item 1 asks for `br` and `return`.

## Findings

All prover steps are from the certification output
(`data/v3-contexts/measure.txt`).

### 1. What stands before a context rule in `STEP`

On a list that is one administrative term, `STEP` tries `Step/pure` and
`Step/read` first. The machine's table has 24 rules whose redex is such
a term (7 for a label, 11 for a handler, 6 for a frame), all pure or
read, none among `STEP`'s own rules. So each of them must fail before
`Step/ctxt-label`, `-handler` or `-frame` is reached. Each needs a body
of one of four shapes:

| Body | Rules |
|---|---|
| values | `label-vals`, `handler-vals`, `frame-vals` |
| `TRAP` alone | `trap-label`, `trap-handler`, `trap-frame` |
| values, then `br`, `return` or `return_call_ref`, then anything | `br-label-zero`, `br-label-succ`, `br-handler`, `return-label`, `return-handler`, `return-frame`, `return_call_ref-label`, `return_call_ref-handler`, `return_call_ref-frame-null`, `return_call_ref-frame-addr` |
| an exception reference and `THROW_REF`, nothing else | `throw_ref-label`, `throw_ref-frame`, `throw_ref-handler-{empty,catch,catch_ref,catch_all,catch_all_ref,next}` |

`(exit-body-p b)` is the disjunction. The third row is `(exit-block-p b)`:
the first element of `b` that is not a value has head `BR`, `RETURN` or
`RETURN_CALL_REF`, **or** it has the head of a null or function reference
and `RETURN_CALL_REF` follows it. The second case is there because the
two `return_call_ref` rules of a frame match the reference before the
instruction by its head and never test `val-p`: a function reference
whose address is not a natural number is not a value, and nothing in the
rule's body excludes it. It is the same fact as for `call_ref` in
[V1-dispatch](V1-dispatch.md) §4.

### 2. Generated lemmas (`rules/context.lisp`)

| Family | Says | Count | Prover steps |
|---|---|---|---|
| `<search>-FAILS-WHEN-NOT-EXIT-BLOCK` | a search of one of the ten rules of row 3 fails on a list that is not `exit-block-p` | 10 of 10 | 4,317 to 52,018 |
| `<R>-FAILS-WHEN-NOT-EXIT-BODY` | rule `R` fails on `l` unless `(exit-body-p (cadddr (car l)))` | 24 of 24 | 4,127 to 7,842; 75,640 in all |

- Both end with a census that fails the book if a lemma is missing; the
  recorded set of missing lemmas is empty.
- The searches are proved by the induction of the search, with the search
  open. What they need about lists is forward chaining from the generated
  match functions (V1's `VALS-P-WHEN-<match>`): a value prefix matched in
  two pieces is a value prefix (`vals-p-of-take-from-two-parts`, for
  `br-label-zero` and `return-frame`, which split the values into those
  that stay and those that leave).
- `return_call_ref-frame-addr` has two searches, one inside the other.
  The inner one (`STEP_READ/SPLIT/SEARCH118`) is by hand: what it found
  (74,636 steps), then that the outer search calls it on prefixes of its
  own list.

### 3. A body that steps is not the body of an exit (V3 item 2)

```lisp
(defthm not-exit-body-p-when-block-steps      ; 2,009 steps
  (implies (and (vals-p v) (not (value-head-p (car i))) (true-listp r)
                (w3t::step (list :|%;%| z (append v (cons i r)))))
           (not (exit-body-p (append v (cons i r))))))
```

- Values alone: not this block (`i` is not a value). `TRAP` alone and an
  exception with `THROW_REF`: C3 of `rules/terminal.lisp`
  (`step-of-trap-alone`, `step-of-uncaught-exception`).
- `br`, `return`, `return_call_ref` first: new,
  `step-of-vals-exit-instr-rest` (449 steps): a block
  `v ++ (i) ++ r` with `(exit-head-p (car i))` does not step, for any
  number of values and any rest. No relation has a rule for these heads
  (V1's `<relation>-OF-VALS-INSTR-WITHOUT-RULE`), and `Step/ctxt-instrs`
  finds no step with fewer values, by the induction of V2
  (`no-step-below-when-exit-head`, 1,396 steps; V2's `no-step-below`,
  `flat-search` and their lemmas are used as they are).
- **The block is values, then an instruction whose head is not a
  value's.** This is the hypothesis that makes the lemma short: with it
  the reference case of `exit-block-p` cannot occur, and the element
  before `THROW_REF` is a value. It holds for the block of every machine
  state inside a control entry: `op-step` has an instruction with rules
  at the head, `anyprefix-step` a `TRAP` or `THROW_REF`, and one entry
  further out the head is an administrative term. Without it the lemma
  would need "a reference that is not a value, then `return_call_ref`,
  does not step", which no machine state needs.
- For an administrative term in the block no step is needed:
  `not-exit-body-p-of-vals-admin-term-rest` (194 steps).

### 4. One entry (V3 item 1)

- `step-of-admin-term-is-context-rule` (926 steps): on one term whose
  body is not `exit-body-p`, `STEP` is the three context rules. The pure
  and the read rules fail by §2 through V1's
  `<relation>-OF-REDEX-<head>`; `Step/ctxt-instrs` has no value before
  the term and no rest; `STEP` has no rule of its own for the head.
- `step/r-ctxt-{label,handler,frame}-of-stepping-body` (1,746, 1,746 and
  3,997 steps): what each context rule returns when the body steps, by
  `:expand` of the rule. **The `%SIZE` test was no difficulty** (plan2.md
  §5 row 2): after `%size-of-cons` it is linear arithmetic. V0's
  `%size-check-of-admin-body` is not used (its `nth` form never matches,
  as V2 found).
- `step-of-admin-term` (1,641) and `step-of-admin-term-in-block` (4,250):
  for `(admin-term k n x b)`, `k` one of `:l :h :f`, with values before
  and a rest after,

  ```
  STEP (s; f; v ++ ((k n x b)) ++ r) = (s'; f_out; v ++ ((k n x' b')) ++ r)
  ```

  where `(s'; f'; b')` is the step of `b` in frame `x` for a frame and in
  `f` otherwise; `f_out` is `f` for a frame and `f'` otherwise; `x'` is
  `f'` for a frame and `x` otherwise. With `v` or `r` not empty this is
  V2's `step-of-admin-term-in-flat-block`.

Hypotheses of `step-of-admin-term-in-block`: `k` is one of the three
kinds; `x` is a true list unless `k` is `:f` (the context rules of a
label and a handler test it); `b` is a true list and not `exit-body-p`;
`v` are values and `r` is a true list; the body steps, to a state of the
shape `(:|%;%| s' f')` (`Step/ctxt-frame` takes the state apart).

### 5. The context lemma and `op-step` (V3 items 3 and 4)

```lisp
(defthm step-under-ctrl                       ; 14,313 steps
  (implies (and (ctrl-ok ctrl) (true-listp b) (not (exit-body-p b))
                (w3t::step (list :|%;%| (list :|%;%| s fr) b))
                (state-shape-p (cadr (car (w3t::step (list :|%;%| (list :|%;%| s fr) b))))))
           (equal (w3t::step (list :|%;%| (list :|%;%| s (mv-nth 1 (abs-ctrl ctrl b fr)))
                                   (mv-nth 0 (abs-ctrl ctrl b fr))))
                  (let* ((inner (w3t::step (list :|%;%| (list :|%;%| s fr) b)))
                         (s2 (cadr (cadr (car inner))))
                         (fr2 (caddr (cadr (car inner))))
                         (b2 (caddr (car inner))))
                    (list (list :|%;%| (list :|%;%| s2 (mv-nth 1 (abs-ctrl ctrl b2 fr2)))
                                (mv-nth 0 (abs-ctrl ctrl b2 fr2))))))))
```

- By the induction of `abs-ctrl` (`abs-ctrl-induct`: the block and the
  frame one entry further out), with `abs-ctrl` closed and opened one
  entry at a time by `abs-ctrl-when-consp`. Each step is
  `step-of-admin-term-in-block` as a rewrite rule, and the next block is
  not `exit-body-p` because its first instruction is the term (§3).
- No hint but `:induct`.
- `op-step-simulates` (64,282 steps): from V2's
  `op-step-is-step-of-flat-block`, which says the block of the next state
  is the step of the block and that `ctrl` is unchanged, §3 for the block
  `rev(vals) ++ is`, and the context lemma. Four `:use` instances, no
  case split.

**Hypotheses** (of a lemma; no theorem of plan2.md §1 got one):

| Lemma | Hypothesis | Why |
|---|---|---|
| `step-under-ctrl` | `(not (exit-body-p b))` | an exit rule of the innermost entry fires before the context rule otherwise. Follows from "the block steps" for every block the machine has (§3) |
| `step-under-ctrl` | the step of `b` returns a state `(:|%;%| s' f')` | `Step/ctxt-frame` fails otherwise. `op-step-is-step-of-flat-block` gives the state in that form; in general it is V2's `step-own-state-shape` |
| `op-step-simulates` | head not `TRAP`, not `THROW_REF`, not administrative; `op-step` ends `:run` | as V2 ([V2-flat](V2-flat.md) §6) |

### 6. The machine bug

`Step/ctxt-handler` tests `(true-listp catch*)` before it steps the body,
as `Step/ctxt-label` tests the continuation. `enterable-p` asked a true
list of a label's continuation only. Seen when the hypotheses of §4 were
written down against `entry-ok`; then run:

```
c = (:|%;%| (:|%;%| st fr) ((:handler_%{%}% 0 5 ((:nop)))))
(w3t::step c)                         = nil
(machine-ok (ms-of-config c))         = t
machine: enters the term (clock 0), then nop (clock 1, status :run)
```

So C2 was false for a state with `machine-ok`: the machine made a step
the specification does not make. The run cannot end in a result (every
rule that leaves a handler tests the same list, so the machine ends
`:stuck`), which is why T1 would not have been false, and why no test
found it: no decoded module has such a term. But C2 is stated for every
running state with `machine-ok`.

Fix, in `machine/machine.lisp` and `machine/ok.lisp`: `enterable-p` and
`entry-ok` ask a true list for the third component unless the term is a
frame. The fast machine calls the same `enterable-p`. One old proof
changed: `enter-step-keeps-abs` in `clock0.lisp` split on
`(enterable-p ...)` with the definition open, and its checkpoint after
the change was

```
(IMPLIES (AND (NOT (EQUAL (ENTRY-KIND (CAR (MS-IS S))) :FRAME_%{%}%))
              (NOT (TRUE-LISTP (ENTRY-X (CAR (MS-IS S)))))
              (CONSP (MS-IS S)))
         (EQUAL (MS-STORE (ENTER-STEP S)) (MS-STORE S)))
```

The hint now disables `enterable-p`, so that the two cases are the two
lemmas written for them. No other old proof changed; times in §8.

### 7. What failed first

- **A block of all the values is not `operands`.**
  `flat-search-of-exit-instr` at `k = 0`:

  ```
  (IMPLIES (AND (VALS-P VALS) (EXIT-HEAD-P (CAR I)) (CONSP R)
                (W3T::STEP (LIST :|%;%| Z (APPEND (REVAPPEND VALS NIL) (LIST I)))))
           (NOT (LIST (LIST :|%;%| ...))))
  ```

  `nthcdr 0` is rewritten away and `(revappend vals nil)` is not
  `(operands (len vals) vals)` to the rewriter. A lemma for that form
  (`step-of-rev-vals-exit-instr`), as in [V2-flat](V2-flat.md) §7.
- **A disjunction in the hypothesis of a search lemma.** With
  `exit-block-p` open, "the search fails unless the first instruction is
  `br` ..., or a reference then `return_call_ref`" failed for all nine
  searches, also for those that had proved with the first disjunct alone
  (`STEP_PURE/SEARCH65`):

  ```
  (IMPLIES (AND ... (W3T::STEP_PURE/MATCH59 (TAKE (+ -1 K) L))
                (EQUAL (CAR (NTH (+ -1 K) L)) :BR) ...
                (EQUAL (CAR (NTH (FIRST-NONVAL L) L)) :REF.FUNC_ADDR)
                (NOT (EQUAL (CAR (NTH (FIRST-NONVAL L) (CDR L))) :RETURN_CALL_REF)))
           (NOT (CONSP (CDR (NTH (+ -1 K) L)))))
  ```

  `(first-nonval l)` is not rewritten inside the split hypothesis. What
  works: `exit-block-p` closed, and two rewrite rules that conclude it
  from a value prefix (`exit-block-p-when-vals-then-exit-instr`,
  `-then-reference`); the free variable `k` is bound by the
  forward-chained `(vals-p (take k l))`.
- **`append` opened by a case split on the values.** The first proof of
  §3 enabled `exit-block-p` and `value-head-p` and used
  `step-of-exn-throw` on the block; `(car (append v ...))` split on
  `(consp v)`, `append` opened, and the rules stated for
  `(append v (cons i r))` no longer matched (checkpoint `Subgoal 15'`, a
  goal about `(first-nonval (cons (car v) (append (cdr v) (cons i r))))`).
  Now three lemmas, each about the closed form
  (`exit-block-p-of-vals-instr-rest`, `val-p-of-car-when-exn-throw-p`,
  then the theorem with `car-of-append` disabled).
- **A rewrite rule whose hypothesis is an equation with free variables.**
  `step-of-admin-term` was first stated with
  `(equal (w3t::step (... (if (equal k :f) x f) ...)) (list (list :|%;%| (list :|%;%| s2 f2) b2)))`.
  It did not fire:

  ```
  (IMPLIES (AND (TRUE-LISTP X) (TRUE-LISTP B) (NOT (EXIT-BODY-P B))
                (EQUAL (W3T::STEP (LIST :|%;%| (LIST :|%;%| S F) B))
                       (LIST (LIST :|%;%| (LIST :|%;%| S2 F2) B2))))
           (EQUAL (W3T::STEP (LIST :|%;%| (LIST :|%;%| S F) (LIST (ADMIN-TERM :L N X B))))
                  (LIST (LIST :|%;%| (LIST :|%;%| S2 F2) (LIST (ADMIN-TERM :L N X B2))))))
  ```

  The free variables are matched against the hypothesis as it is written,
  with `(if (equal :l :f) x f)` not yet `f`. And in the induction of the
  context lemma, stated the same way, the equation in the hypotheses was
  not used to replace the step of the block (checkpoint
  `Subgoal *1/2.1`: the induction hypothesis's own premise, the step of
  the next block, was left unproved). Both are now stated as V2 states
  `step-of-flat-block`: the inner step is bound by
  `(equal inner (w3t::step ...))` and the result is written with its
  components. The proof of `step-of-admin-term` went from 133,994 prover
  steps (three `:use` instances) to 1,641 (no hint but the definition of
  `admin-term`).
- **A rule that rewrites what another rule's hypothesis names.**
  `car-of-admin-term` (the head as a `case` on the kind) fired inside
  `(member-equal (car (admin-term ...)) *admin-heads*)` before the lemma
  for that term could. The book has only the second,
  `admin-head-of-admin-term`.
- No failed checkpoint but the one of §6 was a state the machine can
  reach.

### 8. Gate and tests

`make -C engine check` after the change of `machine.lisp`, every engine
book certified again (`data/v3-contexts/gate.txt`):
`engine: no skip-proofs, no defaxiom in 27 book(s)`. Times of the books
that are new or whose source changed:

| Book | Before (s) | After (s) |
|---|---|---|
| `machine/machine` | 2.9 | 2.6 |
| `machine/ok` | 18.8 | 20.2 |
| `machine/clock0` | 3.8 | 3.6 |
| `lib/lists` | 2.5 | 2.4 |
| `rules/context` | new | 4.3 |
| `machine/op-context` | new | 2.6 |

("Before" from [V0-ground](V0-ground.md) §6.) The `fast/` books certify
with no change to their source; their times are in `gate.txt`.

Tests, all with the machine after the fix. No module in them is outside
what the tests covered before; none of them is a claim about the proved
subset (plan.md D8), they compare machines.

| Test | Run | Result |
|---|---|---|
| 1, list machine against the spec at every step | `machine/difftest-run.lsp`, `data/v3-contexts/difftest1.out` | 10 runs, 0 disagreements; every line equal to E6's |
| 2, list machine against the spec over spec-test-3 | `machine/difftest2-all.sh`, 6 jobs, 900 s; `data/v3-contexts/difftest2/` | 32,707 commands same result and same store; 24,728 `:unsupported` (outside D5); 11 not invocations; 24 printed as different, all of them the machine out of its 2,000,000 steps with the same store where the spec finishes (see below); 250 scripts finished, 8 stopped at 900 s |
| lockstep, fast machine against list machine | `fast/fasttest-run.lsp`, `data/v3-contexts/fasttest.out` | 8 lockstep runs, 0 disagreements; 6 whole runs with equal final states |
| 3, fast machine against list machine over spec-test-3 | `fast/difftest3-all.sh`, 8 jobs, 900 s; `data/v3-contexts/difftest3/` | 32,659 commands with equal final states, 24,726 `:unsupported` on both machines in equal states, 13 out of fuel on both in equal states, 11 not invocations, **0 different**; 251 scripts finished, the same 7 stopped at 900 s as in E7 (which had 32,649 equal) |
| slides | `make -C engine slides` | 7 of 7 identical to V8 |

### 9. Practice (step2.md), where the books depart from it

- `rules/context.lisp` has 9 `:use`, 5 `:cases`, 9 `:expand`;
  `machine/op-context.lisp` has 1 hint with `:use` (four instances) and 1
  `:expand`. No `"Subgoal"` hint. The `:use` hints are instances of
  lemmas with `:rule-classes nil` (`not-exit-body-p-when-block-steps`
  has the free `z`) and of V2's `no-step-below` lemmas at
  `(+ 1 (len vals))`.
- `admin-term` (defined in `machine.lisp`, an old book) is disabled in
  the header of the two new books, not at the end of its defining book:
  old proofs open it.
- `engine/lib/lists.lisp` got two rules: `revappend-of-revappend-nil`,
  `nth-when-too-large`. The books that include it certify unchanged.
- One line was added to the proof practice of step2.md, from §7: a lemma
  that depends on another step names that step by its components.

Test 2 against E6's run (33,113 same, 2 different, 45 `:spec-fuel`,
256 scripts finished): the driver's spec fuel was raised from 200,000 to
20,000,000 steps on 2026-11-16 (commit 6b90823), the machine's stayed at
2,000,000 machine steps. So no command is `:spec-fuel` now, and 24
commands of the `memory_fill`, `memory_copy` and `memory_grow` scripts
(loops over 65,536 addresses) end with the spec's result on one side and
`:FUEL` on the machine's: the comparison prints them as different. None
has a machine result that differs from the spec's. The two differences
of E6 were in `call_indirect`, which did not finish in 900 s this time;
more scripts stop at the time limit (8 against 2) because the spec now
runs longer per command and the gate was certifying at the same time.
The fix cannot change a run of a decoded module (it concerns a term no
decoder builds); this run shows no new disagreement, not more.

## Open questions

- V4's `exit-step` needs, for each of the 24 rules, what it returns
  (`*instrs-not-yet*` of `rules/flat.lisp` lists the 12 that return what
  a search found) and that it is the first of its place to fire as the
  machine's `try-rules` has it. V1's `try-rules-of-{pure,read}-rules`
  cover the three administrative heads; the pure exits come before every
  context rule, so the context rule does not have to fail first, unlike
  what plan2.md V4 item 1 says for rules "after the context rules":
  there are none (§1).
- `step-under-ctrl` asks the state shape of the inner step. For
  `anyprefix-step` (pure and read rules) the state is unchanged, so the
  shape is that of the state before.

## Data

All under `data/v3-contexts/`.

- `measure.sh`: reads the generator lines, the census lines, the prover
  steps of the named theorems, the certification times and the hint
  counts. `measure.txt`: its output. Regenerate at the repository root,
  inside `nix develop`, after `make -C engine check`:
  `sh plan/wasm-engine/notes/data/v3-contexts/measure.sh > plan/wasm-engine/notes/data/v3-contexts/measure.txt`.
- `gate.txt`: the lines of `make -C engine check` that name a book or the
  result.
- `handler-bug.lsp` and `handler-bug.out`: the configuration of §6 on the
  machine before the fix (commit 4e6e5b0) and after.
- `difftest1.out`; `difftest2/SUMMARY` and `difftest2/D2-LINES.txt.gz`;
  `fasttest.out`; `difftest3/per-command.txt` and
  `difftest3/D3-LINES.txt.gz`.
