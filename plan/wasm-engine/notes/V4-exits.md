# V4: exits and propagation

- Milestone: V4 (plan2.md: `exit-step`, `anyprefix-step`, `THROW_REF-NULL`, each lifted by the context lemma)
- Date: 2026-11-18
- Repo commit: f8c3d9f plus this note's commit
- Status: final
- Feeds engine plan: V5 (C2 holds for every clock-1 case of `machine-step`; the hypotheses of the four step theorems are what `machine-step` tests; every pure and read rule returns a true list), V6 (`fast-step` changed in the same line as `machine-step`), V10 if P2 says yes (the machine is no longer stuck at `throw_ref` under a null reference)
- Incorporated in engine plan: yes (plan2.md V4, "Current state", §5 row 3)

## Summary

- **V4 is complete.** Two new books, `engine/rules/exits.lisp` (2.9 s)
  and `engine/machine/exit-steps.lisp` (2.4 s), certify under
  `make -C engine check`. The gate has 29 books (27 before), no
  `skip-proofs`, no `defaxiom`, no trust tag.
- **The two exit theorems certify, and the third item**:

  ```lisp
  (defthm exit-step-simulates                    ; 43,762 prover steps
    (implies (and (machine-ok s)
                  (consp (ms-ctrl s))
                  (equal (ms-status (exit-step s)) :run))
             (equal (stepn 1 (machine-abs s))
                    (list (machine-abs (exit-step s))))))

  (defthm anyprefix-step-simulates               ; 93,769
    (implies (and (machine-ok s)
                  (sym-member (entry-kind (car-t (ms-is s))) '(:trap :throw_ref))
                  (equal (ms-status (anyprefix-step s)) :run))
             (equal (stepn 1 (machine-abs s))
                    (list (machine-abs (anyprefix-step s))))))

  (defthm op-step-simulates-throw_ref-null       ; 69,546
    (implies (and (machine-ok s)
                  (equal (entry-kind (car-t (ms-is s))) :throw_ref)
                  (equal (entry-kind (car-t (ms-vals s))) :ref.null_addr)
                  (equal (ms-status (op-step s)) :run))
             (equal (stepn 1 (machine-abs s))
                    (list (machine-abs (op-step s))))))
  ```

  With V3's `op-step-simulates` these are C2 for every clock-1 case of
  `machine-step` (§5). No theorem of plan2.md §1 got a hypothesis and
  `machine-ok` did not change.
- **`exit-step` needs nothing about the block inside the entry.** All 24
  rules of an administrative term are pure or read rules, and `STEP`
  tries `Step/pure` and `Step/read` before every context rule. So a rule
  of the term that fires is `STEP`'s, whatever the body is: the facts
  plan2.md V4 item 1 lists ("`vals ++ (br l) ++ r` does not step", ...)
  are not used. They stay proved (V3) for the stuck direction (V10).
- **A machine bug was found and fixed** (§6). `machine-step` and
  `fast-step` gave `throw_ref` to `op-step` when the top of the operand
  stack had the head `:ref.null`. No value has that head: a null
  reference is `(:ref.null_addr)`, which is what the rule
  `Step_read/throw_ref-null` matches. So the machine never applied the
  rule and ended `:stuck` where the specification steps to `TRAP`. C2 was
  not false (a stuck machine claims nothing) and no theorem was; V4
  item 3 would have been a theorem about a case that cannot occur. The
  test is now `:ref.null_addr` in both machines.
- **Every pure and every read rule now has its "returns a true list"
  lemma**: 182 of 182 (170 in V2). `*instrs-not-yet*` of
  `rules/flat.lisp` is covered by `rules/exits.lisp`, whose census has an
  empty recorded set.
- **Tests after the machine change** (§8): test 1, 0 disagreements
  in 10 runs, every line equal to V3's; test 2, 32,706 commands with the
  same result and store, none with another result (24 where the
  machine's own fuel ended); lockstep, 0 disagreements in 8 runs; test 3,
  32,648 commands with equal final states, 0 different; slides, 7 of 7
  identical to V8.

## Findings

All prover steps are from the certification output
(`data/v4-exits/measure.txt`).

### 1. What the 12 rules return

`Step/pure` and `Step/read` fire only if the instructions their relation
returns are a true list. `anyprefix-step` tests it at run time;
`exit-step` does not. So C2 for `exit-step` needs the fact for the rules
of an administrative term, and V2 had left 12 rules without it: those
that return what a search found.

| Family | Says | Count | Prover steps |
|---|---|---|---|
| `<search>-INSTRS-TRUE-LISTP` | `(true-listp (car (<search> ...)))` | 13 searches (10 generated, 3 by hand) | 2,326 to 10,427 |
| `<R>-INSTRS-TRUE-LISTP` | `(true-listp (car (R ...)))` | 12 of 12 | 50 to 404 |

- By hand: `STEP_PURE/SEARCH51` (`br-label-zero`) returns
  `val^n ++ instr'*`, where `instr'*` is the label's continuation, an
  argument of the search that the rule has tested: the lemma has the
  hypothesis `(true-listp instrs)`. `STEP_READ/SPLIT/SEARCH118` and `119`
  (`return_call_ref-frame-addr`) are one inside the other.
- No rule returns a list that is not a true list, so `exit-step` did not
  need the run-time test that `anyprefix-step` has; the test there is
  now redundant and stays.
- Census: `SEARCH-INSTRS-CENSUS 12 searches: 12 lemmas` (the searches the
  rules call directly; `SEARCH118` is called by `SEARCH119`),
  `INSTRS-CENSUS 182 rules: 182 lemmas`.

### 2. An administrative term on which a rule fires (V4 item 1)

- `try-rules-on-admin-term` (9,101 steps): on `((kw n x b))`, `kw` one of
  the three heads, `try-rules` over the machine's table is `STEP_PURE`,
  then `STEP_READ/SPLIT`; the table has no own rule for these heads. From
  V1's three `try-rules-of-*-rules`, which do not exclude these heads.
- `step-of-admin-term-when-rule-fires` (6,322): if `try-rules` fires,
  `STEP` of the term is `(z; res)`. `Step/pure` and `Step/read` are the
  first two disjuncts of `STEP`; the true list is §1.
- `step-of-admin-term-in-block-when-rule-fires` (1,110): with values
  before and a rest after, by V2's `step-of-admin-term-in-flat-block`.
- `step-of-exit-term` (16,250): the same for `(admin-term k n x b)` and
  `(rules-for (list :entry k))`, as `exit-step` writes them; three
  instances, one per kind.

Nothing here mentions the body `b`. Compare V3, where the context rule
had to be reached and so the 24 rules had to fail.

### 3. The two rules on a whole block (V4 item 2)

The block is `v ++ (i) ++ r`, `v` values, `i` of head `TRAP` or
`THROW_REF`. These are the two heads V1's dispatch lemmas exclude.

- `step_pure-of-vals-trap-rest` (25,207): at a `TRAP`, `STEP_PURE` is
  `trap-instrs`. `step_read/split-of-vals-throw_ref-rest` (32,252): at a
  `THROW_REF`, `STEP_READ/SPLIT` is `throw_ref-null`, then
  `throw_ref-instrs`. Both by opening the relation: every other rule
  fails by its shape lemma.
- Each of the two rules fails at the head of the other (V1's
  `-fails-when-first-instr-not-*`).
- **`throw_ref-null` stands before `throw_ref-instrs` in the relation**,
  and `anyprefix-step` tries `throw_ref-instrs` alone. So where
  `throw_ref-instrs` fires, `throw_ref-null` must fail:
  - `(exn-before-throw-p l)`: the first element that is not a value has
    the head `:ref.exn_addr`, or the element before it has.
    `step_read/split/search134-fails-when-not-exn-before-throw` (44,042,
    by the induction of the search) and the same for the rule (951).
  - in the machine's block, `rev(vals) ++ (i) ++ r`, that is
    `(equal (car (car vals)) :ref.exn_addr)`
    (`exn-before-throw-p-of-rev-vals-throw_ref-rest`, 2,240);
  - `throw_ref-null` fails unless the element before the `THROW_REF` has
    the head `:ref.null_addr` (731; 4,178 in the machine's block).
- `step-of-block-rule` (27,225): if `try-rules` over
  `(rules-for :anyprefix)` fires on the block, `STEP` of the block is
  `(z; res)`. Hypotheses: `vals` are values, `r` is a true list, the head
  of `i` is `TRAP` or `THROW_REF`. No hypothesis about the top of the
  stack: with a null reference there, `throw_ref-instrs` fails and
  nothing is claimed.

### 4. `throw_ref` under a null reference (V4 item 3)

The redex is `(ref.null_addr) (throw_ref)`; `redex-arity` is 1 and the
table has one rule for the opcode. This is V2's flat block for the head
V2 excludes, and V2's search lemmas are used as they are
(`flat-search-finds-redex` at arity 1):

- `step-of-throw_ref-instr-alone` (4,324): `((throw_ref))` does not step,
  so no step with fewer operands (`no-step-below-1-of-throw_ref`, 93).
- `try-rules-on-null-throw_ref-is-step` (5,822): what `op-step` makes of
  the rule is `STEP` of the redex.
- `step-of-null-throw_ref-block-is-flat-search` (3,234): with more values
  or a rest, no pure and no read rule fires on the whole block
  (`throw_ref-null` by its length, `throw_ref-instrs` by §3), so `STEP`
  is `Step/ctxt-instrs`.
- `step-of-null-throw_ref-block` (5,626): the statement of V2's
  `step-of-flat-block` for this head.

### 5. The machine (`machine/exit-steps.lisp`)

- `stepn-1-under-ctrl` (9,593): V3's `step-under-ctrl` with the step of
  the block given as `(equal (w3t::step ...) (list (list :|%;%| (list
  :|%;%| s2 fr2) b2)))` and the conclusion as `stepn 1`. `:rule-classes
  nil`: it is used with all its variables given.
- `block-step-simulates` (13,545): if `STEP` of the innermost block of
  `s` is the innermost block of `s2`, and `s2` has the control stack of
  `s`, then `(stepn 1 (machine-abs s))` is `(list (machine-abs s2))`.
  The block is not the body of an exit because it steps (V3's
  `not-exit-body-p-when-block-steps`). `anyprefix-step-simulates` and
  `op-step-simulates-throw_ref-null` are instances.
- `exit-step-simulates`: the block that steps is the one **around** the
  innermost entry, `rev(entry-v e) ++ (term) ++ entry-r e`, in the frame
  outside the entry, lifted through `(cdr ctrl)`. It is not the body of
  an exit because its first instruction is an administrative term
  (`not-exit-body-p-of-vals-admin-term-rest`).

**C2 for a clock-1 step, case by case** (`machine-step`, in its order):

| Case of `machine-step` | Step | Theorem |
|---|---|---|
| no instruction left, `ctrl` not empty | `exit-step` | `exit-step-simulates` |
| `throw_ref`, top of the stack `ref.null_addr` | `op-step` | `op-step-simulates-throw_ref-null` |
| `trap` or `throw_ref` with other values or instructions | `anyprefix-step` | `anyprefix-step-simulates` |
| `br`, `return`, `trap`, `throw_ref` first, `ctrl` not empty | `exit-step` | `exit-step-simulates` |
| any other instruction | `op-step` | `op-step-simulates` (V3) |

V5 item 1 is this case split.

**Hypotheses** (of a lemma; no theorem of plan2.md §1 got one):

| Theorem | Hypothesis | Why |
|---|---|---|
| all three | the step ends `:run` | a step that stops has clock 0 (`clock0.lisp`) |
| `exit-step-simulates` | `(consp (ms-ctrl s))` | there is an entry to leave; `machine-step` tests it |
| `anyprefix-step-simulates` | the head is `TRAP` or `THROW_REF` | with another head the two relations have other rules; `machine-step` tests it |
| `op-step-simulates-throw_ref-null` | the head is `THROW_REF` and the top of the stack has the head `:ref.null_addr` | the two tests of `machine-step` for this case. The second is used to make `throw_ref-instrs` fail on the whole block; it also follows from the rule having fired |

### 6. The machine bug

Found by reading `Step_read/throw_ref-null` for item 3, then run
(`data/v4-exits/throw-null-bug.lsp`, `.out`):

```
c = (:|%;%| (:|%;%| nil nil) ((:ref.null_addr) (:throw_ref)))
(w3t::step c)                  = ((:|%;%| (:|%;%| nil nil) ((:trap))))
machine of f8c3d9f             : status :STUCK, abs unchanged
machine after the fix          : status :TRAP
```

and the same with a value before and an instruction after, and inside a
label. `machine-step` (and `fast-step`, the same line) tested
`(eq (entry-kind (car-t vals)) :ref.null)`. `:ref.null` is the head of
the instruction `ref.null ht`, which steps to the value
`(:ref.null_addr)`; under `machine-ok` the operand stack holds values, so
the test was never true. The state then went to `anyprefix-step` (both
rules fail), to `exit-step` (no rule of the term matches) or to
`:stuck`.

- It is the stuck direction: the machine stopped where the specification
  steps. T1 says nothing about `:stuck`, so no proved statement was
  false, and C2 was not (the clock of a step that stops is 0).
- No test found it: no script of spec-test-3 throws a null reference
  (`exceptions--throw_ref` has no such command), and the demos do not use
  `throw_ref`.
- Fix: `:ref.null_addr` in `machine/machine.lisp` and `fast/fast.lisp`,
  one token each. No proof of an old book changed; every engine book was
  certified again (§8).

### 7. What failed first

- **A hypothesis that binds a variable which is already bound.**
  `try-rules-on-admin-term` was first stated for a list `l` with the
  hypothesis `(equal l (list (list kw n x b)))`. As a rewrite rule its
  left side binds `l`; `n`, `x`, `b` are then free in a hypothesis that
  is not in the context, and the rule never fires:

  ```
  (IMPLIES (AND (TRUE-LISTP (CAR (W3T::STEP_PURE (LIST (LIST KW N X B))))) ...
                (MV-NTH 0 (TRY-RULES (RULES-FOR (HEAD-PLACE KW)) Z (LIST (LIST KW N X B)))))
           (TRUE-LISTP (MV-NTH 2 (TRY-RULES (RULES-FOR (HEAD-PLACE KW)) Z (LIST (LIST KW N X B))))))
  ```

  Now the left side has the list written out.
- **A conclusion about a bound name is not a rewrite rule.** With
  `(equal tr (try-rules ...))` in the hypotheses, the conjunct
  `(true-listp (mv-nth 2 tr))` has only `tr` on its left side. The
  checkpoint was

  ```
  (IMPLIES (AND (MEMBER-EQUAL KW '(:LABEL_%{%}% :HANDLER_%{%}% :FRAME_%{%}%))
                (MV-NTH 0 (TRY-RULES (RULES-FOR (HEAD-PLACE KW)) Z (LIST (LIST KW N X B)))))
           (EQUAL (MV-NTH 2 (TRY-RULES ...)) (APPEND (MV-NTH 2 (TRY-RULES ...)) NIL)))
  ```

  Now a lemma of its own with `try-rules` written out
  (`try-rules-on-admin-term-result`), true whether a rule fires or not.
  The same checkpoint appeared once more while `try-rules-on-admin-term`
  was enabled: it rewrote the `try-rules` that the other lemmas name. It
  is disabled after the two lemmas that open it.
- **The search keeps `(cadr (nthcdr k l))`.** The rule that concludes
  `exn-before-throw-p` was first stated with
  `(equal (car (nth (+ 1 k) l)) :throw_ref)`, as V3's
  `exit-block-p-when-vals-then-reference` is:

  ```
  (IMPLIES (AND ... (W3T::STEP_READ/SPLIT/MATCH127 (TAKE K L)) (< K (LEN L))
                (EQUAL (CAR (NTH K L)) :REF.EXN_ADDR) ...
                (CONSP (CDR (NTHCDR K L)))
                (EQUAL (CAR (CADR (NTHCDR K L))) :THROW_REF) ...)
           (EXN-BEFORE-THROW-P L))
  ```

  Stated with `(consp (cdr (nthcdr k l)))` and
  `(car (cadr (nthcdr k l)))`, as `rules/shape.lisp` does for the same
  search, it is used.
- **A rule about `(nth (len v) (append v ...))` after `len-of-revappend`.**
  In `step-of-block-rule` the block is `(append (revappend vals nil) ...)`;
  `(len (revappend vals nil))` becomes `(len vals)` and V1's
  `nth-of-first-nonval-of-append-of-vals-and-instr` no longer matches:

  ```
  (IMPLIES (AND (NOT (EQUAL (CAR (CAR VALS)) :REF.EXN_ADDR)) (VALS-P VALS) (TRUE-LISTP R)
                (EQUAL (CAR I) :THROW_REF)
                (CONSP (W3T::STEP_PURE/R-TRAP-INSTRS (APPEND (REVAPPEND VALS NIL) (CONS I R)))) ...)
           (EQUAL (FLAT-SEARCH (LEN VALS) (REVAPPEND VALS NIL) I R Z) ...))
  ```

  ("`trap-instrs` fires at a `THROW_REF`", which is false.) Now a lemma
  for a variable `v` (`step_pure/r-trap-instrs-of-vals-throw_ref-rest`),
  which the rewriter instantiates.
- **`(consp vals)` does not give `(<= 1 (len vals))` to a rule.**
  `vals-p-of-operands` asks `(<= (nfix j) (len vals))`; with `(consp
  vals)` in the hypotheses `step_read/split-of-vals-throw_ref-rest` did
  not fire on `(append (operands 1 vals) (list i))`. The hypothesis is
  now the inequality, which is what `op-step` tests.
- **`take-of-1` takes the redex apart.** In
  `op-step-simulates-throw_ref-null` the arity is the constant 1, and
  `(take 1 vals)` became `(list (car vals))`, so the redex was no longer
  `(append (operands 1 vals) (list i))`. Disabled in that proof.
- No failed checkpoint was a state the machine can reach. The bug of §6
  was not found by a checkpoint.

### 8. Gate and tests

`make -C engine check` after the change of `machine.lisp` and `fast.lisp`,
every engine book certified again (`data/v4-exits/gate.txt`):
`engine: no skip-proofs, no defaxiom in 29 book(s)`. Times of the books
that are new or whose source changed:

| Book | Before (s) | After (s) |
|---|---|---|
| `machine/machine` | 2.6 | 2.5 |
| `fast/fast` | 3.3 | 3.2 |
| `rules/exits` | new | 2.9 |
| `machine/exit-steps` | new | 2.4 |

("Before" from [V3-contexts](V3-contexts.md) §8 and its `gate.txt`.) The
books that include the two machines certify with no change to their
source; the long ones are `fast/frame` 269 s, `fast/memory` 381 s,
`fast/refine` 145 s and `fast/refine-step` 377 s.

Tests, all with the two machines after the fix. None of them is a claim
about the proved subset (plan.md D8), they compare machines.

| Test | Run | Result |
|---|---|---|
| 1, list machine against the spec at every step | `machine/difftest-run.lsp`, `data/v4-exits/difftest1.out` | 10 runs, 0 disagreements; every line equal to V3's |
| 2, list machine against the spec over spec-test-3 | `machine/difftest2-all.sh`, 6 jobs, 900 s; `data/v4-exits/difftest2/` | 32,706 commands same result and same store; 24,722 `:unsupported` (outside D5); 11 not invocations; 24 printed as different, all of them the machine out of its 2,000,000 steps with the same store where the spec finishes (as in V3); 250 scripts finished, the same 8 stopped at 900 s as in V3 (see below) |
| lockstep, fast machine against list machine | `fast/fasttest-run.lsp`, `data/v4-exits/fasttest.out` | 8 lockstep runs, 0 disagreements, every line equal to V3's; 6 whole runs with equal final states |
| 3, fast machine against list machine over spec-test-3 | `fast/difftest3-all.sh`, 8 jobs, 900 s; `data/v4-exits/difftest3/` | 32,648 commands with equal final states, 24,726 `:unsupported` on both machines in equal states, 11 out of fuel on both in equal states, 11 not invocations, **0 different**; 251 scripts finished, the same 7 stopped at 900 s as in V3 and E7 (see below) |
| slides | `make -C engine slides` | 7 of 7 identical to V8 |
| the three configurations of §6 | `data/v4-exits/throw-null-bug.lsp` | `:STUCK` before the fix, `:TRAP` after, as the specification |

The numbers of tests 2 and 3 are each one full run and a second run of
the scripts that the full run stopped at 900 s and V3's had finished:

- Test 2: the full run was started while the gate was certifying, and
  `memory_grow` and `memory64--memory_grow64` did not finish in it
  (`SUMMARY`: 32,641 same, 22 printed as different, 248 scripts
  finished). Run again alone they finish (`SUMMARY-rerun`: 123 same, 12
  at the machine's fuel). The table counts these two scripts from the
  second run: 32,641 - 58 + 123 and 22 - 10 + 12.
- Test 3: `bulk-memory--bulk` did not finish in the full run (the
  computer slept during it); run again alone it finishes with 104
  commands equal (`per-command.txt`). The table counts it from the
  second run: 32,553 - 9 + 104.
- Against V3 (32,707 and 32,659): a script that stops at the time limit
  gets a different number of commands done from run to run. No command
  has a machine result that differs, in either test.
- The fix cannot change a run in which no null reference is thrown, and
  no script throws one (§6): these runs show no new disagreement, not
  more. What tests the fix is the last row.

### 9. Practice (step2.md), where the books depart from it

- `rules/exits.lisp` has 8 hints with `:use`, 5 `:cases`, 2 `:expand`;
  `machine/exit-steps.lisp` has 5 hints with `:use`. No `"Subgoal"` hint.
  The `:use` hints are instances of lemmas with `:rule-classes nil`
  (their free variables are the parts of a machine state) and of V1's
  and V2's lemmas at a constant (`v` empty, arity 1, the three kinds of
  term).
- `try-rules` and `apply-rule` (defined in `machine.lisp`, an old book)
  are disabled in the header of the two new books, as `admin-term` is
  since V3.
- `rules/flat.lisp` keeps its constant `*instrs-not-yet*` and its census:
  the 12 lemmas need the searches, which that book does not open. The
  census of `rules/exits.lisp` is over all 182 rules and records none
  missing.

## Open questions

- V5 item 1 is the case split of §5. `machine-clock` is 1 exactly in
  those cases when the step ends `:run`; the heads of the last case have
  to be shown to be neither administrative nor `TRAP`/`THROW_REF` from
  the tests `machine-step` made before it.
- `anyprefix-step` tests `(true-listp res)`; by §1 the test is always
  true. Removing it would change the machine (and `fast-anyprefix-step`)
  for no gain in the theorem; left as it is.

## Data

All under `data/v4-exits/`.

- `measure.sh`: reads the generator lines, the census lines, the prover
  steps of the named theorems, the certification times and the hint
  counts. `measure.txt`: its output. Regenerate at the repository root,
  inside `nix develop`, after `make -C engine check`:
  `sh plan/wasm-engine/notes/data/v4-exits/measure.sh > plan/wasm-engine/notes/data/v4-exits/measure.txt`.
- `gate.txt`: the lines of `make -C engine check` that name a book or the
  result.
- `throw-null-bug.lsp` and `throw-null-bug.out`: the three configurations
  of §6 on the machine before the fix (commit f8c3d9f) and after.
- `difftest1.out`; `difftest2/SUMMARY` and `difftest2/D2-LINES.txt.gz`;
  `fasttest.out`; `difftest3/per-command.txt` and
  `difftest3/D3-LINES.txt.gz`.
