# V2: the flat block

- Milestone: V2 (plan2.md: operand prefix, `ctxt-instrs`, the same with an administrative term in the middle, `op-step` at the top level)
- Date: 2026-11-17
- Repo commit: a342495 plus this note's commit
- Status: final
- Feeds engine plan: V3 (`op-step-is-step-of-flat-block` and `step-of-admin-term-in-flat-block` are the two halves of each induction step), V4 (the 12 rules without an instructions lemma; `throw_ref-null`), V5 (the hypotheses of `op-step-simulates-flat`)
- Incorporated in engine plan: yes (plan2.md V2, "Current state")

## Summary

- **V2 is complete.** Two new books, `engine/rules/flat.lisp` (6.2 s) and
  `engine/machine/op-flat.lisp` (2.6 s), certify under
  `make -C engine check`. The gate has 25 books (23 before), no
  `skip-proofs`, no `defaxiom`, no trust tag. No machine changed, so no
  differential test was due.
- **The exit theorem certifies, for every opcode with rules at once**:

  ```lisp
  (defthm op-step-simulates-flat
    (implies (and (machine-ok s)
                  (not (consp (ms-ctrl s)))
                  (not (admin-kind (car-t (ms-is s))))
                  (not (sym-member (entry-kind (car-t (ms-is s))) '(:trap :throw_ref)))
                  (equal (ms-status (op-step s)) :run))
             (equal (stepn 1 (machine-abs s))
                    (list (machine-abs (op-step s))))))
  ```

  The opcode enters only through V1's per-relation lemmas. The largest
  proof is 200,185 prover steps.
- **The machine's choice of redex is `STEP`'s** (plan2.md §5 row 3 did not
  happen): no checkpoint of a failed attempt was a state the machine can
  reach. Every failure was a matter of how a lemma was stated (§7).
- **The `call_ref` question of V1 is settled without a change to the
  invariant**: `machine-ok` says the operands are values (`val-list-p`),
  and a function reference that is a value names a natural number.
- **For V3**: the lemma to lift is `op-step-is-step-of-flat-block`, which
  has no hypothesis about the control stack; and
  `step-of-admin-term-in-flat-block` is the `ctxt-instrs` half of the
  context lemma's induction step.

## Findings

All prover steps are from the certification output
(`data/v2-flat/measure.txt`).

### 1. The search of `Step/ctxt-instrs` (`flat.lisp`)

`STEP/R-CTXT-INSTRS` on `(z; l)` takes the length `p` of the value prefix
and calls `STEP/SEARCH21` with `k` from `p` down to 0. At `k` it steps the
values from `k` on and the first instruction: so it tries the **fewest
operands first**. It needs values before `k` or a rest after the
instruction, and the `%SIZE` test.

- `(flat-search k x i r z)` says exactly that for `l = x ++ (i) ++ r`,
  `x` values, `i` not a value, with nothing of the generated code in it.
- `step/search21-becomes-flat-search` (63,187 steps) and
  `step/r-ctxt-instrs-becomes-flat-search` (469) rewrite the two generated
  functions to it. The `%SIZE` test is discharged there, once
  (`%size-of-operands-and-instr`, from V0's `%size-check-of-sublist`), and
  the shape of the inner result by V0's `step-result-shape`. No later
  proof opens the search.
- The other three context rules fail unless the list is one administrative
  term of their head (`step/r-ctxt-{label,handler,frame}-fails-when-not-shape`,
  1,932 to 3,723 steps, by `:expand` in V1's `shape-theory`).

### 2. A rule that fires has `redex-arity` operands

```lisp
(defthm step_pure-arity                   ; 88,197 steps
  (implies (and (redex-shape-p kw l)
                (w3t::step_pure l)
                (natp (redex-arity (nth (+ -1 (len l)) l) z vals)))
           (equal (redex-arity (nth (+ -1 (len l)) l) z vals) (+ -1 (len l)))))
```

and the same for `STEP_READ/SPLIT` (94,638; head not `THROW_REF`) and
`step-own` (45,866). Proof: `:cases` on the 106 known heads; V1's
`<relation>-OF-REDEX-<KW>` gives the rules of the head and each
`<R>-ARITY` closes its case. A head that `redex-arity` does not support
contradicts the `natp` hypothesis (`redex-arity-of-last-when-not-supported`,
with the list `*arity-heads*` of the 48 supported heads).

`step-own-arity` has the `call_ref` hypotheses of V1 §4, as a disjunction:
the head is not `call_ref`, or the list has one element, or the top of
`vals` is the element before the instruction and, if it is a function
reference, names a natural number. Two facts were added for it: every
`call_ref` rule fails on a list of one element, and the three rules for a
function fail unless the reference has head `REF.FUNC_ADDR`.

### 3. What a rule returns (generated)

| Family | Says | Rules | Proof time |
|---|---|---|---|
| `<R>-INSTRS-TRUE-LISTP` | the instructions of a pure or a read rule are a true list | 170 of 182 | in the 3.8 s of the book |
| `<R>-STATE-SHAPE` | the state of one of `STEP`'s own rules has the shape `(:|%;%| s f)` when the state before has | 30 of 30 | the same |

- **Why the first is needed.** `STEP/R-PURE` and `STEP/R-READ` test
  `(true-listp ...)` on what the relation returns and fail otherwise; the
  machine uses the result as it is. So C2 needs that the result is a true
  list.
- **The 12 without a lemma** return what a search found (`br-label-*`,
  `br-handler`, `return-*`, `trap-instrs`, `return_call_ref-*`,
  `throw_ref-instrs`). All have an administrative term or a whole block as
  redex: the census fails the book if one of them is a rule of an opcode.
  They are V3's and V4's (`*instrs-not-yet*`).
- **The second is the item V0 left to V2.** The machine keeps `(cadr z')`
  and `(caddr z')` as store and frame; `machine-abs` rebuilds
  `(:|%;%| store frame)`, which is `z'` only if `z'` has that shape. The
  theory of each proof is the rule and the 14 functions of the
  specification named `$with_*` and `$add_*`, read from the world.
- Per relation, for a symbolic head: `step_pure-instrs-true-listp`
  (43,236), `step_read/split-instrs-true-listp` (78,280),
  `step-own-result-shape` (44,942), `step-own-state-shape` (139,426).

### 4. Operand prefix (V2 item 1)

`(operands j vals)` is `(revappend (take j vals) nil)`: the top `j` values
of the machine's stack in the order of the configuration.
`(no-step-below n i z vals)`: `STEP` fails on `(z; (operands m vals) ++ (i))`
for every `m < n`.

```lisp
(defthm no-step-below-arity               ; 5,685 steps
  (implies (and (vals-p vals) (op-instr-p i) (natp n) (<= n (len vals))
                (natp (redex-arity i (list :|%;%| s f) vals))
                (<= n (redex-arity i (list :|%;%| s f) vals)))
           (no-step-below n i (list :|%;%| s f) vals)))
```

By induction on `n`. With `m` operands, `m` less than the arity: no rule
of the three relations fires (§2); the three context rules for one term
fail (§1); and `Step/ctxt-instrs` searches fewer operands still, where the
induction hypothesis says `STEP` fails
(`flat-search-of-operands-when-no-step-below`). The type-dependent arities
need nothing more: `redex-arity` is the rule's own count (V1).

`(op-instr-p i)`: `i` is a cons, its head is not a value's, not `TRAP`,
not `THROW_REF`, not an administrative head.

### 5. The flat block (V2 items 2 and 3)

- `step-of-redex` (14,179): on `(operands a vals) ++ (i)` with `a` the
  arity, `STEP` is `Step/pure`, `Step/read` or its own rules; the four
  context rules fail.
- `step-of-flat-block` (31,917): for `vals` values, `r` a true list, `a`
  the arity, `a <= (len vals)`, if `STEP` of the redex is `(z'; is')` then

  ```
  STEP (z; rev(vals) ++ (i) ++ r) = (z'; rev(nthcdr a vals) ++ is' ++ r)
  ```

  Two cases. Nothing around the redex: the block is the redex. Otherwise
  no pure and no read rule fires on the block (V1's
  `step/r-*-of-vals-instr-rest` when `r` is not empty; §2 when only values
  are before), and the search skips the counts below `a` (§4) and stops at
  `a` (`flat-search-finds-redex`).
- `step-of-admin-term-in-flat-block` (1,673): the same with one
  administrative term for `i`, `v` or `r` not empty. The search finds the
  term at once (no operand), so nothing is asked about `STEP` on fewer
  elements. Needs that the pure and the read rules of an administrative
  head fail on a list that is not one element (V1's length lemmas).

### 6. `op-step` (V2 item 4, `op-flat.lisp`)

- `try-rules-on-redex-is-step` (200,185): when `try-rules` over the rules
  of the opcode fires with `(mv t z2 res)`, `STEP` of the redex is
  `((:|%;%| (:|%;%| (cadr z2) (caddr z2)) res))` and `res` is a true list.
  From V1's three `try-rules-of-*-rules` and §3.
- `op-step-is-step-of-flat-block` (155,593): for `machine-ok`, a head
  `op-instr-p` and `op-step` ending `:run`, `STEP` of
  `(store; frame; rev(vals) ++ is)` is the same term of the next state,
  and the control stack is unchanged. **No hypothesis about `ctrl`.**
- `op-instr-p-when-op-step-runs` (75,723): `op-instr-p` follows from
  `op-step` ending `:run` on a head that is not administrative, not `TRAP`
  and not `THROW_REF`: a value's head and `nil` have no rules in the table.
- `op-step-simulates-flat` (2,653): the exit.

**Hypotheses** (of a lemma; no theorem of plan2.md §1 got one):

| Hypothesis | Why |
|---|---|
| `(not (consp (ms-ctrl s)))` | V2 is the flat case; V3 removes it |
| head not `TRAP`, not `THROW_REF` | on those heads `trap-instrs` and `throw_ref-instrs` can fire on the whole block, and V1's per-relation lemmas exclude them. `machine-step` gives `op-step` such a head in one case only, `throw_ref` under `ref.null`: V4 item 3 |
| head not administrative | `machine-step` enters such a term; `op-step` never sees one |
| `op-step` ends `:run` | a step that stops is clock 0 (`clock0.lisp`) |

### 7. What failed first

- **`nthcdr 0` and `take 0` are rewritten away.** The size lemma stated
  for `(append (nthcdr k x) (list i))` did not fire at `k = 0`. Checkpoint:

  ```
  (IMPLIES (AND (CONSP R) (W3T::STEP (LIST :|%;%| Z (APPEND X (LIST I)))) ...)
           (EQUAL (WRT::%SIZE (APPEND X (LIST I)))
                  (WRT::%SIZE (APPEND X (CONS I R)))))
  ```

  A second lemma for the form at 0 (`%size-of-all-operands-and-instr`).
  The same with `(not (take k x))` for `k > 0`: `take-under-iff`.
- **A rule stated with `(nth 2 (list ...))`** (V0's `%size-check-*`) never
  matches: the rewriter reduces the `nth` first. V2 restates the fact
  without it.
- **`no-step-below` for a number that is not an integer.**
  `step-of-operands-when-no-step-below` without `(natp n)`:

  ```
  (IMPLIES (AND (ZP N) (NATP J) (< J N))
           (NOT (W3T::STEP (LIST :|%;%| Z (APPEND (OPERANDS J VALS) (LIST I))))))
  ```

  True for `n = 1/2`, `j = 0` only if `STEP` fails: the hypothesis was
  missing. Not a machine state.
- **Induction on the search with a case split inside.** "The search from
  `k` finds the redex" by induction on `k` left

  ```
  (W3T::STEP (... (OPERANDS (+ (- K) (LEN VALS)) VALS) ...))   ; a hypothesis
  ```

  with nothing to say that this count is the arity. A forward-chaining
  rule for it did not fire (its `natp` hypothesis is not known to
  type-set). What works: the rewrite rule `flat-search-when-step-fails`
  (a failed step moves the search by one), then "the search from any count
  up to `a` is the search from `a`" by an induction that counts up
  (`flat-search-skips-too-few-operands`, 2,737 steps), then one expansion
  at `a`.
- **The opener opens every `STEP`.** `step-opener-with-step-own` enabled
  in the proof of `step-of-flat-block` also opened the step of the redex
  in the hypothesis (checkpoint `Subgoal 2.250.2401''`, a goal about
  `STEP_PURE` of both lists). The outer step is now its own lemma,
  `step-of-flat-block-is-flat-search`, whose statement has no inner step;
  the main proof runs with the opener disabled.
- **Seven `:use` hints in one proof**: `try-rules-on-redex-is-step` in one
  piece passed the limit of 2,000,000 steps with no checkpoint. In three
  pieces (`try-rules-on-redex`, `step-of-redex-by-relation`, then the
  theorem with no hint) it is 166,915 + 38,390 + 200,185.
- **A free variable no hypothesis binds.** The lemmas with
  `(redex-shape-p kw l)` as a hypothesis do not fire on
  `v ++ (i)`: the shape is rewritten to true and is not in the context.
  They are `:rule-classes nil` or restated for `(append ... (list i))`.

### 8. Practice (step2.md), where the books depart from it

- `flat.lisp` has 19 `:use`, 9 `:cases`, 9 `:expand`; `op-flat.lisp` has 3
  `:use`. No `"Subgoal"` hint. The `:use` hints are the instances of the
  lemmas with a free `kw` (§7 last item) and of `step-of-flat-block`,
  whose variables `a` and `inner` stand for large terms.
- `engine/lib/lists.lisp` got seven rules: `nthcdr-of-revappend-nil`,
  `take-of-revappend-nil`, `take-of-take`, `nth-of-take`,
  `nth-of-revappend-nil`, `consp-of-take`, `take-of-1`. The books that
  include it certify unchanged.
- `revappend-of-take-becomes-operands` and the definition of `operands`
  have a `theory-invariant`.
- At the end of `flat.lisp` the rules that open or move a search or a step
  are disabled (`flat-search`, `flat-search-when-step-fails`,
  `step-of-redex`, `step-of-redex-by-relation`, `try-rules-on-redex`,
  `no-step-below-arity`).

## Open questions

- V3's context lemma needs the step of the block inside an entry as a
  step of the list around it: `step-of-admin-term-in-flat-block` asks
  `v` or `r` not empty; with both empty the list is the term alone and
  only the entry's own context rule applies.
- For V5: `machine-step` reaches `op-step` in its last case and for
  `throw_ref` under `ref.null`. The last case gives the hypotheses of
  `op-step-simulates-flat` but for `br` and `return` with no control
  entry, where it stops `:stuck` before `op-step`.

## Data

All under `data/v2-flat/`.

- `measure.sh`: reads the generator lines, the census lines, the prover
  steps of the named theorems, the certification times and the hint counts
  from `engine/rules/flat`, `engine/machine/op-flat` and `engine/lib/lists`.
  `measure.txt`: its output. Regenerate at the repository root, inside
  `nix develop`, after `make -C engine check`:
  `sh plan/wasm-engine/notes/data/v2-flat/measure.sh > plan/wasm-engine/notes/data/v2-flat/measure.txt`.
