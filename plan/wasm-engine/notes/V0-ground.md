# V0: ground work for the proofs of plan 2

- Milestone: V0 (census, `engine/lib/`, one `ctrl-ok`, `step-basics`, the `nop` spike)
- Date: 2026-11-17
- Repo commit: 12ed2a3 plus this note's commit
- Status: final
- Feeds engine plan: V1 (the generator and its theory), V2 and V3 (`step-opener`, `%SIZE`), V5 item 4 (the set of proved opcodes), V6 (both machines' books in one world), V7 (`call_ref`, `data.drop`)
- Incorporated in engine plan: yes (plan2.md V0, "Current state")

## Summary

- **Census.** The slides, `input.tex` and the talk deck apply 37 of the 212
  rule functions. No trap, no exception and no table rule fires. Every call
  is a `call_ref` of a wasm function; `call_ref` of a host function occurs
  in TeX only (3,717 and 63,681 times). `data.drop`, `memory.init` and
  `ref.null` occur in every run, at instantiation, and are not in
  `*d5-opcodes*`.
- **Spike: go, on the first approach.** `STEP/R-PURE` and `STEP/R-READ`
  return `nil` on `v ++ (nop) ++ r` for a symbolic value list `v` and any
  `r`, one of them not empty: 3,634 and 4,719 prover steps for the two
  relations. The whole script, with a lemma for each of the 212 rule
  functions, runs in 8.3 s. The rule functions stay closed.
- **What made it work**: one lemma per rule function, "the rule fails
  unless its list is values followed by one instruction with the rule's
  opcode", proved in a theory that has no definition of the specification
  but the rule's own. In the default theory one such lemma ran 346 s.
- **New books**: `engine/lib/lists.lisp`, `engine/lib/records.lisp`,
  `engine/rules/step-basics.lisp`, `engine/fast/ctrl-kinds.lisp`. The gate
  certifies 20 books (16 before), with the theorems it had.

## Findings

### 1. Census of rule functions

A rule is counted when its function returns a result. The counter wraps
the four ways the fast machine reaches a rule (the rule function, its
executable counterpart, the generated fast version of a memory rule, the
six hot paths of `fast-hot-step`); it is raw Lisp loaded by the driver and
no part of a book (`data/v0-ground/census.lisp`). The TeX driver loads it
when `TEXCENSUS` is set.

| Run | Machine steps | Rule applications | Rule functions | Host `call_ref` |
|---|---|---|---|---|
| Slides (7 slides, instantiation and 4 queries) | not counted | 3,626,696 | 28 | 0 |
| TeX, `engine/tex/input.tex` | 55,072,572 | 27,946,273 | 34 | 3,717 |
| TeX, the talk deck (`engine/tex/deck/deck.tex`) | 606,874,026 | 305,651,715 | 34 | 63,681 |

The steps that are not rule applications move a value or enter an
administrative term (clock 0), or are host steps. The table of all 37
rules with their counts is `data/v0-ground/census-table.txt`. By place:

| Place | Rule functions that fired |
|---|---|
| Operators (pure) | `binop-val`, `relop`, `testop`, `unop-val`, `cvtop-val`, `select-true`, `select-false`, `drop`, `local.tee`, `if-true`, `if-false`, `br_if-true`, `br_if-false`, `br_table-lt`, `br_table-ge` |
| Read | `local.get`, `global.get`, `block`, `loop`, `call`, `ref.null`, `load-num-val`, `load-pack-val`, `memory.init-succ`, `memory.init-zero` |
| Step | `local.set`, `global.set`, `store-num-val`, `store-pack-val`, `call_ref-func`, `data.drop` |
| Label | `label-vals`, `br-label-zero`, `br-label-succ`, `return-label` |
| Frame | `frame-vals`, `return-frame` |

What this fixes for the later milestones:

- **V5 item 4 (P3).** The opcodes that ran are inside D5 except three: `memory.init`, `data.drop` and `ref.null`, which the
  specification's instantiation emits for every module with a data
  segment or a `ref.null` initializer. The table of proved opcodes must
  contain them, or the slides stop `:unsupported` during instantiation.
- **V7.** `call_ref-func` is on the path of every call (26, 111,851 and
  1,136,140 applications): `call` rewrites to it. Its place lemma is
  needed for T2 to cover any module with a function call. `data.drop`
  fires 1 time (slides) and 40 times (TeX), always at instantiation.
- **P1.** A host `call_ref` occurs in TeX and not in the slides, as
  expected. With P1 as decided the slides are inside T3 and TeX is run as
  stretches between host calls.
- **Not exercised by any demo**: every trap rule (`binop-trap`, the
  out-of-bounds rules, `unreachable`), `trap-instrs`, the handler rules,
  `throw`, `throw_ref`, `try_table`, tables, `memory.size`, `memory.grow`,
  `memory.copy`, `memory.fill`. Their only tests are tests 1 to 3.
- The TeX run is outside S0: it uses `f32` (`cvtop-val` 1,594 and
  `unop-val` 459 applications in the deck) and host calls.

### 2. The spike: `nop`

Statement (the V1 exit statement for `nop`), for any state `z`:

```lisp
(defthm step/r-pure-of-vals-nop-rest
  (implies (and (vals-p v) (or (consp v) (consp r)))
           (equal (w3t::step/r-pure (list :|%;%| z (append v (cons '(:nop) r)))) nil)))
(defthm step/r-read-of-vals-nop-rest      ; the same for STEP/R-READ
  ...)
```

Both are proved in `data/v0-ground/spike-nop.lsp`, a session script
(not a certified book; V1 makes the book). Output:
`data/v0-ground/spike-nop.out`.

| Lemma | Prover steps |
|---|---|
| `step_pure-of-vals-nop-rest` (`STEP_PURE` opened, its 79 rule functions closed) | 3,634 |
| `step_read/split-of-vals-nop-rest` (`STEP_READ/SPLIT` opened, its 103 rule functions closed) | 4,719 |
| `step/r-pure-of-vals-nop-rest` | 268 |
| `step/r-read-of-vals-nop-rest` | 280 |
| All events of the script (49 summaries) | 722,354 |
| Wall time of the script, includes and all | 8.3 s |

How it goes:

1. `(redex-shape-p kw l)`: `l` is not empty, every element but the last
   has the head of a value, and the last has head `kw`.
2. Per rule function `R` with opcode (or administrative head) `K`, the
   rewrite rule `<R>-FAILS-WHEN-NOT-SHAPE`:
   `(implies (not (redex-shape-p K l)) (equal (R l) nil))`. `K` comes
   from `rule-place`. 201 of the 210 are generated and proved with no
   hint but the theory (3 below); none needs induction.
3. The nine rules with a variable number of values (`block`, `loop`,
   `try_table`, `throw`, `struct.new`, `array.new_fixed`, the three
   `call_ref` rules) match `(take (- (len l) j) l)` with a generated
   `MATCHnn` function. Two more facts do them: `MATCHnn` accepts only
   value lists (41 of the 48 one-argument match functions, generated, by
   induction; the other 7 match something else), and "values before position `n`: the shape of `l` is the
   shape of `(nthcdr n l)`".
4. The two rules on a whole block (`trap-instrs`, `throw_ref-instrs`) are
   not of that shape. For them: if the rule fires, the first element of
   `l` that is not a value has head `TRAP` (`REF.EXN_ADDR` or
   `THROW_REF`). By induction on their searches.
5. `(redex-shape-p kw (append v (cons i r)))` is
   `(and (atom r) (equal (car i) kw))` when `v` are values and `i` has
   no value head. So every rule of another opcode fails on
   `v ++ (nop) ++ r` by rewriting, and `nop`'s own rule fails because the
   list is longer than 1.

**The risk of plan2.md §5, first row, did not happen**, and the reason is
visible: no proof opens a rule function on the symbolic `append`. A rule
is opened once, on a variable `l`, in its own lemma.

**Approaches**: one. Inside it, four things failed first and are kept
here because V1 will meet them again:

- *The default theory.* The first generator enabled only `R` on top of
  the current theory. `STEP_PURE/R-VUNOP-VAL-SHAPE` then ran 346 s and
  was stopped by hand, with 943 prover steps counted: the time goes to
  preprocessing, which opens every enabled non-recursive function of the
  numerics (`$VUNOP_` and what it calls). **A step limit does not bound
  this.** In the theory `minimal-theory` + all executable counterparts +
  six list rules + `R`, the same lemma takes under 0.01 s, and all 201
  take 1.9 s.
- *One event, one step limit.* A generator that is one `make-event` of a
  `progn` runs under one limit, the outer one, for the sum of its
  lemmas. With `(set-prover-step-limit 2000000)` the match-function
  family failed from the fourth lemma on, at `Subgoal *1/3'`, for no
  reason in the lemma. The generator's event needs its own large limit;
  each lemma keeps its `with-prover-step-limit`.
- *`(implies (MATCHnn s) (vals-p s))` as a rewrite rule.* Each such rule
  makes every later `(vals-p ...)` goal backchain into a recursive match
  function. As `:forward-chaining` rules all 41 prove (about 3,200 steps
  each).
- *Tail lemmas stated with `(+ -1 (len l))`.* Checkpoint of the first
  version, under induction on `(len l)`:

  ```
  Subgoal *1/1'
  (IMPLIES (AND (CONSP L)
                (REDEX-SHAPE-P (CAR (CADR (NTHCDR (+ -1 (LEN (CDR L))) L))) (CDR L))
                (VALS-P (TAKE (+ -1 (LEN L)) L))
                (NOT (EQUAL (CAR (NTH (+ -1 (LEN L)) L))
                            (CAR (CADR (NTHCDR (+ -1 (LEN (CDR L))) L))))))
           (NOT (REDEX-SHAPE-P (CAR (CADR (NTHCDR (+ -1 (LEN (CDR L))) L))) L)))
  ```

  Not a machine state: a proof that lost its way in the arithmetic. The
  lemmas are now stated for any `n` with the hypothesis
  `(equal (len l) (+ 1 n))` and proved by induction on `n` and `l`
  together; the instance `n = (+ -1 (len l))` is found by the rewriter.

Two smaller ones: a lemma about `(len (append v (cons i r)))` is not
used once `len-of-append` has rewritten its left side, so the `nop` fact
is stated on the term the goal has (`step_pure/r-nop-of-append-of-vals-and-instr`);
and `(cadr (nthcdr n l))` and `(nth (+ 1 n) l)` are both normal forms
in the generated bodies, so a lemma must use the one its rule uses.

**What V1 still has to do** beyond turning the script into a book:
`first-nonval` (it is `STEP/PREFIX7`; the script uses that directly), the
length of the list per rule ("`R` fires, so `(len l)` is `k + 1`", done
here for `nop` only), the statement per relation in terms of
`try-rules` and `rules-for`, and the census check at the end of each
family.

### 3. `engine/lib/`

- `lib/records.lisp`: the seven `put-assoc-equal` lemmas of
  `fast/frame.lisp`, moved unchanged; `frame.lisp` includes the book in
  the place where they stood, so the theory of every book after it is
  what it was.
- `lib/lists.lisp` (35 lemmas, 2.0 s). Part 1: `car-t`, `cdr-t`,
  `len-t`, `app`, `rev-onto`, `nth-t` equal `car`, `cdr`, `len`,
  `append`, `revappend`, `nth` with no hypothesis; `take-n` equals `take`
  when `n` is at most the length; `drop-n` equals `nthcdr` on a true list
  or when `n` is at most the length. These eight are disabled at the end
  of the book and are the theory `machine-lists`. Part 2, enabled:
  `len`, `car`, `cdr`, `consp`, `true-listp`, `nth`, `take`, `nthcdr` of
  `append`; `len` of `take` and `nthcdr`; `take` and `nthcdr` at the
  length; `equal-of-len-and-constant`; and `revappend` normalized to
  `(append (revappend x nil) acc)`.
- **Decision: no old book includes `lib/lists`.** The plan asks that
  existing books include the library instead of restating, and also that
  they are not rewritten because their proofs depend on their theory.
  For `records` both hold. For `lists` they do not: the library would
  add about 25 enabled rules about `append`, `take` and `nthcdr` to
  `ok.lisp` and to everything in `fast/`. So the three lemmas old books
  state themselves stay there (`len-t-is-len` in `ok.lisp` and
  `refine.lisp`, `true-listp-app`, `true-listp-drop-n`, `car-t-is-car`,
  `cdr-t-is-cdr`); the library's own versions have other names
  (`-becomes-`), so a book can include both.
- **The Nix ACL2 has 332 certified system books**, the closure of what
  the repository included when the flake was written. `std/lists/top`
  and `std/lists/nth` are not among them. `include-book` of an
  uncertified book works in a session and fails under `cert.pl`
  (`Can't open ... Permission denied`, in the store). `lib/lists` uses
  `std/lists/append`, `len`, `take`, `nthcdr`, `revappend`, `rev` and
  `arithmetic/top`, all certified, and all `local`. A book that needs
  another system book has to add it to `flake.nix` `systemBooks`, which
  rebuilds ACL2.

### 4. One `ctrl-ok`

`fast/refine-op.lisp` defined `WE::CTRL-OK` (every entry is `:l`, `:h` or
`:f`) and `machine/ok.lisp` defines it as the invariant of the control
stack. The fast one is now `ctrl-kinds-ok` (and `ctrl-ok-top`,
`fast-exit-step-refines-ctrl-ok` are `ctrl-kinds-ok-top`,
`fast-exit-step-refines-ctrl-kinds-ok`). `fast/ctrl-kinds.lisp` includes
`machine/ok` and `fast/refine-op` together and proves

```lisp
(defthm ctrl-kinds-ok-when-ctrl-ok
  (implies (ctrl-ok c) (ctrl-kinds-ok c)))
(defthm ctrl-kinds-ok-of-ms-ctrl-when-machine-ok
  (implies (machine-ok s) (ctrl-kinds-ok (ms-ctrl s))))
```

The statement of `fast-step-refines` is otherwise unchanged. That the two
books load together is itself the result V6 needs; `len-t-is-len` is
stated in both with the same formula and is redundant.

### 5. `engine/rules/step-basics.lisp` (2.7 s)

- `spec-definitions`: the theory of the 2,185 `:definition` runes of the
  packages W3T and WRT, disabled at the top of the book. A proof book
  that includes `step-basics` starts with the specification closed.
- `stepn`: the definition of `theorem/simulation.lisp`, stated again (a
  redundant event when both are included), with `stepn-of-0` and
  `stepn-of-1`; then disabled.
- `step-opener`: `(w3t::step c)` equals `STEP`'s body, which is read
  from the world, when `c` is a `cons` term. Disabled; a proof enables
  it. Proved in `minimal-theory` with one `:expand`.
- `step-result-shape`: `(implies (w3t::step c) (step-result-p (w3t::step c)))`,
  where `step-result-p` says: a list of one element
  `(:|%;%| z' is')` with `is'` a true list. 72,317 prover steps. From
  one lemma per rule function `STEP` calls (36: 30 generated, 6 by hand;
  the family ends with a check that none is missing). No induction over
  `STEP`'s clique: the context rules build their result explicitly, so
  only the search of `ctxt-instrs` needs an induction, on its counter.
  The two host-call rules are included: `$LIFT_RESULT` returns a true
  list for every host.
- **Not proved here: that `z'` has the shape `(:|%;%| s f)`.** It needs a
  fact about each state-changing function (`$WITH_LOCAL` and the like)
  and is V2's (`op-step` at the top level).
- `%SIZE`: `%size-of-cons`, linear rules for `take` and `nthcdr`, and
  the two tests the context rules make, as rewrite rules:
  `%size-check-of-admin-body` (the body of a label, handler or frame is
  smaller than the list holding the term; no hypothesis) and
  `%size-check-of-sublist` (`(take m (nthcdr k l))` is smaller than `l`
  when it is not all of `l`). The second row of plan2.md §5 is settled:
  the check is discharged for a symbolic body.

### 6. Existing books: what changed, and certification times

No proof in an existing book was changed. Changes: a first line pointing
at `LICENSE` in the 17 engine books that had none; `frame.lisp` includes
`lib/records`; `refine-op.lisp` renames `ctrl-ok`. No old book got a
"disable at the end" event, since no new book needs one yet.

Times of `make -C engine check`, every engine book certified again,
`-j 4` (before: at `12ed2a3`, `data/v0-ground/gate-before.txt`; after:
`data/v0-ground/gate-after.txt`):

| Book | Before (s) | After (s) |
|---|---|---|
| `portcullis` | 0.2 | 0.2 |
| `lib/records` | new | 0.3 |
| `theorem/simulation` | 2.4 | 2.4 |
| `rules/if-true` | 2.4 | 2.4 |
| `machine/machine` | 2.8 | 2.9 |
| `rules/first-lemmas` | 2.9 | 3.0 |
| `lib/lists` | new | 2.5 |
| `machine/ok` | 18.7 | 18.8 |
| `machine/clock0` | 3.8 | 3.8 |
| `rules/terminal` | 125.4 | 125.8 |
| `machine/terminal-ok` | 2.1 | 2.3 |
| `rules/step-basics` | new | 2.8 |
| `fast/frame` | 269.5 | 269.6 |
| `fast/memory` | 371.3 | 378.5 |
| `fast/fast` | 3.0 | 3.2 |
| `fast/refine-hot` | 3.3 | 3.6 |
| `fast/refine` | 141.3 | 140.6 |
| `fast/refine-mem` | 40.1 | 39.9 |
| `fast/refine-step` | 354.4 | 345.8 |
| `fast/refine-op` | 7.2 | 6.8 |
| `fast/ctrl-kinds` | new | 2.8 |
| Sum of the engine books | 1351.0 | 1357.9 |

Wall time of the gate: 19 min 54 s after. The run before took 24 min 52 s,
of which about 5 min certified `translate/gen/wasm-3.0` again; the two
wall times are not comparable, the per-book times are. Result after:
`engine: no skip-proofs, no defaxiom in 20 book(s)`.

## Open questions

- V5 item 4 names "the generated table of proved opcodes": it must be
  built from the opcodes with lemmas, and the census says it has to
  contain `memory.init`, `data.drop` and `ref.null`. `*d5-opcodes*` in
  `frame.lisp` does not; whether that constant is extended (which adds
  frame lemmas for their rules, V7) or the table is separate is V5's
  and V7's choice.
- The census counts rules that fired. A count of rules tried is not
  taken; it is not needed for the proofs.

## Data

All under `data/v0-ground/`.

- `census.lisp`, `census-slides.sh`, `census-tex.sh`: the counter and
  the two drivers. `census-slides.out`, `census-tex.out`,
  `census-tex-deck.out`: their output. `census-table.py` makes
  `census-table.txt` from the three. Regenerate, inside `nix develop`
  at the repository root:
  `sh plan/wasm-engine/notes/data/v0-ground/census-slides.sh`,
  `sh .../census-tex.sh` and `sh .../census-tex.sh engine/tex/deck/deck.tex`
  (40 s and 4.5 min; needs `engine/slides/build/sent.wasm` and
  `engine/tex/build/dl`).
- `spike-nop.lsp`, `spike-nop.out`: the spike. Regenerate in that
  directory with `acl2 < spike-nop.lsp` (8 s; needs `rules/terminal` and
  `machine/machine` certified). It includes `std/lists/top`, uncertified
  in the store, which a session allows.
- `gate-before.txt`, `gate-after.txt`: the `Built` lines of the two gate
  runs.
