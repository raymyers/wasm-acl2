# V1: dispatch lemmas

- Milestone: V1 (plan2.md: `first-nonval`, the shape of a redex per rule function, the rules without a fixed shape, the relations as the machine's table, the census)
- Date: 2026-11-17
- Repo commit: f9a79e3 plus this note's commit
- Status: final
- Feeds engine plan: V2 (operand prefix, `ctxt-instrs`, `op-step` at the top level), V3 (the rules on an administrative term), V4 (`trap-instrs`, `throw_ref-instrs`, `THROW_REF-NULL`), V5 item 4 (the opcodes `redex-arity` supports)
- Incorporated in engine plan: yes (plan2.md V1, "Current state", §5 rows 1 and 4)

## Summary

- **V1 is complete.** Three new books, `engine/rules/shape.lisp`,
  `dispatch.lisp` and `arity.lisp`, certify under `make -C engine check`
  in 4.5 s, 7.4 s and 3.9 s. The gate has 23 books (20 before), no
  `skip-proofs`, no `defaxiom`, no trust tag.
- **Every rule function has its lemmas**: 210 of 212 a shape lemma, 201
  a length lemma and a forward-chaining lemma; the other 11 are by hand
  (nine take their operand count from a type, two work on a whole block).
- **The machine's table is `STEP`'s order**: on a list of values followed
  by one instruction of head `kw`, `try-rules` over the pure (read, own)
  rules that `rules-for` gives for `kw` is `STEP_PURE` (`STEP_READ/SPLIT`,
  the rest of `STEP`) on that list. Three theorems, for a symbolic `kw`.
- **The exit statements certify**: `STEP/R-PURE` and `STEP/R-READ` return
  `nil` on `v ++ (i) ++ r` for `nop`, `binop` and `local.get` when `r` or
  the extra values are not empty: 254 to 5,098 prover steps each.
- **Both risks of plan2.md §5 that V1 decides are settled.** Row 1: no
  proof over a symbolic `v ++ (i) ++ r` is large (the largest, 31,304
  steps). Row 4: the type-dependent arities of `block`, `loop`,
  `try_table`, `throw` and `call_ref` equal the rule's own count; no
  change to `redex-arity`.
- **One finding about the machine, not a bug of a reachable state**: the
  `call_ref` rules accept a reference `(:ref.func_addr a)` by its shape,
  and `redex-arity` returns `nil` when `a` is not a natural number. The
  arity lemmas for a function reference carry the hypothesis `(natp a)`,
  which V2 has to get from the invariant (§5).

## Findings

All prover steps are from the certification output
(`data/v1-dispatch/measure.txt`).

### 1. `first-nonval` and `redex-shape-p` (`shape.lisp`)

- `(first-nonval l)`: the index of the first element that is not a
  value. `step/prefix7-becomes-first-nonval` rewrites the specification's
  `STEP/PREFIX7` to it (446 steps), so a proof never needs that definition.
  On `v ++ (i) ++ r` with `v` values and `i` not a value it is `(len v)`
  (`first-nonval-of-append-of-vals-and-instr`).
- `(redex-shape-p kw l)`: `l` is not empty, every element but the last
  has the head of a value, the last has head `kw`. Facts: a list has one
  shape (`redex-shape-p-unique`); on `v ++ (i) ++ r` it is
  `(and (atom r) (equal (car i) kw))` (894 steps); the head of the
  element at `first-nonval` is `kw`, a value's, or there is none; no
  element has another head that is not a value's (`head-member`).
- `value-head-p` (of `rules/terminal.lisp`) is disabled in the header of
  the three books. Enabled, it is opened into ten equalities before any
  rule about it can fire.

### 2. Per rule function, generated (`shape.lisp`)

For a rule function `R` with opcode or administrative head `K` and a
fixed shape of `n` elements:

```lisp
(defthm <R>-FAILS-WHEN-NOT-SHAPE          ; 210 rules
  (implies (not (redex-shape-p K l)) (equal (R l) nil)))
(defthm <R>-FAILS-WHEN-NOT-LENGTH         ; 201 rules
  (implies (not (equal (len l) n)) (equal (R l) nil)))
(defthm <R>-SHAPE                         ; 201 rules, :forward-chaining
  (implies (R l) (and (redex-shape-p K l) (equal (len l) n))))
```

(`(R (list :|%;%| z l))` for a rule of `STEP_READ/SPLIT` or of `STEP`.)
`K` is from `rule-place`; `n` is read from the rule's body (the first
test `(equal (len <variable>) 'n)`), and the lemma fails if that reading
is wrong. Each proof runs in `minimal-theory`, the executable
counterparts, eight named rules and `R`, with a step limit of 100,000.
All 603 take 1.7 s of proof time. The rules on an administrative term
(`label-vals`, `br-label-*`, `frame-vals`, the handler rules) are of a
fixed shape, one element, and are among the 201.

### 3. The rules without a fixed shape (`shape.lisp`, `arity.lisp`)

- **Nine rules take a number of values from a type**: `block`, `loop`,
  `try_table`, `throw`, `struct.new`, `array.new_fixed` and three
  `call_ref` rules. Shape: each matches its values with a generated
  `MATCHnn` function; 41 of the 48 one-argument match functions accept
  value lists only (`VALS-P-WHEN-<MATCHnn>`, forward chaining; the seven
  others match types, instructions or catch clauses and are recorded in
  `*match-fns-not-values*`). The shape lemma then needs no hint:
  `redex-shape-p-of-vals-then-tail` is a rewrite rule whose free variable
  `n` is bound by the forward-chained `(vals-p (take n l))`. The spike
  used a `:use` there.
- **Their operand count** is stated against the machine, in `arity.lisp`
  (§4).
- **Two rules work on a whole block**, `trap-instrs` and
  `throw_ref-instrs`. Two facts each: the rule fails unless the element at
  `first-nonval` has head `TRAP` (`REF.EXN_ADDR` or `THROW_REF`), and it
  fails unless some element has head `TRAP` (`THROW_REF`). The first is
  for `v ++ (i) ++ r`, the second for a redex, where a malformed element
  with a value's head may stand at `first-nonval`.

### 4. Operand counts against `redex-arity` (`arity.lisp`)

```lisp
(defthm <R>-ARITY
  (implies (R l)
           (equal (redex-arity (nth (+ -1 (len l)) l) z vals)
                  (+ -1 (len l)))))
```

- 81 generated, from `<R>-SHAPE` and one rule about `redex-arity` on the
  last element of a redex (`fixed-arity`: `redex-arity` on the head alone,
  for the heads whose arity is a constant).
- 8 by hand: `block`, `loop`, `try_table` (2,471 to 2,723 steps), `throw`
  (2,738), `call_ref-null` (2,337), `call_ref-func` (314,430) and the two
  host rules (326,226 and 323,643). `redex-arity` is opened and computes
  the count with the same function of the specification as the rule
  (`$blocktype_`, `expand` of the tag's or the function's type).
- **Hypotheses of the `call_ref` lemmas** (they are lemma hypotheses, not
  yet hypotheses of a theorem of plan2.md §1):
  - `(equal (car vals) (nth (+ -2 (len l)) l))`, all four: `redex-arity`
    reads the reference from the operand stack, so its top has to be the
    element before `call_ref`. True in `op-step` by construction.
  - `(natp (cadr (nth (+ -2 (len l)) l)))`, the three with a function
    reference: see §5.
  - `call_ref-func` is stated for a state `(list :|%;%| s f)`. The rule
    reads the store with `($s z)`, which is `(cadr z)` only for a state of
    that shape. The machine's `ms-z` has it.
- **Census**: 89 rules have an arity lemma. The 123 without: 97 rules of
  the 51 heads `redex-arity` does not support (vectors, structs, arrays,
  `ref.test`, `ref.i31`, `i31.get`, `br_on_cast*`, the conversions,
  `table.size`, `return_call*`; list in `measure.txt`), and 26 rules on an
  administrative term or a block. The book fails if the set differs. All
  37 rules the demos apply (V0) have theirs, but the six on an
  administrative term, which have a shape lemma of one element.
- So V5 item 4 has its table: the opcodes with an arity lemma are the
  opcodes for which `redex-arity` is not `nil`.

### 5. `(:ref.func_addr a)` with `a` not a natural number

The rules `call_ref-func` and `call_ref-hostfunc-*` match the reference by
shape: `(consp ref)`, head `:REF.FUNC_ADDR`, one argument. They test
`(< a (len funcs))` and take `(nth a funcs)`; for `a = -1` or `a` a symbol
both go through (`nth` of a non-natural is `car`). `redex-arity` asks
`(natp a)` and otherwise returns `nil`, and `op-step` then stops
`:unsupported`. So on such a state the specification may step and the
machine refuses. This is not a difference in a result: `:unsupported` is
not a result, and the reference is not a value (`funcaddr-p`), so a state
built from values does not have it. **For V2**: the operand-prefix lemma
for `call_ref` needs the top of the operand stack to be a value, from
`machine-ok`; if `machine-ok` does not say that operands are values, that
is the fact to add to the invariant.

### 6. The relations are the machine's table (`dispatch.lisp`)

- `*pure-rule-fns*` (79), `*read-rule-fns*` (103), `*own-rule-fns*` (30):
  the rule functions of `STEP_PURE`, `STEP_READ/SPLIT` and `STEP` itself,
  read from their bodies. `(pure-rules l)`, `(read-rules l)`,
  `(own-rules l)` keep the members of one group, in the order of `l`.
- `(head-place kw)`: `(:entry :l)`, `(:entry :h)`, `(:entry :f)` for the
  three administrative heads, `(:op kw)` otherwise.
- `(step-own c)`: the part of `STEP`'s body after its two relations and
  four context rules, read from the body. `step-opener-with-step-own`
  (disabled, 571 steps) opens `STEP` into six calls and `step-own`; a
  `theory-invariant` keeps it apart from `step-opener`.
- Per relation and per head with a rule there, generated (104 lemmas: 49
  pure, 39 read, 16 own):

  ```lisp
  (defthm STEP_PURE-OF-REDEX-BINOP        ; 24,941 steps
    (implies (redex-shape-p :binop l)
             (equal (w3t::step_pure l)
                    (or (w3t::step_pure/r-binop-val l)
                        (w3t::step_pure/r-binop-trap l)))))
  ```

  and `<relation>-OF-REDEX-WITHOUT-RULE` for every other head (24,869,
  38,931 and 9,153 steps). The relation function is opened; each of its
  rule calls is rewritten to `nil` by its shape lemma.
- The three theorems, for a symbolic `kw`:

  ```lisp
  (defthm try-rules-of-pure-rules         ; 293,675 steps
    (implies (and (redex-shape-p kw l)
                  (not (equal kw :trap))
                  (equal place (head-place kw)))
             (equal (try-rules (pure-rules (rules-for place)) z l)
                    (if (w3t::step_pure l)
                        (mv t z (car (w3t::step_pure l)))
                      (mv nil z nil)))))
  ```

  `try-rules-of-read-rules` (995,909 steps; `kw` not `:throw_ref`; the
  relation is `(w3t::step_read/split (list :|%;%| z l))`) and
  `try-rules-of-own-rules` (411,019 steps; no exclusion; the result is
  the state and the instructions of `(car (step-own ...))`, with the
  machine's accessors as `apply-rule` writes them). Proof: `:cases` on
  `kw` being one of the 106 heads of the table; a known head computes
  `rules-for` and uses its generated lemma; an unknown one has no rules
  (`rules-for-of-head-place-when-not-known`).
- `try-rules-of-rules-for` (disabled, 6,536 steps): `try-rules` over
  `(rules-for place)` is `try-rules` over its pure rules, then its read
  rules, then its own rules. From `rules-for-is-pure-read-own`, which
  holds for every entry of `*rule-places*` by computation.
- **The two exclusions are the two block rules.** On a redex of head
  `TRAP` with values before it `trap-instrs` fires, and it is no rule of
  `(:op :trap)`; the same for `throw_ref-instrs` and `THROW_REF`. The
  machine takes those states to `anyprefix-step` or `exit-step` (V4).
  `throw_ref-null` is a read rule of `(:op :throw_ref)`, so it is outside
  `try-rules-of-read-rules`: V4 item 3 proves it by hand, as planned.

### 7. `v ++ (i) ++ r` (`dispatch.lisp`)

| Lemma | Says | Prover steps |
|---|---|---|
| `step_pure-of-vals-instr-rest` | `r` not empty, `i` not a value and not `TRAP`: no pure rule fires | 21,442 |
| `step_read/split-of-vals-instr-rest` | the same for the read rules, `i` not `THROW_REF` | 26,496 |
| `step-own-of-vals-instr-rest` | the same for `STEP`'s own rules | 6,793 |
| `step_pure-of-vals-instr-without-rule` | any `r`: no pure rule fires when the head of `i` has none | 25,392 |
| `step_read/split-of-vals-instr-without-rule` | the same for the read rules | 31,304 |
| `step/r-pure-of-vals-instr-rest`, `step/r-read-of-vals-instr-rest` | `Step/pure` and `Step/read` on `(z; v ++ (i) ++ r)`, `r` not empty | 274, 280 |

The exit statements, each for values `v`, any `z`, any `i` with the head
named:

| Theorem | Hypothesis besides `(vals-p v)` | Prover steps |
|---|---|---|
| `step/r-pure-of-vals-nop-rest` | `(or (consp v) (consp r))` | 1,202 |
| `step/r-read-of-vals-nop-rest` | none | 260 |
| `step/r-pure-of-vals-binop-rest` | `(or (not (equal (len v) 2)) (consp r))` | 5,098 |
| `step/r-read-of-vals-binop-rest` | none | 260 |
| `step/r-pure-of-vals-local.get-rest` | none | 254 |
| `step/r-read-of-vals-local.get-rest` | `(or (consp v) (consp r))` | 967 |

Three have no hypothesis about the count: `nop` and `binop` have no read
rule, `local.get` no pure rule. The other three use one `:cases
((consp r))`: with `r` not empty the shape fails, with `r` empty the
length lemma of the instruction's rules does.

### 8. What failed first

Kept because V2 will meet the same.

- **A lemma that needs induction and has no `:induct`.**
  `redex-shape-p-of-append-of-vals-and-instr` with no hint ran 229 s to
  the step limit of 2,000,000 with no checkpoint (118 subgoals of
  `redex-shape-p-when-consp-cdr` against `cdr-of-append`). With
  `:induct (len v)` and the two opener rules disabled: 894 steps. A step
  limit bounds the steps, not the time of one that loops through large
  terms.
- **A statement that was false.** "The head of the element at
  `first-nonval` is `kw` or a value's" fails when every element is a
  value: there is no such element. Checkpoint:

  ```
  Subgoal *1/1.7'
  (IMPLIES (AND (CONSP L) (NOT (CONSP (CDR L))) (W3T::VAL-P (CAR L))
                (NOT (EQUAL (CAR (NTH 1 L)) (CAR (CAR L)))))
           (VALUE-HEAD-P (CAR (NTH 1 L))))
  ```

  Not a machine state; the lemma now says "is not `kw2`" for a `kw2` that
  is not `nil`, not `kw` and not a value's head.
- **A free variable bound by the wrong hypothesis.**
  `head-member-when-head-of-nth` with `(< (nfix n) (len l))` first never
  fired: the goal had `(< k (len l))`. With the hypothesis
  `(equal (car (nth n l)) kw)` first, `n` is bound from the goal's
  equality.
- **`(len l)` is replaced by its constant.** The first generic rule for
  the generated arity lemmas had the left side
  `(redex-arity (nth (+ -1 (len l)) l) z vals)`. Checkpoint of all 81:

  ```
  (IMPLIES (W3T::STEP_PURE/R-UNREACHABLE L)
           (EQUAL (REDEX-ARITY (NTH 0 L) Z VALS) 0))
  ```

  The forward-chained `(equal (len l) 1)` had rewritten `(len l)`. The
  rule is now stated for `(nth n l)` with the hypothesis
  `(equal (len l) (+ 1 n))`.
- **`call_ref-func` for any `z`.** Checkpoint: the hypotheses name
  `(W3T::$STORE Z)` and the conclusion `(cadr z)`. Stated for
  `(list :|%;%| s f)` (§4).
- **Two normal forms of the last element.** The `call_ref` rules write
  `(cadr (nthcdr (- (len l) 2) l))` and the lemma `(nth (+ -1 (len l)) l)`;
  the checkpoint ended in
  `(NOT (EQUAL (CAR (NTH (+ -1 (LEN L)) L)) :UNREACHABLE))`.
  `cadr-of-nthcdr` (in `typed-arity-theory`, disabled otherwise) joins
  them.

### 9. Practice (step2.md), where the books depart from it

- Three `:use` hints remain: `redex-arity-of-last-when-redex-shape-p`
  (two facts about the last element at `n` instead of `(+ -1 (len l))`),
  `try-rules-of-rules-for` (the fact it uses has its own left side on the
  right) and none in a generated lemma. Three `:cases` hints in the exit
  statements and one in each `try-rules-of-*-rules`.
- `engine/lib/lists.lisp` got six rules: `consp-of-nthcdr`,
  `len-when-not-consp`, `mv-nth-of-cons-and-constant`,
  `equal-of-constant-plus-and-constant` and `equal-of-sum-of-lens-and-0`
  (a length that is a sum, against a constant). Only `rules/step-basics`
  and the books after it include the library; they certify unchanged.
- Each generator prints one line per lemma (`SHAPE`, `LENGTH`, `FC`,
  `MATCH`, `REDEX`, `ARITY`), each lemma has its step limit, and each
  family ends with a census that fails the book.

## Open questions

- V2 needs the per-relation statement on the machine's own redex,
  `(rev-onto (take-n k vals) (list i))`; `redex-shape-p` of that term
  from `machine-ok` is V2's first lemma. Whether `machine-ok` says that
  the operands are values has not been read here (§5).
- For a head that `redex-arity` does not support and that has rules,
  `op-step` stops `:unsupported` because `k` is not a number. V5 item 4
  (the generated table) can take the heads from the arity census.

## Data

All under `data/v1-dispatch/`.

- `measure.sh`: reads the generator lines, the census lines, the prover
  steps of the named theorems and the certification times from
  `engine/rules/{shape,dispatch,arity}.cert.out`, and lists the demo
  rules of V0 without an arity lemma and the heads `redex-arity` does not
  support. `measure.txt`: its output. Regenerate at the repository root,
  inside `nix develop`, after `make -C engine check`:
  `sh plan/wasm-engine/notes/data/v1-dispatch/measure.sh > plan/wasm-engine/notes/data/v1-dispatch/measure.txt`.
