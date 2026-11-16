# The fast machine: memory in an array, equal to the list machine at every step

- Milestone: E7 (Phase A: the machine runs and is tested; the refinement theorem is next)
- Date: 2026-11-16
- Repo commit: 9b37c94 plus this note's commit
- Status: draft
- Feeds engine plan: E7, E12 (the slides on the fast machine), E9
- Incorporated in engine plan: yes (E7, "Current state")

## Summary

- `engine/fast/fast.lisp`: the fast machine. Its state is a stobj whose
  fields are the list machine's, except that memory 0's bytes are in a byte
  array and the store holds an empty byte list. `fm->ms` puts the bytes
  back.
- **It equals the list machine at every step**: lockstep comparison of
  `fm->ms` with `machine-step`, 0 disagreements in 8 runs (9,481 steps,
  with a trap and an uncaught exception), and equal final states on every
  timed run.
- **Memory no longer costs with its size**: the memory loop (10,000
  iterations) takes 133 to 226 ms at 1, 16 and 64 pages, against 4,108,
  65,615 and 257,322 ms on the list machine (30 to 1,140 times faster).
  Flat code is as fast as on the list machine (count 156 ms, nested 132 ms,
  throw 186 ms).
- **The slides: 0.7 to 1.4 s each on the fast machine** (3.3 to 4.3 s on
  the list machine), 7 of 7 still identical to V8. What is left is
  arithmetic and dispatch.
- Phase A is in program mode. The refinement theorem (`fm->ms` of a fast
  step is the list machine's step) is Phase B, from the lemmas of
  `frame.lisp` and `memory.lisp`.

## Findings

### How a rule is applied

| Rule | Path |
|---|---|
| The 16 memory rules of D5 (loads, stores, their bounds rules, `memory.size`, `memory.fill`, `memory.copy`) | a fast version **generated from the rule's own body** by `make-event`: the three forms in which a D5 memory rule touches memory, `(len bytes)`, `(take n (nthcdr a bytes))` and `($with_mem z x i j b)`, are replaced by the array's length, a read of `n` bytes, and a write request that the machine carries out |
| Pure rules, and rules with a frame lemma in `frame.lisp` (`*frame-safe-rules*`) | the rule function itself, on the store without bytes |
| Every other rule | the exact fallback: the bytes are copied into the store, the rule runs, the result's bytes are copied back |

The fast versions are the rule bodies with three substitutions, so the
equality proofs of Phase B are those of `memory.lisp` (window, splice,
length) after unfolding.

### Two performance bugs, found by the benchmarks

- The test "is this rule frame-safe" first recomputed each rule's opcode
  with string operations on every application. It is now a constant list
  made once at certification.
- `throw` was 12 times slower than on the list machine (2,112 ms), and at
  64 pages `throw 2000` took 83 s: the whole memory was copied on every
  iteration. A trace of the fallback showed one rule,
  `STEP_READ/SPLIT/R-RETURN_CALL_REF-FRAME-ADDR` (a tail-call rule outside
  D5, without a frame lemma), which is tried first when an exception leaves
  a function frame. It cannot match there, but the fallback copied the
  memory before finding out. The fallback is now entered only if the rule's
  opcode heads an instruction at the top level of the redex, or of the
  administrative term's body (every rule's pattern requires that). After
  it: `throw 3000` 186 ms.

### Rates (`data/e7-fast/fasttest.out`)

| Run | List machine | Fast machine |
|---|---|---|
| count 20,000 | 159 ms | 156 ms |
| memloop 10,000, 1 page | 4,108 ms | 138 ms |
| memloop 10,000, 16 pages | 65,615 ms | 136 ms |
| memloop 10,000, 64 pages | 257,322 ms | 226 ms |
| nested 5,000 | 135 ms | 132 ms |
| throw 3,000 | 183 ms | 186 ms |

The slides (`data/e7-fast/slides-fast.txt`, `slides-check.out`):

| Slide | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| Fast machine, ms | 901 | 675 | 1,208 | 678 | 1,366 | 1,417 | 1,183 |
| Identical to V8 | yes | yes | yes | yes | yes | yes | yes |

### Arithmetic and dispatch: where a step's time goes

A microbenchmark of the parts of one `i32.sub` step on the list machine
(1,000,000 calls each, `engine/fast/micro.lsp`):

| Part | us per call |
|---|---|
| `$BINOP_` alone (the spec's arithmetic, D6) | 0.046 |
| the rule function `STEP_PURE/R-BINOP-VAL` (pattern match + `$BINOP_`) | 0.129 |
| through `apply-rule` (a `case` over 212 rule names) | 0.283 |
| through `try-rules` and `rules-for` (an `assoc-equal` on list keys) | 0.494 |
| a whole `machine-step` (arity, value tests, redex, new state) | 0.860 |
| a whole `machine-step` of a value push | 0.179 |
| a whole `machine-step` of `local.get` | 0.791 |

So the arithmetic is about 5% of a step; dispatch is about 40%. A CPU
profile of the counting loop has 93% of its samples in `__bzero`
(allocation, about 500 bytes a spec step).

**Direct dispatch** (in `fast.lisp`): for every place (an opcode, an
entry kind, `:anyprefix`), one generated function calls that place's rules
in `STEP`'s order, each through its fixed path; a step is one `case` on
the opcode keyword. Result (`data/e7-fast/fasttest-dispatch.out`,
`slides-fast-dispatch.txt`):

| Run | List machine | Fast, generic dispatch | Fast, direct dispatch |
|---|---|---|---|
| count 20,000 | 165 ms | 156 ms | 81 ms |
| nested 5,000 | 132 ms | 132 ms | 62 ms |
| throw 3,000 | 181 ms | 186 ms | 83 ms |
| memloop 10,000, 64 pages | 259,937 ms | 226 ms | 70 ms |
| slides (7) | 3.3 to 4.3 s | 0.7 to 1.4 s | 0.33 to 0.69 s |

Lockstep: still 0 disagreements; slides: still 7 of 7 identical to V8. The
counting loop now runs about 2 million spec steps per second.

What is left in a step, in the order of the measurements: the value test
(`VAL-P` through `ec-call` on every value push), building the redex list
and the new operand stack, the rule's pattern match, and the store
updates. The next cuts are clean fast paths for the hottest instructions
(`local.get/set/tee`, `binop`, `relop`, `br_if`), each proved equal to its
rule (E4 item 3's clean forms), and guard-verified raw execution in Phase
B.

## Open questions

- Where the time of flat code goes (rule dispatch over 212 symbols, a new
  state each step, the redex list, the spec's numeric functions). Profile
  next.
- Phase B: the refinement theorem, and guards verified, so that the fast
  machine runs as raw Lisp in logic mode.
- The fallback's match test is an execution shortcut; Phase B needs it as a
  lemma (a rule fails when its opcode heads no top-level instruction).

## Data

`engine/fast/fast.lisp`, `fasttest.lsp`, `fasttest-run.lsp`;
`data/e7-fast/`: `fasttest.out`, `slides-fast.txt`, `slides-check.out`.
