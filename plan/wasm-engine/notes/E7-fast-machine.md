# The fast machine: memory in an array, equal to the list machine at every step

- Milestone: E7 (Phase A done; speed for the slides done; Phase B in progress: per-rule, per-place, memory and fast-path lemmas proved; the step theorem is next)
- Date: 2026-11-16
- Repo commit: 9b37c94 plus this note's commit
- Status: draft
- Feeds engine plan: E7, E12 (the slides on the fast machine), E9
- Incorporated in engine plan: yes (E7, "Current state")

## Summary

- `engine/fast/fast.lisp`: the fast machine. Its state is a stobj whose
  fields are the list machine's, except that memory 0's bytes are in a byte
  array and the store holds an empty byte list. `fm->ms` puts the bytes
  back. Logic mode, guards verified.
- **It equals the list machine**: lockstep comparison at every step on the
  benchmarks (0 disagreements), and **differential test 3 over the whole
  spec-test-3 suite: 32,649 commands with equal final states, 0
  different** (24,726 more stop `:unsupported` on both, in equal states).
  Differential test 3 found one bug, now fixed: the memory fast paths
  assumed the store has one memory.
- **Memory no longer costs with its size**: the memory loop takes 58 to
  60 ms at 1, 16 and 64 pages (4,115 to 255,171 ms on the list machine).
- **Arithmetic and dispatch**: fast paths for the hottest instructions
  (binop step 0.55 to 0.16 us, local.get 0.37 to 0.08 us); counting loop
  51 ms (158 on the list machine).
- **The slides: 0.20 to 0.36 s each** (3.3 to 4.3 s on the list machine),
  7 of 7 identical to V8.
- **Proofs** (Phase B, no skip-proofs): `refine.lisp` (frame-safe rules per
  rule and per place, 60 of 103 places; the general fallback),
  `refine-mem.lisp` (all 19 memory rules), `refine-hot.lisp` (the six fast
  paths equal the general path). Left: the step parts and the theorem for
  `fast-step`.

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

### Logic mode, guards verified (Phase B, first step)

`fast.lisp` is now in logic mode with every guard of the machine verified
(certifies in 3.0 s); the code generators stay in program mode. The
spec's functions are reached through `ec-call`, as in the list machine;
the generated memory-rule versions are logic mode without verified guards
(their bodies are spec terms) and are called through `ec-call`; a write
into the array checks that the value is a byte (that the spec writes only
bytes is a Phase B obligation). Still equal to the list machine at every
step, 7 of 7 slides identical to V8 (`data/e7-fast/fasttest-logic.out`,
`slides-fast-logic.txt`). It is somewhat slower than the program-mode
version: count 88 ms (81), throw 147 ms (83), slides 0.40 to 0.85 s (0.33
to 0.69).

### Refinement, layers 1 to 3 (`engine/fast/refine.lisp`, 78 s)

- (1) The array as a list: `mem-to-list` is the stobj's array field.
- The fast store invariant `fast-store-ok`: memory 0's bytes are empty in
  the store, there is a memory, and the store has all its fields
  (`store-fields-p`). Every frame-safe step rule keeps it (generated
  `*-KEEPS-FAST-STORE`, all prove after record lemmas at the level of
  `%GET-FIELD`/`%PUT-FIELD`; `global.set` and `throw` needed them).
- (2) Per rule: a frame-safe rule on the full store equals the rule on the
  fast store, with the bytes put back into the result (`*-ON-FAST-STORE`,
  from the frame lemmas).
- (3) Per place: for each of the **60 of 103 places** whose rules are all
  frame-safe, `TRY-RULES` of the list machine on the full store equals the
  generated `FAST-TRY-*` function on the fast store with the bytes put back,
  and the place function leaves the array unchanged
  (`FAST-TRY-*-REFINES`, `*-KEEPS-ARRAY`).
- (2') The general fallback (`fast-apply-rule-fallback`, one theorem for
  every rule with no fast path): the rule on the full store agrees with the
  fast machine's fallback (bytes copied out of the array, the result's bytes
  copied back), under three hypotheses about the rule: its result is a
  configuration whose memory 0 has a byte list (`fallback-result-ok`, to be
  discharged in layer 4), it fails with the state unchanged
  (`rule-fails-plainly`), and it fires only when its opcode is in the redex
  (`rule-needs-opcode`, which makes the fast machine's precheck sound). The
  last two are proved per rule for **87 of the 90** fallback rules; not yet
  for `call_ref` of a host function (2 rules; the engine has no host
  functions) and `return_call_ref` inside a frame (1), whose opcode lies
  deeper in the redex. Book time 104 s.
- **Memory (`engine/fast/refine-mem.lisp`, 49 s): all 16 memory rules.**
  With one memory (`one-memory-p`), the fast store invariant, and memory 0
  a record (`mem0-record-p`):
  - the 12 read rules (load, memory.size, memory.fill, memory.copy): the
    generated fast version on the fast store and the array **equals** the
    spec's rule on the full store (`*-FAST-IS-FULL`);
  - the 4 store rules: `fast-apply-rule` agrees with the rule on the full
    store, the array being memory 0's bytes afterwards
    (`*-FAST-REFINES`).
  Two changes to the machine made this provable without facts about the
  spec's byte encodings: `mem-window` reads a non-natural address as 0,
  as `nthcdr` does; and a store is written into the array only when its
  bytes are a byte list of the length `$with_mem` replaces and fit in
  memory, otherwise the exact fallback runs (at most 8 bytes are checked
  per store). Lockstep: still 0 disagreements; slides 7 of 7 identical to
  V8; memloop still independent of memory size (81 ms at 64 pages).
- Remaining for the places: the 5 memory places as a whole (from the rule
  lemmas, as for the other places) (load, store, memory.size,
  memory.fill, memory.copy) and 38 that use the general fallback (tables,
  GC structs and arrays, SIMD, memory.init, memory.grow, return_call).
  The general fallback below covers the 38.

### Speed: memory.init and fast paths for the hottest instructions

Profile and counts of the slide deck on the fast machine
(`data/e7-fast/slides-profile.txt`, `slides-histogram.txt`):

- **memory.init took the slow fallback**, which copies the whole memory
  out of the array and back: 1,621 times each for memory.init-oob, -zero
  and -succ during instantiation (the deck and the font are copied into
  memory a byte at a time), 7.7 GB allocated, about 5 of the 9.8 s of the
  deck. Like memory.fill they read only the memory's length, so they now
  have generated fast versions (19 memory rules in all). The deck: 9.8 s to
  4.4 s.
- **Instruction counts** (13,332,316 steps for the deck): value pushes
  45.2%, local.get 14.5, binop 11.7, local.set 5.6, br_if 4.2, relop 3.9,
  label exits 3.8, local.tee 3.1.
- **Fast paths** (`fast-hot-step`): for local.get, local.set, local.tee,
  binop, relop and br_if, the step is computed directly from the stack and
  the frame with the same spec functions (`$local`, `$with_local`,
  `$binop_`, `$relop_`, `val-p`) when the operands have the rule's shape,
  and gives the state the general path gives; otherwise the general path
  runs. Value pushes test the common case `(:const (:i32) c)` first
  (`i32-const-p`, proved to imply `val-p`).

Per step (`micro-fast`, 10^6 calls each), before and after:

| Step | General path | Fast path |
|---|---|---|
| binop (i32.sub) | 0.554 us | 0.161 us |
| local.get | 0.367 | 0.083 |
| local.set | 0.504 | 0.145 |
| relop | 0.407 | 0.142 |
| br_if | 0.256 | 0.067 |
| value push | 0.129 | 0.062 |

Runs (`data/e7-fast/fasttest-hot.out`, after the fix below): count 51 ms
(88), memloop 58 to 60 ms at 1 to 64 pages (81), nested 78 ms (87), throw
132 ms (147). **Slides: 0.20 to 0.36 s each** (`slides-fast-hot.txt`;
0.39 to 0.81 before; 3.3 to 4.3 s on the list machine), 7 of 7 identical
to V8. Lockstep: 0 disagreements.

**Proved** (`engine/fast/refine-hot.lisp`, 5.6 s): for each of the six,
when the fast path handles the instruction, its state is the state
`fast-op-step` gives (`HOT-LOCAL.GET` ... `HOT-BR_IF`, hypotheses: `fmp`,
status `:run`, the instruction at the head of the instruction list); and
`fast-val-p` is `value-instr-p`.

### A bug found by differential test 3: several memories

`engine/fast/difftest3-one.lsp` runs every action command of a spec-test-3
script on both machines from the same configuration and compares the final
states, memory included. On `local_tee` it found 4 differences: stores in
a module whose memory is the store's second memory (the script's earlier
module left one). The memory fast paths read and write the array, which
holds the store's memory 0, without checking that the instruction's memory
is memory 0. The refinement lemmas had this as a hypothesis
(`one-memory-p`); the machine now checks it (`fast-one-memory-p`, proved
equal to `one-memory-p`) and otherwise runs the exact fallback, which is
right for any number of memories. The bug dates from Phase A; the slides
and the benchmarks have one module and never met it.

### Differential test 3 over the spec suite (`data/e7-fast/difftest3/`)

`engine/fast/difftest3-all.sh` (8 jobs, 900 s per script) over the 258
spec-test-3 scripts, after the fix: 32,649 commands with equal final
states, 24,726 that stop `:unsupported` on both machines in equal states
(instructions the list machine does not have: floats, SIMD, GC), 13 out
of fuel on both in equal states, 11 not invocations, **0 different**.
251 scripts finished; 7 were stopped at 900 s (memory.fill, memory.copy,
memory.grow and call_indirect scripts, where the list machine is slow on
large memories), every command they ran agreeing. Per script:
`per-script.txt`; every result line: `D3-LINES.txt.gz`.

## Open questions

- The step theorem needs the fallback's result to keep memory 0 a byte
  list (`fallback-result-ok`). Plan: the machine checks it and refuses
  (`:unsupported`) otherwise, so that the theorem reads "when the fast
  machine does not refuse, its step is the list machine's step".
- The per-rule opcode facts for 3 rarely used rules (`call_ref` of a host
  function, `return_call_ref` in a frame).

## Data

`engine/fast/fast.lisp`, `refine.lisp`, `refine-mem.lisp`,
`refine-hot.lisp`, `fasttest.lsp`, `fasttest-run.lsp`, `micro-fast.lsp`,
`difftest3-one.lsp`, `difftest3-all.sh`; `data/e7-fast/`: `fasttest.out`,
`fasttest-logic.out`, `fasttest-hot.out`, `micro-fast.out`,
`slides-fast.txt`, `slides-fast-logic.txt`, `slides-fast-hot.txt`,
`slides-histogram.txt` (and `.lsp`), `slides-profile.lsp`, `difftest3/`.
