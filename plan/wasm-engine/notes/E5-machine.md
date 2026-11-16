# Machine design: a context-stack machine that mirrors the spec's intermediate forms

- Milestone: E5 (all three items)
- Date: 2026-11-15
- Repo commit: 78d1584 plus the E2 commit (rule functions exist: `STEP_PURE/R-<RULE-ID>`)
- Status: final (headless; the user reviews when they choose, see "For the user to review")
- Feeds engine plan: §3 (architecture), E3 (theorem shape), E6, E7, E8, E9, E11, §5 (risks)
- Incorporated in engine plan: yes (§3, E6, E7, "Current state")

## Summary

- The machine keeps the spec's own data (store, frame, values, instruction
  trees) and replaces only the *search*: the evaluation context is an
  explicit control stack, the operands are a separate stack, and the next
  rule is chosen by a `case` on the head instruction.
- There is no flat bytecode and no program counter. A continuation is a
  pointer into the instruction tree (the `cdr` of a body). A label entry
  stores where a branch goes, so branch targets are resolved when the block
  is entered.
- Every machine step is 0 or 1 spec steps, except bulk memory
  (`memory.fill`, `memory.copy`), which is one machine step for a number of
  spec steps that the clock function gives. Branches, returns, traps and
  exceptions unwind one control entry per machine step, as the spec does.
- The fast machine is the same step function over an abstract stobj
  (`defabsstobj`), not a second definition. The refinement theorem of E7
  becomes the correspondence obligations of about 30 primitives.
- Host calls: the list machine calls the spec's `$hostcall`, so its theorem
  holds for every host. The fast host layer is installed under a trust tag
  in the view driver only.

## Findings

### What carries over from the prior art

- **x86isa** (ACL2 books `projects/x86isa`): one definition of the machine
  over an abstract stobj; the logical state is a simple object, the
  executable state is arrays. Proofs see only the logical side. Carried
  over: `defabsstobj`, a small set of primitives with their correspondence
  lemmas, `mbe` for fast paths of arithmetic. Not carried over: its
  "app-view" split, which has no counterpart here.
- **WasmRef-Isabelle** (Watt et al., a fast interpreter refined from the
  WasmCert-Isabelle semantics): the proved interpreter works on an explicit
  stack of frames and labels instead of nested administrative terms, and is
  connected to the semantics by a function that rebuilds the nested term.
  Carried over: exactly this shape (`abs` below). Not carried over: its
  monadic heap layer; ACL2 has stobjs for that.
- Neither was re-read in this session (no network fetch was made). The two
  paragraphs above are from memory of the papers. A session that depends on
  a detail of either must read the source first.

### State

List machine state `ms` (a plain ACL2 object; field names are the
primitives of E7):

| Field | Content |
|---|---|
| `store` | the spec store `s`, unchanged representation |
| `frame` | the spec frame record `f` of the innermost activation (`LOCALS`, `MODULE`) |
| `vals` | operand stack of the innermost block, top first; every element satisfies `VAL-P` |
| `is` | the instructions still to run in the innermost block (a tail of a body in the module, or a short list the machine built) |
| `ctrl` | control stack, innermost first; entries below |
| `status` | `:run`, `:done`, `:trap`, `:stuck`, `:unsupported` |

Control entries. `v` and `r` are the operand stack and the continuation of
the enclosing block, saved when the entry was pushed:

| Entry | Spec term it stands for |
|---|---|
| `(:L n is0 v r)` | `LABEL_ n {is0} ...`; `is0` is `nil` for a block and the one-element list of the loop instruction for a loop |
| `(:H n catches v r)` | `HANDLER_ n {catches} ...` |
| `(:F n f v r)` | `FRAME_ n {frame} ...`; `f` is the caller's frame, `frame` is the current one |

### The abstraction function

```
abs(ms):
  cur := rev(vals) ++ is ;  fr := frame
  for e in ctrl, innermost first:
    (:L n is0 v r)     cur := rev(v) ++ [ (LABEL_ n is0 cur) ] ++ r
    (:H n catches v r) cur := rev(v) ++ [ (HANDLER_ n catches cur) ] ++ r
    (:F n f v r)       cur := rev(v) ++ [ (FRAME_ n fr cur) ] ++ r ;  fr := f
  return (:|%;%| (:|%;%| store fr) cur)
```

`abs` runs only in the differential tests (E6) and in proofs.

### The step function

`i` is the head of `is`. "Rule" is the spec rule the step corresponds to;
its function is `<REL>/R-<RULE-ID>` after E2.

| Case | Action | Rule | Clock |
|---|---|---|---|
| `is` empty, `ctrl` empty | `status := :done` | (terminal) | 0 |
| `is` empty, top `(:L n is0 v r)` | `vals := vals ++ v; is := r`; pop | `label-vals` | 1 |
| `is` empty, top `(:H ...)` | the same | `handler-vals` | 1 |
| `is` empty, top `(:F n f v r)` | needs `len vals = n`; `vals := vals ++ v; is := r; frame := f`; pop | `frame-vals` | 1 |
| `i` is a value | `vals := i . vals; is := cdr is` | none (`abs` is unchanged) | 0 |
| `TRAP`, `vals` or `cdr is` not empty | `vals := nil; is := (TRAP)` | `trap-instrs` | 1 |
| `TRAP` alone, `ctrl` empty | `status := :trap` | (terminal) | 0 |
| `TRAP` alone, top entry `(_ ... v r)` | `vals := v; is := TRAP . r`; pop (frame: restore `f`) | `trap-label`, `trap-handler`, `trap-frame` | 1 |
| `(BR 0)`, top `(:L n is0 v r)` | `vals := take n vals ++ v; is := is0 ++ r`; pop | `br-label-zero` | 1 |
| `(BR l+1)`, top `(:L ...)` | `vals := vals ++ v; is := (BR l) . r`; pop | `br-label-succ` | 1 |
| `(BR l)`, top `(:H ...)` | `vals := vals ++ v; is := (BR l) . r`; pop | `br-handler` | 1 |
| `RETURN`, top `:L` or `:H` | `vals := vals ++ v; is := RETURN . r`; pop | `return-label`, `return-handler` | 1 |
| `RETURN`, top `(:F n f v r)` | `vals := take n vals ++ v; is := r; frame := f`; pop | `return-frame` | 1 |
| `(BLOCK bt body)` | `(m n) := $blocktype_`; push `(:L n nil (nthcdr m vals) (cdr is))`; `vals := take m vals; is := body` | `Step_read/block` | 1 |
| `(LOOP bt body)` | the same with `(:L m (list i) ...)` | `Step_read/loop` | 1 |
| `(TRY_TABLE bt catches body)` | push `(:H n catches (nthcdr m vals) (cdr is))`, then `(:L n nil nil nil)`; `vals := take m vals; is := body` | `Step_read/try_table` | 1 |
| `(IFELSE bt i1 i2)` | pop `c`; `is := (BLOCK bt i1 or i2) . cdr is` | `if-true`, `if-false` | 1 |
| `(BR_IF l)`, `(BR_TABLE ...)` | `is := (BR l') . cdr is`, or `cdr is` | `br_if-*`, `br_table-*` | 1 |
| `(CALL x)` | `is := (REF.FUNC_ADDR a) (CALL_REF tu) . cdr is` | `Step_read/call` | 1 |
| `(CALL_INDIRECT x tu)` | `is := (TABLE.GET x) (REF.CAST (REF NULL tu)) (CALL_REF tu) . cdr is` | `call_indirect` | 1 |
| `(CALL_REF tu)`, top value a function address | push `(:F m frame (rest of vals) (cdr is))`, then `(:L m nil nil nil)`; `frame :=` new frame; `vals := nil; is := body` | `Step/call_ref-func` | 1 |
| `(CALL_REF tu)`, host function | `$hostcall`; results onto `vals` | `Step/call_ref-hostfunc-res` | 1 |
| `(THROW x)` | allocate the exception in `store` as the rule does; `is := (REF.EXN_ADDR a) THROW_REF . cdr is` | `Step/throw` | 1 |
| `THROW_REF`, more than the reference on `vals`, or `cdr is` not empty | `vals := (ref); is := (THROW_REF)` | `throw_ref-instrs` | 1 |
| `THROW_REF` alone, top `:L` or `:F` | `vals := ref . v; is := THROW_REF . r`; pop | `throw_ref-label`, `throw_ref-frame` | 1 |
| `THROW_REF` alone, top `(:H n catches v r)` | no clause: pop as above (`handler-empty`). First clause matches: `vals := fields ++ v; is := (BR l) . r`; pop (`handler-catch`, `-catch_ref`, `-catch_all`, `-catch_all_ref`). Else replace the entry's `catches` by its `cdr` (`handler-next`) | as named | 1 |
| numeric, local, global, table, load, store | pop operands, call the spec's function (`$binop_`, `$with_local`, ...), push the result or put `TRAP` at the head of `is` | the rule of the instruction | 1 |
| `MEMORY.FILL`, `MEMORY.COPY` | the whole range in one step | `memory.fill-*`, `memory.copy-*`, and the `store`/`load` rules they expand to | from the clock function, by induction on the length |
| anything else | `status := :unsupported` | | |

A case whose operands are missing or have the wrong tag gives
`status := :stuck` (D2, checked engine).

The actions in this table were written from the rule names and from
knowledge of the spec source, not by reading each generated rule
function. Differential test 1 of E6 (`abs` after every machine step
against the spec stepped `clock` times) is the check; a row that is wrong
fails there.

**Why the machine mirrors the intermediate forms.** `call` could build the
frame directly, and `br 2` could pop three entries at once. Then one machine
step would be several spec steps across context levels, and each such
lemma would need its own induction on the control stack. With the table
above, one lemma per rule and one context lemma are enough. The cost is a
few conses per call and one machine step per unwound level. A fused step
can be added later as an optimisation proved against this machine.

### What "pre-decoding" becomes

The plan asked for resolved branch targets, stored block arities and
handler tables.

- **Branch targets**: a label entry holds `is0` and `r`, which are pointers
  into the instruction tree. No table is needed.
- **Handler tables**: the `:H` entry holds the `catches` list of the
  instruction itself.
- **Block arities**: the list machine calls `$blocktype_` at every block
  entry. If E7 measures this as a cost, the loader wraps each block
  instruction once with its `(m n)` and `abs` erases the wrapper; the
  invariant then says that the stored pair equals `$blocktype_` for the
  frame's module. This is an E7 item only if the profile asks for it.

### The invariant `machine-ok`

- `vals` and every saved `v` are true lists of `VAL-P` objects.
- `is` and every saved `r` and `is0` are true lists.
- Every control entry has one of the three shapes; `n` is a natural number.
- Nothing about types. A checked machine gets stuck where the spec does.

The step function preserves it for every case. It is needed in the
simulation proof for one reason: the spec's `ctxt-instrs` rule takes the
instructions up to the first one that is not a value, and `abs` puts
`rev(vals)` in front, so the proof must know that these are values.

### The clock function

`clock(ms)` is the number in the table: 0 for a value push and for the
terminal cases, 1 for every other case except bulk memory. For
`MEMORY.FILL` with count `n` and `MEMORY.COPY` it is a closed form in `n`
that E8 reads off the rules (`fill-succ` expands to a `STORE` and a smaller
`MEMORY.FILL`); the lemma is by induction on `n`.

Steps with clock 0 do not change `abs`. They cannot repeat forever: each
one shortens `is`.

### How an exception unwinds

`THROW x` allocates the exception instance in the store exactly as
`Step/throw` does, so the two stores stay equal. `THROW_REF` then drops
the rest of the current block (`throw_ref-instrs`), and pops one control
entry per step. At a handler entry the clauses are tried in order, one per
step (`handler-next`). A matching clause turns the exception into a `BR`,
which unwinds like any branch. A handler entry is passed by `BR` and
`RETURN` in one step (`br-handler`, `return-handler`).

`try_table` pushes two entries, the handler and a label inside it, as the
rule produces `HANDLER_ n {catch*} (LABEL_ n {eps} ...)`.

### What the simulation proof has to show (input to E3, E4, E11)

For a state with `machine-ok` and `status = :run`:

1. clock 0: `abs(mstep ms) = abs(ms)`.
2. clock 1: `STEP(abs(ms)) = (list abs(mstep ms))`.
3. bulk memory: `STEPS` with fuel `clock(ms)` from `abs(ms)` passes through
   `abs(mstep ms)`.

`STEP` returns the result of the *first* rule function that fires. So (2)
needs, for every case, that the earlier rules do not fire. With one
function per rule this is a set of small lemmas of the kind "rule function
R returns `nil` unless the head instruction is K" (the dispatch lemmas of
E4). Three lemma families lift a redex to the whole configuration:

- **Operand prefix**: for an instruction that takes `k` operands, `STEP`
  on `v_j ... v_1 i` is `nil` for `j < k` and the rule's result for
  `j = k`. `ctxt-instrs` tries the longest value prefix first (config
  `:split "Step" "ctxt-instrs" :strategy :redex`), so this is the order in
  which the proof meets the cases.
- **`ctxt-instrs`**: a step of `v_k ... v_1 i` is a step of
  `vals ++ i ++ rest`.
- **`ctxt-label`, `ctxt-handler`, `ctxt-frame`**: a step inside the
  innermost entry is a step of the whole, by induction on `ctrl`. The
  generated size check in front of each recursive premise (`%SIZE` of the
  inner instructions against the outer) has to be discharged here; it is
  true because the inner list is a proper part of the outer term.

The statement is one direction only: what the machine computes, the spec
computes. When the machine says `:stuck`, nothing is claimed in the first
version. Proving that the spec is stuck too needs the failure of all 218
rules and is a later item.

### The fast machine (E7)

- One step function, written over primitives (`vals-push`, `vals-pop`,
  `local-get`, `mem-load-byte`, `ctrl-push`, ...). E6 defines the
  primitives on the list state. E7 adds a concrete stobj (operand stack as
  one array with a stack pointer, control stack as arrays, locals in the
  operand array, memory as a byte array, globals and tables as arrays) and
  a `defabsstobj` whose logical side is the E6 state. The step function is
  not rewritten.
- The saved `v` of an entry is a stack height in the concrete state, and
  `vals ++ v` is no work at all there.
- Values stay spec objects (`(:CONST (:I32) n)`) in the first version.
  Unboxed operands are a later refinement of the primitives.
- D6 holds in the logic: the step function calls `$binop_` and the other
  spec functions. Where the profile asks for it, a call is wrapped in
  `(mbe :logic (spec call) :exec (direct arithmetic))`. ACL2 checks the
  two equal when it verifies guards, so this is a proof and not a second
  implementation.

### Host calls

`Step/call_ref-hostfunc-res` calls `$hostcall(hf, s, val*)`, which is the
constrained function `%hostcall-hook`. The list machine calls the same
function on the same store, so its theorem holds for every host, as §3 of
the plan says.

In the fast machine the store is in the stobj. Calling the hook needs the
store as a spec object, and building it copies the whole memory (352 pages
for MuPDF). The design:

- The host primitive's logical side is the list machine's host step. Its
  proved executable side builds the store, calls the hook and writes the
  result back. It is correct and slow.
- For MuPDF, `engine/host/` replaces the executable side of that one
  primitive by functions that work on the stobj. The replacement needs a
  trust tag. It is made in the view driver, never in a book that the
  certify half of the litmus test counts.

### Hand simulations

Notation: `vals` top first; `·` is empty; `c5` is `(CONST I32 5)`.

**1. A loop with `br_if`.** Body `B` = `LOCAL.GET 0, c1, BINOP sub,
LOCAL.TEE 0, BR_IF 0`; local 0 starts at 2; `L` = `(LOOP bt B)`.

| # | Rule | Clock | `vals` | `is` | `ctrl` (innermost first) |
|---|---|---|---|---|---|
| 0 | | | · | `L` | · |
| 1 | `loop` | 1 | · | `B` | `(:L 0 (L) · ·)` |
| 2 | `local.get` | 1 | `c2` | `c1 BINOP LOCAL.TEE BR_IF` | same |
| 3 | value | 0 | `c1 c2` | `BINOP ...` | same |
| 4 | `binop-val` | 1 | `c1` | `LOCAL.TEE 0, BR_IF 0` | same |
| 5 | `local.tee` | 1 | `c1` | `c1, LOCAL.SET 0, BR_IF 0` | same |
| 6 | value | 0 | `c1 c1` | `LOCAL.SET 0, BR_IF 0` | same |
| 7 | `Step/local.set` | 1 | `c1` | `BR_IF 0` | same (frame: local 0 = 1) |
| 8 | `br_if-true` | 1 | · | `BR 0` | same |
| 9 | `br-label-zero` | 1 | · | `L` | · |
| 10.. | as 1 to 7 with local 0 = 0 | | `c0` | `BR_IF 0` | `(:L 0 (L) · ·)` |
| 17 | `br_if-false` | 1 | · | · | same |
| 18 | `label-vals` | 1 | · | · | · |
| 19 | terminal | 0 | `status = :done` | | |

`abs` at row 8: `(LABEL_ 0 (L) (BR 0))`, which `br-label-zero` rewrites to
`L`, the `abs` of row 9. In step 4 `STEP` reaches the redex through
`ctxt-label` then `ctxt-instrs` (prefix `c1 c2`, nothing in front, the
rest behind).

**2. A call that returns.** Caller `c7, CALL g, DROP`; `g` has one
parameter, one result, body `LOCAL.GET 0, RETURN`. `F0` is the caller's
frame.

| # | Rule | Clock | `vals` | `is` | `ctrl` |
|---|---|---|---|---|---|
| 0 | | | · | `c7, CALL g, DROP` | · |
| 1 | value | 0 | `c7` | `CALL g, DROP` | · |
| 2 | `call` | 1 | `c7` | `ref_a, CALL_REF tu, DROP` | · |
| 3 | value | 0 | `ref_a c7` | `CALL_REF tu, DROP` | · |
| 4 | `call_ref-func` | 1 | · | `LOCAL.GET 0, RETURN` | `(:L 1 · · ·) (:F 1 F0 · (DROP))` |
| 5 | `local.get` | 1 | `c7` | `RETURN` | same |
| 6 | `return-label` | 1 | `c7` | `RETURN` | `(:F 1 F0 · (DROP))` |
| 7 | `return-frame` | 1 | `c7` | `DROP` | · (frame `F0`) |
| 8 | `drop` | 1 | · | · | · |

`abs` at row 4: `(FRAME_ 1 Fg (LABEL_ 1 () LOCAL.GET 0, RETURN)), DROP`
with the outer frame `F0`.

**3. A trap inside two nested blocks.** `(BLOCK (BLOCK c1, c0, BINOP
div_u, NOP), NOP), NOP`, both blocks with no parameters or results.

| # | Rule | Clock | `vals` | `is` | `ctrl` |
|---|---|---|---|---|---|
| 0..2 | `block`, `block` | 1, 1 | · | `c1, c0, BINOP, NOP` | `(:L 0 · · (NOP)) (:L 0 · · (NOP))` |
| 3, 4 | value, value | 0, 0 | `c0 c1` | `BINOP, NOP` | same |
| 5 | `binop-trap` | 1 | · | `TRAP, NOP` | same |
| 6 | `trap-instrs` | 1 | · | `TRAP` | same |
| 7 | `trap-label` | 1 | · | `TRAP, NOP` | `(:L 0 · · (NOP))` |
| 8 | `trap-instrs` | 1 | · | `TRAP` | same |
| 9 | `trap-label` | 1 | · | `TRAP, NOP` | · |
| 10 | `trap-instrs` | 1 | · | `TRAP` | · |
| 11 | terminal | 0 | `status = :trap` | | |

**4. A `throw` caught two frames up.** `main`: `(TRY_TABLE bt ((CATCH x
0)) CALL f), NOP` where `bt` has no parameters and the results of tag `x`
(one `i32`); `f`: `CALL g`; `g`: `c9, THROW x, NOP`.

| # | Rule | Clock | `vals` | `is` | `ctrl` |
|---|---|---|---|---|---|
| 1 | `try_table` | 1 | · | `CALL f` | `(:L 1 · · ·) (:H 1 (CATCH x 0) · (NOP))` |
| 2..4 | `call`, value, `call_ref-func` | 1, 0, 1 | · | `CALL g` | `(:L 0 ...) (:F 0 Fm · ·)` on top |
| 5..7 | the same for `g` | 1, 0, 1 | · | `c9, THROW x, NOP` | `(:L 0 ...) (:F 0 Ff · ·)` on top |
| 8 | value | 0 | `c9` | `THROW x, NOP` | same |
| 9 | `Step/throw` | 1 | · | `exn_a, THROW_REF, NOP` | same; the store has the new exception |
| 10 | value | 0 | `exn_a` | `THROW_REF, NOP` | same |
| 11 | `throw_ref-instrs` | 1 | `exn_a` | `THROW_REF` | same |
| 12, 13 | `throw_ref-label`, `throw_ref-frame` | 1, 1 | `exn_a` | `THROW_REF` | `g`'s two entries gone |
| 14, 15 | the same for `f` | 1, 1 | `exn_a` | `THROW_REF` | `(:L 1 · · ·) (:H 1 (CATCH x 0) · (NOP))` |
| 16 | `throw_ref-label` | 1 | `exn_a` | `THROW_REF` | `(:H 1 (CATCH x 0) · (NOP))` |
| 17 | `handler-catch` | 1 | `c9` | `BR 0, NOP` | · |

Row 17 leaves `BR 0` with no label around it: in a real module the
`try_table` sits inside the block that `CATCH x 0` targets, and the branch
continues as in simulation 1. Rows 12 to 15 assume that nothing follows
the calls in `f` and `g`; if something did, a `throw_ref-instrs` step
comes first at each level, as in row 11.

## Alternatives rejected

| Alternative | Why not |
|---|---|
| Flat bytecode with a program counter | `abs` would need a decompiler from a `pc` to the remaining instruction tree, and the proof would need the correctness of the layout. In Lisp a tail of a list is already a constant-time pointer, so the flat form buys only memory locality. To be reconsidered only if the E7 rate fails the go/no-go |
| One machine step for a whole `br l`, `return`, trap or call | Each needs its own induction on the control stack. The unfused machine needs one context lemma for all. A fused step can be proved against this machine later |
| Two step functions (list and stobj) and a refinement theorem between them | Every change to the machine would be made twice and proved equal. `defabsstobj` moves the proof to the primitives, which change rarely |
| The machine re-implements arithmetic with its own proofs | D6. `mbe` gives the speed where it is needed, checked by guard verification |
| An unchecked machine | D2 |

## For the user to review

Nothing here blocks a headless session. Two points touch what is trusted,
so they are named:

1. The fast host layer is installed under a trust tag in the view driver
   (section "Host calls"). The plan already lists the host functions as
   trusted; this says how that trust enters. The litmus output should
   print the tag.
2. The first theorem is one direction (the machine's results are the
   spec's). `:stuck` carries no claim.

## Open questions

- `Step/call_ref-hostfunc-div` (a host call that diverges): what the
  generated rule returns and what the machine does. E8, group H.
- The closed form of the clock for `memory.fill` and `memory.copy`. E8.
- Whether `$blocktype_` at block entry and boxed values are fast enough.
  E7 measures; no rate is claimed here.

## Data

None. The rule names are those of the rule functions in
`translate/gen/wasm-3.0/4_3-execution_instructions.lisp` after E2
(`grep -o "DEFUN STEP[A-Z_]*/R[0-9]*-[^ ]*"`).
