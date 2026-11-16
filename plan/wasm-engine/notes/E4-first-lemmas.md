# First lemmas about the generated step functions: the approach works

- Milestone: E4 (a test before items 1, 3 and 4; no item is complete)
- Date: 2026-11-15
- Repo commit: this note's commit
- Status: draft
- Feeds engine plan: E4, E11, §5 (risks: "proofs about the generated bodies", "`ctxt-*` recursion")
- Incorporated in engine plan: yes (E4, §5)

## Summary

- `engine/rules/first-lemmas.lisp` certifies in 4.0 s with five facts
  about the generated 3.0 functions, each for an arbitrary state `z`.
- A whole `STEP` under a label (`(LABEL_ 0 () nop)`) is proved in 10,141
  prover steps. ACL2 opens every rule function before `Step/ctxt-label`,
  sees that it fails on the shape of the instruction, and recurs.
- So two risks of the plan are smaller than written: proofs about the
  generated bodies are fast with one function per rule, and the `ctxt-*`
  recursion needs only expand hints for a fixed instruction list.
- Not tested: instruction lists with a symbolic prefix or rest
  (`vals ++ i ++ rest`). That is the real E4 item 4 and E11 work.

## Findings

| Lemma | Says | Prover steps |
|---|---|---|
| `step-of-nop-alone` | `STEP (z; nop) = (z; eps)` | 460 |
| `step_pure/r-drop-fires-only-on-val-drop` | dispatch for one rule: if the rule function returns non-`nil`, the list is `val drop` | small |
| `step_pure/r-if-true-fires-only-on-const-if` | the same for a rule with a premise | small |
| `step_pure/r-if-true-clean` | clean form: the rule function on `(const i32 c) (if bt is1 is2)` with `c != 0` returns `((block bt is1))` | small |
| `step-of-nop-under-a-label` | `STEP (z; (LABEL_ 0 () nop)) = (z; (LABEL_ 0 () eps))` | 10,141 |

The recipe, for a later session:

- **Theory.** `step-rule-defs` (defined in the book) is the list of the
  definitions of every W3T function whose name starts with `STEP`. Enable
  it and the non-recursive rule functions open by themselves.
- **Recursive functions.** `STEP`, `STEP/R-CTXT-INSTRS`, `STEP/SEARCH21`
  and the other members of `STEP`'s clique do not open by themselves.
  Give `:expand` hints with `:free` variables, as in the last lemma.
- **Shapes.** The generated patterns test `(TRUE-LISTP x)` and
  `(EQUAL (LEN x) k)`. Two forward-chaining lemmas (`true-listp-len-0`,
  `len-cdr-consp`) turn these into facts about `x`. Without the first,
  the `drop` dispatch lemma fails at "`(cdr i)` has length 0, so `i` is
  `(:drop)`".
- **Ground parts run.** `STEP_PURE` on a constant instruction list is
  evaluated (the functions are executable), so a lemma with a constant
  instruction and a symbolic state costs little.

### What a dispatch lemma should say (design input to item 4)

Every pure rule with a fixed shape matches `val^k instr`: its operands
are values. So "rule R fires on `l`" implies "`l` is values followed by
one last instruction with R's opcode". For the lists the machine's `abs`
builds, `rev(vals) ++ (i . rest)`:

- if `rest` is not empty, the first instruction that is not a value is not
  the last element, so no fixed-shape rule fires on the whole list;
- if `rest` is empty, only the rules for `i`'s opcode can fire, and only
  with the right number of values.

The rules without a fixed shape are few and are handled one by one:
`trap-instrs` and `throw_ref-instrs` (`val* TRAP instr*`), and the rules
whose list is one administrative instruction (`label-*`, `br-label-*`,
`frame-*`, `return-*`, `handler-*`, `trap-label`, ...).

The lemma library therefore needs one function, "index of the first
instruction that is not a value", and per rule function one lemma in
terms of it. `ctxt-instrs` uses the same index (`STEP/PREFIX7`).

## Open questions

- How large the proofs become with a symbolic prefix of values and a
  symbolic rest. Try `nop` and `binop` first, as the plan says.
- Whether one lemma per rule function is written by hand or generated
  (item 3). 322 rule functions belong to the step group, most of them
  outside D5.

## Data

`engine/rules/first-lemmas.lisp`; `make -C engine check`.
