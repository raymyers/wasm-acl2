# Instruction typing for 3.0: what runs today, and the strategy

- Milestone: M6 (item 1: design session, go/no-go on one witness for
  instruction typing). Also model-choice item 3 of the prep
- Date: 2026-11-14
- Repo commit: 56837fd plus this note's commit
- Status: final for the findings and the fix; the strategy is a
  **recommendation waiting for the user's decision**
- Feeds wasm3 plan: §5 M5, M6, M7; §6 (config budget); §7 (risks)

## Summary

First run of generated 3.0 typing code (23 cases, proofs skipped). Before
this session it rejected `i32.const; i32.const; i32.add`: 13 of 23 right.
The cause was mechanical and is fixed: 18 of 23. The 5 left are
subsumption (3), dead code (1) and `trans` (1). Subsumption cannot be
translated mechanically at all. Answer to the go/no-go: **no-go** for
check + output variant alone; **recommended**: a hand-written sequencer
that proposes types, with every step checked by the generated rules.

## Findings

### 1. The cases (data: `data/typing-M6-2026-11-14/`)

Generated relations called directly with an empty context. Expected
answers are from the spec rules; all positive cases are ordinary valid
WASM. V8 was not used yet.

| | 3.0 before | 3.0 after the fix | 2.0 |
|---|---|---|---|
| Right answers | 13 of 23 | **18 of 23** | 5 of 6 |
| `const const add : [] -> [i32]` | rejected | accepted | accepted |
| `block (result i32) const const add` | rejected | accepted | accepted |
| `const; ref.i31 : [] -> [(ref null i31)]` (subsumption) | rejected | rejected | (no such types) |
| `block (result (ref null i31)) const; ref.i31` | rejected | rejected | |
| `const; ref.i31 : [] -> [anyref]` (subsumption and `trans`) | rejected | rejected | |
| `unreachable; add : [] -> [i32]` (dead code) | rejected | rejected | rejected |
| `I31 <: ANY` | rejected | rejected | |
| the 6 ill-typed or negative cases | rejected (right) | rejected (right) | rejected (right) |

"110 of 110 `Instr_ok` rules translate" was true and said nothing about
this. It is the reason M5 to M7 now have behavioural exits.

### 2. Cause of the total failure, and the fix (done)

The 3.0 instruction type has three parts, `t_1* ->_(x*) t_2*`. The
translator made the output variant take the first half of a last
component `c(a, b)` as an input only for two parts. So in 3.0
`INSTRS_OK/SPLIT (C instr*)` got no input stack, the `frame` rule could
not be computed, and nothing longer than one instruction typed. 2.0 has
two-part arrows and was not affected.

Fix in `compile.lisp`:

- `split-last`: `c(a, b, c ..)` splits into input `a` and outputs
  `(b, c ..)`.
- `rel-splits-p`: whether a relation's output variant splits is decided
  per relation, from the premises of its own rules that call it, not from
  its first rule. The old criterion gave 3.0 `REF_OK/SPLIT` three formals
  while its caller passed two (an arity error that certification would
  have hit; found by the new premise-side check).
- A premise that passes one unbound term where the callee's variant needs
  the input part is now an error. That is how `Instrs_ok/sub` shows up as
  a dropped rule instead of compiling into something that never succeeds.

Probe, 3.0 D3 scope: dropped rules 2 → **3** (`Instrs_ok/sub` is new and
honest); rules dropped from output variants 22 → 13 (`Instr_ok` 18 → 10,
`Instrs_ok` 2 → 1). 1.0 `gen/` byte-identical, 2.0 probe report identical.

### 3. Subsumption has no mechanical reading

```
rule Instrs_ok/sub:  C |- instr* : it'
  -- Instrs_ok: C |- instr* : it
  -- Instrtype_sub: C |- it <: it'
```

Nothing but `it <: it'` constrains `it`. A translation would have to
enumerate the subtypes of `it'`, and there are unboundedly many. The
witness rule of the mode table does not apply either: there is no output
variant to take `it` from once the variant needs the input stack. This is
not a translator gap. The declarative rule states what is valid, and the
spec gives the algorithm separately (its validation appendix).

Subsumption is everywhere in 3.0: a non-null reference where a nullable
one is expected, any GC type against `anyref`, every `call` with reference
parameters, every block result. Without it the generated `INSTRS_OK` is
right for 1.0-style numeric code and wrong for most 3.0 code.

### 4. Dead code

`unreachable; i32.add` is rejected in 2.0 and 3.0. The output variant
drops the stack-polymorphic rules, and the 1.0 fallback (try the empty
list and the bound list variables) does not find `[i32 i32]`. This is the
known 1.0 incompleteness (9 spec-test-1 scripts, P5), unchanged.

## The strategy

| Option | What it is | Verdict |
|---|---|---|
| A. Mechanical: check + output variant, accepted witnesses | today, after the fix | **No-go**: no subsumption (3 of 23 cases), no dead code |
| B. Hand-written validator (the spec's algorithm) | about 110 instruction cases by hand | Complete, but it duplicates every generated rule and is tied to the spec only by tests |
| **C. Proposer and checker** | a hand-written sequencer proposes the type of each instruction; the generated rules check each step | **Recommended** |

### Option C in detail

The 110 `Instr_ok` rules stay generated and are used in **check** mode,
where every type is given. Check mode is the mechanical, complete reading
of a rule (it is where "110 of 110" is meaningful). Only the five
structural rules of `Instrs_ok` (`empty`, `instr`, `seq`, `sub`, `frame`)
are replaced by one hand-written function, the sequencer:

1. It keeps the current stack and the set of initialized locals.
2. For each instruction it proposes a concrete type `a ->_(x*) b`:
   - from the generated output variant when the instruction determines
     its type (about 100 rules);
   - from a small table for the 10 rules that the output variant drops
     (`unreachable`, `select`, `br`, `br_table`, `return`, the three
     `return_call`s, `throw`, `throw_ref`), which says what to pop.
3. It checks the proposal with the generated `INSTR_OK C instr type`.
4. It pops the operands with the generated `RESULTTYPE_SUB` (this is
   `sub` and `frame`), pushes `b`, and updates the locals with the
   generated `$with_locals` (this is `seq`).
5. After a stack-polymorphic instruction it marks the stack unreachable;
   pops from it yield whatever is needed (`BOT` where nothing is known),
   as in the spec's algorithm.
6. At the end it compares the stack with the expected result by
   `RESULTTYPE_SUB`.

Why this is the right split:

- **Soundness by construction.** The sequencer accepts only when the
  generated checker accepted every instruction at a concrete type and the
  generated subtyping accepted every pop. A mistake in the hand-written
  part can make it reject a valid program. It cannot make it accept an
  invalid one, except through the five structural steps themselves, which
  are a page of code with a short argument each.
- **Completeness is testable.** Wrong rejections show up against V8 and
  spec-test-3 (`assert_invalid` must reject, everything else must pass).
- **The spec stays the source** for all 110 rules. Option B would re-state
  them by hand.

What the translator needs for it (all three are in the mode-table
hand-over list or small):

1. `:rel-override` for a member of a `rec` group (`Instrs_ok` is in a
   group with `Instr_ok`). Today an override is only possible for a
   relation outside a group.
2. Sub-component output positions (mode-table hand-over item 3), so that
   `Instr_ok/block` calls the sequencer with the block's result type as an
   input and only `x*` as output. Today it takes `t_2*` back and compares
   it for equality, which is why the block case fails.
3. The whole-type variant of `Instr_ok` (mode `(:out 2)`: no input
   stack, the principal type of the instruction), kept for hand-written
   code although it drops rules. The sequencer needs the expected operand
   types before it can pop with subtyping; the variant that takes the
   input stack matches it exactly and so cannot do that. Variants on
   demand are discarded today when a rule fails.

Config cost: 1 `:rel-override` (`Instrs_ok`). The `:witness` entry
loses `Instr_ok` and `Instrs_ok`: the sequencer does not rely on a
single witness, it checks.

Size estimate (not measured): the sequencer and table about 150 to 250
lines of ACL2, against about 80 lines for the 1.0 `Module_ok` override.

### What this means for the other milestones

- **M5**: the sequencer needs `Heaptype_sub` to be complete, so `trans`
  comes first. The case `const; ref.i31 : [] -> [anyref]` needs both.
- **M7**: `Module_ok` calls `Func_ok`, which calls `Expr_ok`, which calls
  the sequencer; no change in its design question.
- **2.0**: has the same two gaps (its `Instrs_ok/sub` is dropped, dead
  code fails). Its gate tests numerics only. 2.0 is a stepping stone, so
  this is recorded, not scheduled.
- **1.0**: unchanged. The same sequencer would close its dead-code
  incompleteness (9 spec-test-1 scripts), which is optional.

## Open questions

- Decision: option C, option B, or accept option A as "sound but
  incomplete" for now.
- Is the 10-entry table enough, or do the operand-polymorphic rules that
  now compile in the output variant (`drop`, `ref.is_null`,
  `ref.as_non_null`, `br_on_null`, `ref.test`, `ref.cast`, the two
  conversions) need entries too? They match the stack top exactly, so a
  non-null reference where the rule says `REF NULL ht` fails. Probably
  yes for some; the M6 behavioural cases will tell.

## Data

`data/typing-M6-2026-11-14/`: `cases-3.0.lsp`, `cases-2.0.lsp`,
`results-3.0-before.txt`, `results-3.0-after.txt`, `results-2.0.txt`,
`run.sh`; `report-3.0-core.txt` and `-rules.txt` (probe after the fix). The 3.0 books are loaded from a scratch copy with proofs
skipped, since 3.0 does not certify in-tree yet (M0, M1); only the parts up
to `2_3-validation_instructions` are needed and they use no missing
builtin. About 30 s.
