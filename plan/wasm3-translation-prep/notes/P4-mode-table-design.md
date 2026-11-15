# Mode table: inputs for the design session

- Milestone: P4 (W1/G2: explicit mode table per relation, inferred, any
  output positions). The design itself is handed to a Fable session and the
  wasm3 plan's M5 (user decision, 2026-11-14)
- Date: 2026-11-14
- Repo commit: b577f07 plus this note's commit
- Status: final (as inputs; the design is not in this note)
- Feeds wasm3 plan: scheme delta (modes), milestones (M5), risks
- Incorporated in wasm3 plan: yes (draft plan, §4 (modes), §5 M5)

## Summary

What the translator has today, the evidence a design must account for, and
the open judgement. Modes are inferred by three attempts per `rec` group
(`:fun`, failing members `:check`, all `:multi`); since P4 they can be
declared per relation (`:modes`, counted), including `:fun2` (last two
components out). The 3.0 config declares 21 relations. The open question
is how to score an attempt so that inference picks these without
declarations, and does not prefer a mode only because it hides a
single-witness existential.

## Findings

### What exists (use it, do not rebuild it)

- Inference: `crel-form-1` (three attempts) and `crel-partial` (best
  attempt reported, `:fun` emitted when salvageable, per-rule stubs).
- Declared modes: config `(:modes ... :pairs (("Rel" . mode) ...))`,
  applied in every attempt by `set-modes` / `set-mode-ids`
  (`declared-mode`). Modes: `:fun`, `:fun2`, `:check`, `:multi`,
  `:closure` (inferred).
- Calling conventions: the car of a `:modes` entry is the convention
  (`:fun`, `:fun2`, `:check`, `:multi`); declared `:multi` once got `:fun`
  by mistake, and only certification found it (P4-wasm2-result). Any new
  mode needs its convention in `set-modes`, `crule-premise`, `crel-1-body`
  and `rel-stubs`.
- Mode table output: the probe prints every relation's final mode; 1.0
  (nothing declared) is 13 `:fun`, 15 `:check`, 7 `:multi`, 1 `:closure`.
- Existential searches in `:check` mode (G5, G8): index `v < |l|`, finite
  nullary types, deferred conclusion tests inside the loop.

### Evidence a design must reproduce

| Group | What works | Source |
|---|---|---|
| 3.0 type validation + subtyping (19) | all `:check`: 1 failing rule (`Heaptype_sub/trans`) after G8; `:multi`: 0, but `trans` then takes one witness `ht'` from `Heaptype_ok/SPLIT` | P1-typing-root-causes, P4-generic-gaps |
| `Instr_ok`, `Instrs_ok` (1.0, 2.0, 3.0) | `:multi`: the check variant keeps stack-polymorphic rules; the split variant computes the output stack, which `Instrs_ok/seq` needs for the intermediate stack | wasm1 T6, P4 |
| `Eval_expr` (3.0) | two outputs (store, values): `:fun2` | P4-generic-gaps |
| `Step`, `Step_read`, `Step_pure` | `:fun` (execution needs the next configuration); "fewest failing rules" once chose `:check` for `Step_read`, which is useless for execution | P1 |
| 1.0 | the three attempts find everything; byte-identity is the guard | `make check` |

### The open judgement

Both `Instrs_ok/seq` (intermediate stack) and `Heaptype_sub/trans`
(intermediate heap type) bind an existential through a split variant.
For `Instrs_ok/seq` the bound value is determined by the inputs (typing
of an instruction sequence computes its output stack), so one witness is
complete. For `trans` it is not, so one witness is incomplete. A score
of "failing rules" cannot tell them apart; a design needs one of:

- a functional-dependency check (is the split variant's output
  determined by its inputs? true for instruction typing by construction of
  the stack discipline, false for subtyping);
- a declared hint per premise (counted config) where the check is not
  decidable;
- or the rule that `:multi` existentials count as failing unless the
  callee is declared functional.

Also open: outputs in any positions (generalizing `:fun2`), and whether
inference should run per relation (local search with the others fixed)
rather than per group.

## Data

Attempt logs: `data/probe-P1-2026-11-14/report-3.0-core.txt`; declared-mode
experiments: `data/probe-P4-modes-2026-11-14/`; current state:
`data/probe-P4-G5G8-2026-11-14/`.

## 2026-11-14: the design

Done in the wasm3 plan, M5 item 1:
[M5-mode-table](../../wasm3-translation/notes/M5-mode-table.md). The open
judgement above is settled by the third option in a stricter form: a
premise that takes a value from an output variant that drops rules is an
error unless a counted `:witness` entry accepts the relation.
