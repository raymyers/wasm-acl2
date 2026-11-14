# Suggested model choice for the prep work

Most of this work will be done with Opus, with limited use of Fable. This
note says where the limited Fable sessions pay off most. Milestone and gap
ids (P0-P7, W1, G2, ...) refer to [plan.md](plan.md).

## Principle

Use Fable where a wrong design decision is expensive and hard to detect.
Use Opus where the work is checked mechanically.

This project has a strong built-in checker: WASM 1.0 must regenerate
byte-identically (`make -C translate check`), and tests compare against V8.
Work guarded by that checker is safe to delegate. Work where tests pass even
when the reasoning is wrong is not.

## Use Fable for (in priority order)

| # | Task | Milestone | Why |
|---|---|---|---|
| 1 | **Mode table design**: replace the three-shot mode guessing in the relation compiler (`crel-form-1`) with declared and inferred modes, including several outputs. Design plus the core implementation, then hand over the remaining cases | P4 (W1, G2) | All of 3.0 typing and instantiation sits on it. A poor design shows up only weeks later, as a growing pile of config overrides |
| 2 | **Typing root-cause triage**: for each failing typing rule in the per-rule gap list, decide whether it is a missing translator feature, a rule that needs an algorithmic reading (transitive subtyping, recursive type indices), or a justified override | after P1 | Sets the size and shape of the wasm3 plan. Today these causes are unknown (S2) |
| 3 | **Instruction typing strategy for 3.0**: does the check + split approach survive subtyping and local-initialization tracking, or do we accept a hand-written validator proved or tested against the rules | go/no-go for the wasm3 plan (S3) | A judgment call with soundness consequences |
| 4 | **Writing `plan/wasm3-translation/plan.md`** | P7 | A synthesis of everything measured. Its milestone order and exit criteria steer all the Opus work that follows |
| 5 | **Review where the checker is blind**: the soundness argument for each counted override, the nondeterminism policy (D4), and any change that makes a relation "sound but incomplete" | ongoing | Tests pass in these cases even when the reasoning is wrong |

## Fine for Opus

| Task | Milestone | What guards it |
|---|---|---|
| Probe as a make target (procedure is in plan §8) | P0 | Must reproduce the §1 numbers |
| Errors tagged with rule id and mode; per-rule stubs | P1 | 1.0 output unchanged |
| Multi-spec plumbing: parameterized paths, packages, flake outputs; split generated books; mode manifest | P2 | 1.0 definitions unchanged, 1.0 tests pass |
| Hint patch to the SpecTec AST printer, reader support, inverse pairs from the IL | P3 | 1.0 output unchanged with the `:inverse` config entry removed |
| Smaller generic gaps: function-argument specialization (G1), counter-only iterations (G3, G4), disjunctions (G5) | P4 | 1.0 unchanged; 2.0 certifies |
| Builtins and oracle vectors | P4 | Each builtin is compared against V8 |
| Conformance driver | P5 | Recorded pass counts |
| Runtime measurement | P6 | Measurements, not judgment |

## Suggested rhythm

1. **After P1**: one Fable session for items 1 and 2 together, since the
   triage informs the mode design.
2. **At the instruction-typing decision**: one Fable session (item 3).
3. **P7**: one Fable session to write the wasm3 plan (item 4).
4. **Short review sessions** whenever a new override or a dropped rule is
   proposed (item 5).

## How this is applied

A session cannot change its own model; the user chooses it when starting the
session. So this file is guidance for the user, not something a session
enforces. "Current state" in plan.md has a "Next Fable session needed for"
line as the reminder.

A session can choose the model of a subagent it spawns, but a subagent gets
only its brief and returns only a summary. That suits a bounded review
(item 5) when the user allows it. It does not suit items 1-4, which need the
full context and several rounds.

## Condition

This split assumes the delegated work keeps two rules from the wasm1 plan:
1.0 output stays unchanged unless a milestone says otherwise, and `gen/` is
never edited by hand. If either slips, the checker stops protecting the
delegated work and the split above no longer holds.
