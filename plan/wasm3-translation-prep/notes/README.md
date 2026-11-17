# Prep notes

Intermediate findings from the prep milestones. They exist so that work can
stop and resume with no memory of earlier sessions, and so that P7 can build
`plan/wasm3-translation/plan.md` from written evidence.

**Rule**: if a finding is not in a note here (or in `../plan.md`), it does not
exist. Do not rely on conversation history, scratch directories or `/tmp`.

## Layout

```
notes/
  README.md            this file: conventions + index
  P<k>-<slug>.md       one note per finding or design, named by milestone
  data/<name>/         raw evidence a note cites: scripts, logs, tables
```

- Notes are append-friendly: add a dated section instead of rewriting history.
  When a later result replaces an earlier one, mark the old section
  `Superseded by <note>` and leave it in place.
- Raw data goes under `data/`, with the script that produced it and the commit
  it was run at. Strip machine-specific paths. Large regenerable files (IL
  dumps) are not stored: store the command instead.

## Note header

Every note starts with:

```markdown
# <title>
- Milestone: P<k> (item text from plan.md)
- Date: YYYY-MM-DD
- Repo commit: <hash the measurement or design applies to>
- Status: draft | final | superseded by <note>
- Feeds wasm3 plan: <which part: probe table / gap list / scheme delta /
  milestones / builtin inventory / config budget / risks / decisions>
- Incorporated in wasm3 plan: no | yes (<section>) | dropped (<reason>)
```

Then: **Summary** (5 lines at most, readable alone), **Findings**, **Open
questions**, **Data** (paths under `data/` and how to regenerate).

## When to write one

- A measurement that plan.md cites or will cite.
- A root cause for a stub or dropped rule.
- A design decision or a rejected alternative, with the reason.
- A decision by the user (D1-D6 and any new ones), with the date.
- Anything a session learned the hard way (a tool quirk, a dead end).

## Session protocol

- **Start**: read `../plan.md` "Current state", then this index, then the
  notes for the milestone being worked on.
- **During**: write the note as the work happens, not at the end. A session
  can lose its context at any point.
- **End (same commit as the work)**: update the note's status, add or update
  its index row below, and update "Current state" in `../plan.md`.

## Index

Keep one row per note, in milestone order. P7 is done only when every row
says `yes` or `dropped` in the last column.

| Note | Milestone | Status | Feeds wasm3 plan | Incorporated |
|---|---|---|---|---|
| [P0-probe-2026-11-14.md](P0-probe-2026-11-14.md) | P0 (baseline, before any change) | final | probe table, gap list | yes (draft plan) |
| [P0-confidence-assessment.md](P0-confidence-assessment.md) | P0 (assessment) | draft | risks, milestone order | yes (draft plan) |
| [P0-probe-tool.md](P0-probe-tool.md) | P0 (all three items: `make probe`, G7, schema) | final | probe table, gap list | yes (draft plan) |
| [P1-gap-list.md](P1-gap-list.md) | P1 (per-rule gap list) | draft | gap list, milestones, config budget | yes (draft plan) |
| [P1-typing-root-causes.md](P1-typing-root-causes.md) | P1 (S2 root causes) | draft | gap list, risks, scheme delta | yes (draft plan) |
| [P2-layout.md](P2-layout.md) | P2 (all items; `rt/` package question open) | final | scheme delta, decisions | yes (draft plan) |
| [P3-hints.md](P3-hints.md) | P3 (items 1-2: hint patch, IL hint forms, inverse pairs from hints) | final | scheme delta, builtin inventory, decisions | yes (draft plan) |
| [P3-builtin-inventory.md](P3-builtin-inventory.md) | P3 (items 3-4: builtin classification, inventory) | final | builtin inventory, config budget, decisions | yes (draft plan) |
| [P5-conformance.md](P5-conformance.md) | P5 (spec-test-1 result, 3.0 data, dry run partial) | draft | milestones, risks, probe table | yes (draft plan) |
| [P6-runtime-baseline.md](P6-runtime-baseline.md) | P6 (all items: step cost, 3.0 approach, crash sites, spec-test-3 estimate) | final | risks, milestones, scheme delta | yes (draft plan) |
| [P4-mode-table-design.md](P4-mode-table-design.md) | P4 (W1 design inputs; design handed to Fable / wasm3 M5) | final | scheme delta, milestones, risks | yes (draft plan) |
| [P4-wasm2-result.md](P4-wasm2-result.md) | P4 (2.0 full target, the P4 exit) | final | milestones, builtin inventory, risks, config budget | yes (draft plan) |
| [P4-generic-gaps.md](P4-generic-gaps.md) | P4 (G1, G3, G4, G9 done; G5, G8 with the mode table) | draft | scheme delta, gap list, config budget | yes (draft plan) |
| [decisions.md](decisions.md) | all (D1-D6) | draft (nothing confirmed) | decisions | yes (draft plan) |
