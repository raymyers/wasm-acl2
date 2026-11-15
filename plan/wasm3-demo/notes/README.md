# WASM 3.0 browser demo: notes

Findings for [the demo plan](../plan.md). The conventions are the prep's
([plan/wasm3-translation-prep/notes/README.md](../../wasm3-translation-prep/notes/README.md)).
The only difference is that notes are named by demo milestone (`W<k>-<slug>.md`;
`S0` is the planning survey). The header uses `Feeds demo plan:` in place of
`Feeds wasm3 plan:`, and records the JSCL rev when a note depends on it.

**Rule**: if a finding is not in a note here (or in `../plan.md`), it does not
exist. Raw outputs go under `data/<name>/` together with the script that made them.

## Index

| Note | Milestone | Status | Summary |
|---|---|---|---|
| [S0-survey](S0-survey.md) | planning | final | 27 books / 486,141 lines / ~33 MB; JSCL has no bignums or ratios; memory is a 65,536-element list per page |
| [W0-feasibility](W0-feasibility.md) | W0 | draft | toolchain in the flake (JSCL image, wabt.js, Playwright Chromium+Firefox); hello passes in node and both browsers |
