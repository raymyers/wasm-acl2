# Decisions D1-D6 (and others)

- Milestone: all (plan §4)
- Date: 2026-11-14
- Repo commit: see the commit that last changed this file
- Status: draft (no decision is confirmed by the user yet)
- Feeds wasm3 plan: decisions
- Incorporated in wasm3 plan: yes (draft plan, §1)

Record a decision here, with the date, when the user makes it; then update
plan.md "Current state" and the wasm3 plan §1.

| # | Decision | State (2026-11-14) | Built on it so far |
|---|---|---|---|
| D1 | 2.0 as a stepping stone | assumed yes | P4: 2.0 certified, `make check-2.0` |
| D2 | One tree, per-version layout, shared `rt/` (package `WRT`) | assumed | P2 layout; `rt/` in `WRT` (P2-layout option A) |
| D3 | 3.0 scope `0.*`-`5.*`; `X.*` out; `6.*`, `7.*` deferred | assumed | flake `wasm3-il` file list |
| D4 | Deterministic nondeterminism profile (V8 choices) | open | nothing (choice parameters only classified) |
| D5 | SpecTec printer patch for hints | assumed | `nix/spectec-ast-print-hints.patch`, inverse pairs and builtin classes from hints |
| D6 | Execution first, typing second | assumed | wasm3 draft plan milestone order |
