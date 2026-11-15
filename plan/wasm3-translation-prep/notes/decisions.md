# Decisions D1-D6 (and others)

- Milestone: all (plan §4)
- Date: 2026-11-14
- Repo commit: see the commit that last changed this file
- Status: final (D1-D6 decided by the user on 2026-11-14)
- Feeds wasm3 plan: decisions
- Incorporated in wasm3 plan: yes (draft plan, §1)

Record a decision here, with the date, when the user makes it; then update
plan.md "Current state" and the wasm3 plan §1.

| # | Decision | State (2026-11-14) | Built on it so far |
|---|---|---|---|
| D1 | 2.0 as a stepping stone | **decided 2026-11-14: yes** | P4: 2.0 certified, `make check-2.0` |
| D2 | One tree, per-version layout, shared `rt/` (package `WRT`) | **decided 2026-11-14: yes, incl. `WRT`** | P2 layout; `rt/` in `WRT` (P2-layout option A) |
| D3 | 3.0 scope `0.*`-`5.*`; `X.*` out; `6.*`, `7.*` deferred | **decided 2026-11-14: yes** | flake `wasm3-il` file list |
| D4 | Deterministic nondeterminism profile (V8 choices) | **decided 2026-11-14: deterministic, V8** (each choice a named builtin fixed to V8; canonical NaN; growth succeeds within limits) | the 11 choice parameters are classified; implementing them is wasm3 M1 |
| D5 | SpecTec printer patch for hints | **decided 2026-11-14: yes** | `nix/spectec-ast-print-hints.patch`, inverse pairs and builtin classes from hints |
| D6 | Execution first, typing second | **decided 2026-11-14: yes** | wasm3 draft plan milestone order |
