# Engine notes

Findings from the milestones of [../plan.md](../plan.md). Conventions
(layout, note header, session protocol) are those of
[the prep notes](../../wasm3-translation-prep/notes/README.md), with
milestone names `E<k>` and the header field "Feeds engine plan".

**Rule**: if a finding is not in a note here (or in `../plan.md`), it does
not exist.

## Index

| Note | Milestone | Status | One line |
|---|---|---|---|
| [E0-baseline](E0-baseline.md) | E0 | final | Flat code runs at 23,000 to 40,000 spec steps/s; allocation by failing rules is the main cost; loads and stores cost O(memory), a step at call depth d costs d²; 64 pages need a larger control stack |
| [E1-mupdf-target](E1-mupdf-target.md) | E1 | draft | The published MuPDF module uses legacy exceptions; fork `raymyers/mupdf`, branch `wasm3-exceptions`, switches to the 3.0 encoding; a Nix script rebuilds it bit for bit; D5 = 165 instructions; six imports are called to render; the small build passes the generated decoder and `Module_ok` |
| [E2-step-logic](E2-step-logic.md) | E2, E4 item 2 | final | Go: `STEP`, `STEP_READ`, `STEPS/%FUEL` are `:logic`. Three missing measures, then one function per rule (D4 (a)) because the `REF_OK` termination proof was too large with the rules inline |
| [E3-theorem](E3-theorem.md) | E3 | final | The theorem is stated for any machine (six constrained functions, four constraints) and its run level is proved; the spec facts behind C3 (values, `TRAP`, an uncaught exception do not step) are proved, and C3 holds for the list machine |
| [E4-first-lemmas](E4-first-lemmas.md) | E4 | draft | Five lemmas about the generated step functions certify in 4 s, among them a whole `STEP` under a label for any state (10,141 prover steps); the recipe and what a dispatch lemma should say |
| [E5-machine](E5-machine.md) | E5 | final | A context-stack machine over the spec's own data that mirrors the spec's intermediate forms: 0 or 1 spec steps per machine step; no flat bytecode; the fast machine is the same step function over an abstract stobj |
| [E6-list-machine](E6-list-machine.md) | E6 | draft | The list machine dispatches on the head instruction and applies the spec's own rule functions to the redex; C1 and C3 proved; test 1: 0 disagreements; test 2: 33,113 commands agree, 2 differ (being checked) |
