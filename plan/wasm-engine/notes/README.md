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
| [E1-mupdf-target](E1-mupdf-target.md) | E1 | draft | The published MuPDF module uses legacy exceptions; fork `raymyers/mupdf`, branch `wasm3-exceptions`, switches the build to the 3.0 encoding; rebuilt module renders the same pixels in V8 |
| [E2-step-logic](E2-step-logic.md) | E2, E4 item 2 | final | Go: `STEP`, `STEP_READ`, `STEPS/%FUEL` are `:logic`. Three missing measures, then one function per rule (D4 (a)) because the `REF_OK` termination proof was too large with the rules inline |
| [E3-theorem](E3-theorem.md) | E3 | draft | The theorem is stated for any machine (six constrained functions, four constraints) and its run level is proved with no `skip-proofs`; E11 proves the constraints for the real machine |
| [E4-first-lemmas](E4-first-lemmas.md) | E4 | draft | Five lemmas about the generated step functions certify in 4 s, among them a whole `STEP` under a label for any state (10,141 prover steps); the recipe and what a dispatch lemma should say |
| [E5-machine](E5-machine.md) | E5 | final | A context-stack machine over the spec's own data that mirrors the spec's intermediate forms: 0 or 1 spec steps per machine step; no flat bytecode; the fast machine is the same step function over an abstract stobj |
