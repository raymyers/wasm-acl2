PLAN is plan/wasm-engine/plan.md
NOTES is plan/wasm-engine/notes/ (index: NOTES/README.md; conventions: plan/wasm3-translation-prep/notes/README.md)

Assume no memory of earlier sessions. Everything needed is in PLAN and NOTES.

Execute these steps:

* Read PLAN "Current state", then the NOTES index, then the notes for the milestone you will work on.
* Choose the next logical milestone item (E0..E11, respecting PLAN "Order and dependencies").
  * Every decision in PLAN §1 is settled. Stop for the user only in the cases of PLAN "When a headless session stops".
  * E5 is headless: write the design note, take the recommended design, go on.
  * E2 changes `translate/`; the user approved it (PLAN "Current state").
  * The run track (E0, E1, E5..E10) does not wait for the proof track (E2, E3, E4, E11).
  * A go/no-go exit that says no-go stops that branch of the plan: record it and wait for the user.
* Check for uncommitted changes; you decide whether to finish them or discard them.
* Complete and verify the task. These gates must stay green, and they must not be weakened: `make -C translate check` (1.0), `make -C translate check-2.0`, `make -C translate check-3.0`, `make -C demo check`. Once `engine/` exists, also `make -C engine check`.
  * Write findings into a note in NOTES as you go. Raw outputs go under NOTES/data/, together with the script that made them.
  * A proof item is done when its book certifies with no `skip-proofs` and no `defaxiom` outside the one event PLAN E3 names. A machine item is done when its differential test against the generated semantics passes, not when it builds.
  * Test before proving (PLAN D7): do not start a simulation proof for a group of instructions whose differential test has not passed.
* If successful
  * Then, in one commit with the work:
    * mark the item complete in PLAN, with measured results and a link to the note
    * add or update the note's row in the NOTES index
    * update PLAN "Current state" (next action, anything in progress, decisions)
  * Otherwise stop, but first record what was tried and why it failed in a note, and update "Current state".

# Tech guidelines

Use Nix to run the whole toolchain (ACL2, SBCL, node, Emscripten).
One session at a time works on `translate/`: check `git status` and `git log` first, and do not start if another session's work is in the tree.
Numbers in PLAN come from a measurement or a test run, never from estimates.
Do not leave findings only in the conversation, a scratch directory or /tmp.
The generated books are the specification. Never copy or edit them. `engine/` includes them.
`translate/` changes only for an item PLAN marks as approved by the user (E2 and D4 (a), both approved 2026-11-15) and only through the generator (`il2acl2/`, `rt/`, config). Everything that certified or passed before must still certify and pass: the gates, unchanged mode manifests, `check-gen` determinism, and identical per-command spec results.
The engine calls the spec's numeric functions (PLAN D6). Do not re-implement arithmetic.
A theorem's hypotheses are part of the result. When a hypothesis is added to make a proof go through, record it and its reason in the milestone's note and in PLAN "Current state".
When a proof attempt fails, keep the failed checkpoint in the note before trying another approach.
The MuPDF sources live in the fork (PLAN E1), not in this repository. Built binaries are not checked in: record the fork commit, the build command and the checksum.
Every claim about a rendered page says whether the module is inside the proved subset (PLAN D8).
