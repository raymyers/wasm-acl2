PLAN is plan/wasm3-translation-prep/plan.md
NOTES is plan/wasm3-translation-prep/notes/ (conventions and index: NOTES/README.md)

Assume no memory of earlier sessions. Everything needed is in PLAN and NOTES.

Execute these steps:

* Read PLAN "Current state", then the NOTES index, then the notes for the milestone you will work on.
* Choose the next logical milestone item (P0..P7, respecting the dependency order in PLAN §5).
* Check for uncommited changes, it will be your choice to finish or discard.
* Complete and verify task. WASM 1.0 must still pass `make -C translate check`.
  * Write findings into a note in NOTES as you go (header and layout per NOTES/README.md). Raw outputs go under NOTES/data/ with the script that made them.
* If successful
  * Then, in one commit with the work:
    * mark the item complete in PLAN, with measured results and a link to the note
    * add or update the note's row in the NOTES index
    * update PLAN "Current state" (next action, anything in progress, decisions)
  * Else bail, but first record what was tried and why it failed in a note, and update "Current state".

# Tech guidelines

Use Nix to run all toolchain.
Numbers in PLAN come from the probe or a test run, never from estimates.
Do not leave findings only in the conversation, a scratch directory or /tmp.
