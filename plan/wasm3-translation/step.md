PLAN is plan/wasm3-translation/plan.md
NOTES is plan/wasm3-translation/notes/ (index: NOTES/README.md; conventions: plan/wasm3-translation-prep/notes/README.md)

Assume no memory of earlier sessions. Everything needed is in PLAN and NOTES.

Execute these steps:

* Read PLAN "Current state", then the NOTES index, then the notes for the milestone you will work on.
* Choose the next logical milestone item (M0..M9, respecting PLAN "Order and dependencies").
  * An item marked "design session" produces a note and a decision for the user. Do not start the items after it in that milestone until the decision is recorded.
* Check for uncommited changes, it will be your choice to finish or discard.
* Complete and verify task. The gates must stay green: `make -C translate check` (1.0), `make -C translate check-2.0`, and `make -C translate check-3.0` once M0 has made it.
  * Write findings into a note in NOTES as you go. Raw outputs go under NOTES/data/ with the script that made them.
  * A typing item is not done because it compiles. It is done when its behavioural cases pass (PLAN M5, M6, M7 exits).
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
1.0 output stays byte-identical unless a milestone item says otherwise; `gen/` is never edited by hand.
A new config entry, a dropped rule or a new `:witness` relation needs its reason written in the config and is listed in "Current state" for the user.
