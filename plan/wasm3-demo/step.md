PLAN is plan/wasm3-demo/plan.md
NOTES is plan/wasm3-demo/notes/ (index: NOTES/README.md; conventions: plan/wasm3-translation-prep/notes/README.md)

Assume no memory of earlier sessions. Everything needed is in PLAN and NOTES.

Execute these steps:

* Read PLAN "Current state", then the NOTES index, then the notes for the milestone you will work on.
* Choose the next logical milestone item (W0..W9, respecting PLAN "Order and dependencies").
  * W1 confirms a decision the user has already made (PLAN D5). Stop for the user only if a D5 condition fails.
  * Never wait for the user on a choice that PLAN marks *(default)*: take the default and record it.
  * A go/no-go exit that says no-go stops the plan: record it and wait for the user.
* Check for uncommitted changes; you decide whether to finish them or discard them.
* Complete and verify the task. These gates must stay green, and they must not be weakened: `make -C translate check` (1.0), `make -C translate check-2.0`, `make -C translate check-3.0`. Once W2 exists, also `make -C demo check` for the parts already built.
  * Write findings into a note in NOTES as you go. Raw outputs go under NOTES/data/, together with the script that made them.
  * An item is not done because it builds. It is done when its comparison against ACL2 output passes (PLAN W3, W4, W7 exits), or when its headless browser test passes (W5, W6, W8).
* If successful
  * Then, in one commit with the work:
    * mark the item complete in PLAN, with measured results and a link to the note
    * add or update the note's row in the NOTES index
    * update PLAN "Current state" (next action, anything in progress, decisions)
  * Otherwise stop, but first record what was tried and why it failed in a note, and update "Current state".

# Tech guidelines

Use Nix to run the whole toolchain (ACL2, SBCL, JSCL, node).
Numbers in PLAN come from a measurement or a test run, never from estimates.
Do not leave findings only in the conversation, a scratch directory or /tmp.
Never copy files under `translate/` for the demo. `demo/extract` reads the books, `rt/` and the test data, and anything derived goes to `demo/build/` (not checked in).
`translate/` changes only for an approved item (today: W7) and only through the generator (`il2acl2/`, `rt/`, config). `gen/` is never edited by hand. Generated output may change, 1.0 included (commit the regenerated `gen/wasm-1.0` with the translator change), but everything that certified or passed before must still certify and pass: the three gates, unchanged mode manifests, `check-gen` determinism, and identical per-command spec results (PLAN W7 item 4).
A new shim function, an override or a new extractor table entry needs its reason written next to it, and is listed in "Current state" for the user.
As visual progress is made (W0 item 1, then every W5, W6 and W8 item that changes the page), add a screenshot to `plan/wasm3-demo/progress/`, in the same commit. Name: `NN-Wk-slug.png`, where NN is the next two-digit number (e.g. `03-W5-step-mode.png`). Take it with the Playwright script in `demo/test/` (headless Chromium, 1280×800, light theme), so it can be retaken. Each file must be at most 150 KB: compress it (PNG palette quantization, from Nix), and if that is not enough, crop it to the part that changed.
