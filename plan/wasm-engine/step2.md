PLAN is plan/wasm-engine/plan2.md
NOTES is plan/wasm-engine/notes/ (index: NOTES/README.md)

Assume no memory of earlier sessions. Everything needed is in PLAN, NOTES and plan/wasm-engine/plan.md (the first plan: its decisions D1 to D10 stand).

Execute these steps:

* Read PLAN "Current state", then the notes for the milestone you will work on.
* Choose the next item (V0..V9, respecting PLAN "Order and dependencies"). V1..V5 and V6..V7 are independent after V0.
  * P1 and P3 are decided. P2 is the user's, after V5. Stop for the user only in the cases of plan.md "When a headless session stops".
* Check `git status` and `git log`; you decide whether to finish or discard uncommitted changes.
* Complete and verify the item. Gate: `make -C engine check`. It must stay green and must not be weakened. If `translate/` is touched (it should not be), its gates apply too.
  * An item is done when its book certifies under the gate with no `skip-proofs`, no `defaxiom` and no trust tag. A session result is not a gate.
  * An item that changes a machine re-runs the differential test PLAN names for it.
  * Write findings into a note in NOTES as you go (`V<k>-<name>.md`); raw outputs and the scripts that made them go under NOTES/data/.
* If successful, in one commit with the work:
  * mark the item complete in PLAN, with measured results and a link to the note
  * add or update the note's row in the NOTES index
  * update PLAN "Current state"
* Otherwise stop, but first record what was tried and why it failed in a note, and update "Current state".

# Tech guidelines

Use Nix to run the toolchain.
For interactive ACL2 work use the `acl2-mcp` tools (`start_session`, `evaluate`, `end_session`); end your sessions when done.
Proof practice, for every book you write or touch (source, reasons and the state of `engine/`: plan/wasm-engine/practices.md):
* One header per book: `include-book`s, then one theory block. Library includes (`std/lists`, arithmetic) are `local`; what a later book needs is restated in `engine/lib/`.
* A definition is followed by its lemmas and then disabled, in the defining book. A proof enables what it opens.
* No `"Subgoal"` hints: a case that needs one becomes a lemma. Few hints; before a `:use` or `:expand`, try the fact as a rewrite rule.
* Step limits (`set-prover-step-limit`), never time limits.
* Names: `f-of-g`, `-when-hyp`, `-under-equiv`; never `lemma1`, `crock`. Generated lemmas are `<rule>-<property>`.
* State lemmas with `mv-nth`, not `cadddr`; keep `mv-nth` disabled.
* Rules that loop together get a `theory-invariant`.
* A rewrite rule about a head keyword is stated in both orientations, `(equal (car x) kw)` and `(equal kw (car x))`.
* `defun`/`defthm` only; spaces, no tabs, no trailing whitespace; a header line pointing at `LICENSE`.
Never open `W3T::STEP` with the rule definitions enabled. Reason about a rule function through its generated lemmas.
A generator prints one line per lemma, gives each lemma a step limit, and ends with a check that the lemmas missing are exactly the recorded ones.
The generated books are the specification. Never copy or edit them.
The engine calls the spec's numeric functions (plan.md D6). Do not re-implement arithmetic.
A theorem's hypotheses are part of the result. When one is added to make a proof go through, record it and its reason in the note and in PLAN "Current state".
When a proof attempt fails, keep the failed checkpoint in the note before trying another approach. If the checkpoint is a state the machine can reach, it is a machine bug: fix the machine and re-run its tests.
Numbers in PLAN come from a measurement, never from an estimate.
Every claim about a run says whether the module is inside the proved subset (plan.md D8). TeX's host calls are outside it (P1).
