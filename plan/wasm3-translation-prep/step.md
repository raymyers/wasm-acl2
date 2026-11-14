PLAN is plan/wasm3-translation-prep/plan.md

Execute these steps:

* Study PLAN and choose the next logical milestone item (P0..P7, respecting the dependency order in §5).
* Check for uncommited changes, it will be your choice to finish or discard.
* Complete and verify task. WASM 1.0 must still pass `make -C translate check`.
* If successful
  * Then Update PLAN to mark task complete (with measured results), commit
  * Else bail.

# Tech guidelines

Use Nix to run all toolchain.
Numbers in PLAN come from the probe or a test run, never from estimates.
