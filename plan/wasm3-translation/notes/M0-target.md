# 3.0 as a target: IL checked in, `make check-3.0`, in-tree certification

- Milestone: M0 (items 1 and 2)
- Date: 2026-11-14
- Repo commit: c9fe71d plus this note's commit
- Status: final
- Feeds wasm3 plan: §5 M0 (done), §6 (config budget), "Current state"

## Summary

3.0 is a target like 2.0. `il/wasm-3.0.il.sexp` and its decls are checked
in (`check-il SPEC=3.0` reproduces them), and `make check-3.0`
regenerates `gen/wasm-3.0` and certifies it in-tree, in `:program` mode.
Measured: **`make check-3.0` takes 1 min 32 s** (certification alone
1 min 26 s, 79 s of it in `certify-book`, 45 s in `5_3-binary_instructions`).
The prep's experiment certified in 97 s, but from a scratch tree with
hand-made stubs and a patched `rt/prelude.lisp`. None of that is needed
any more. The 1.0 gate (`gen/wasm-1.0` byte-identical) and the 2.0 gate
(8,724/8,724 numeric and 528/528 SIMD vectors) stay green. The probe is
unchanged: 2 stubs, 3 dropped rules, 0 declared modes.

Four changes were needed. Two are config entries and are listed for the
user: `:program`, and `:recursive nil` added to the `:memoize` entry.

## What changed

1. **Builtins that `rt/` lacks become stubs** (translator, `cdef` in
   `compile.lisp`). A clause-less def whose mangled name `rt/` does not
   define is emitted as a defun that signals an error. It is listed with
   the stubs in the `wasm3.lisp` header. Before, the generated code called
   an undefined function, so certification failed (the prep experiment
   added 46 stubs by hand). **3.0 stubs: 27** = `Module_ok`,
   `$utf8single` (the 2 of the probe), the 13 numeric builtins of plan §3,
   the 11 choice parameters (`$ND`, `$R_*`) and `$hostcall`. M1 removes
   the last 25 by defining them in `rt/`. The old header line "Numeric
   builtins with no definition in rt/ yet" stays (13 names), now saying
   "emitted as stubs until added". 1.0 and 2.0 have no such builtin, so
   their output does not change. The probe does not pass the `rt/` names
   into this check, so its stub count still means "untranslatable forms" (2).

2. **Config `:program`** (new entry, `config/wasm-3.0.lsp`). Every part
   starts with `(program)` instead of `(set-verify-guards-eagerness 0)`,
   and the events go out without `%TRY-LOGIC` / `%TRY-GUARDS`. Reason (in
   the entry): this bounds certification time. One guard proof in
   `5_2-binary_types` ran more than 15 CPU minutes in the prep (P5), and
   the step limits do not bound wall time. Execution is the same. M9
   removes it. I did not add a macro to `rt/`: a new `rt/` name would
   change the import list in `gen/wasm-1.0/package.lsp`.

3. **Fuel only where it is used** (translator, `fuel-wrap`). The first
   in-tree certification failed in `2_1-validation_types`: ACL2 rejects
   `SUBTYPE_OK2/ALL1`, whose `%FUEL` formal (added by M5's fuel group) is
   irrelevant. That aux calls only itself and a builtin. Now a function of
   a fuel group takes `%FUEL` only if its body mentions it (the relation
   functions) or calls, transitively, one that does. M5 and M6 had loaded
   3.0 with proofs skipped, which hid this. It is the second translator
   bug found by certifying 3.0, after the prep's `close-aux-formals`.

4. **`:memoize ... :recursive nil`** (option added to the 3.0 entry;
   translator `memo-wrap`). With certification green, it took 7 min 6 s:
   each of the 12 books after `2_3-validation_instructions` spent 22 s
   including it. Measured in a session: `(memoize 'instr_ok/%m)` alone
   took 17 s, because memoize recompiles the function's huge body inline.
   With `:recursive nil` it wraps the compiled function. The recursion
   still goes through the memoized function, because `R/%M` recurses only
   via its entry `R`, which calls the global `R/%M`. Measured on the
   certified books, 17 instructions, ill-typed (`memo-case.lsp`):
   **0.01 s memoized, more than 300 s (killed) unmemoized**. 1.0 keeps the
   default (byte-identical output); the option exists only in the 3.0 entry.

## Behaviour on the certified books

The M5/M6 typing cases (`typing-M6-2026-11-14/cases-3.0*.lsp`) run on
the certified in-tree books (`run-cases.sh`, 1.9 s for everything) and
give the same 49 results as M6 and M5 recorded on the scratch copy with
proofs skipped (`results-certified.txt`; the only differences are line
wraps). The same cases are still wrong (`trans`, subsumption in M6), as
expected.

## Config budget after M0

`config/wasm-3.0.lsp`: 9 entries (`:def utf8`, `:builtins`, `:split`,
`:decreasing`, `:memoize` (now with `:recursive nil`), `:sized`,
`:witness`, `:fuel`, `:program`). The "PROVISIONAL" header is gone. The
entries are validated against the IL on every run (`config-entry-errors`,
now also for `:program`). The `:witness` reason still says "PROVISIONAL
... not yet argued for 3.0"; that argument belongs to M6.

## Data

`data/target-M0-2026-11-14/`: `run-cases.sh` (the cases on the certified
books) with `memo-case.lsp`, `results-certified.txt`; `cert-times.sh` and
`cert-times.txt` (per book); `probe-3.0-core.txt` (the probe after M0);
`wasm3-header-lists.txt` (builtins, stubs and dropped rules from the
`wasm3.lisp` header).
