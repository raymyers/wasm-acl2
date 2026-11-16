# The 3.0 step group in logic mode: go

- Milestone: E2 (all four items), and E4 item 2 (D4 (a), one function per rule)
- Date: 2026-11-15
- Repo commit: 78d1584 (before), this note's commit (after)
- Status: final
- Feeds engine plan: E2 exit, E4, §2 (starting point), D4, "Current state"
- Incorporated in engine plan: yes (E2, E4 item 2, §2, "Current state")

## Summary

- **Go.** `STEP`, `STEP_READ`, `STEP_READ/SPLIT`, `STEP/SEARCH21`,
  `STEPS/%FUEL`, `STEPS` and `EVAL_EXPR` are `:logic` in
  `translate/tests/sem-3.0/modes-3.0.lsp`. Theorems can mention them.
- Three things kept them in `:program`; everything else followed from
  these: no measure for the type substitution group, no common measure for
  the fuel group of type validation, and `$concatn_`. A fourth appeared
  once those were fixed: the termination proof of `REF_OK` was too large
  with the rules inline.
- The fix for the fourth is D4 (a): the translator now emits one function
  per rule, for every relation and every spec version. This is E4 item 2,
  done here because E2 needed it.
- 3.0 modes: `:program` 288 to 132 (113 of the 1,409 functions that
  existed before, and 19 of the 732 new rule functions). No function that was `:logic`
  or `:guards` got worse.
- No definition body changed. The changes are measure declarations, one
  lemma, and the move of each rule's term into its own function.

## Findings

### Why the step group was in program mode (item 1 and 2)

The M9 logs do not hold the failed attempts: `%TRY-LOGIC-T` is a
`make-event` with `:or`, and only the alternative that succeeds is kept in
the output. So the cause was found from the certified books instead:
`data/e2-logic/callgraph.lsp` lists every `:program` function reachable
from `STEPS` with its `:program` callees (output:
`data/e2-logic/callgraph-78d1584.txt`, 76 functions).

A `:program` function with no `:program` callee failed on its own. A
group of them that call only each other failed as a group. There were
three:

| Root | Why ACL2 could not admit it | Who needs it |
|---|---|---|
| `$SUBST_TYPEUSE` and 14 more (type substitution, one `mutual-recursion`) | Structural recursion on the first argument, but four functions hand it unchanged to another one (`$subst_typeuse` and `$subst_heaptype` to `$subst_deftype`, `$subst_valtype` to `$subst_reftype`, `$subst_storagetype` to `$subst_valtype`). No measure was given and the default fails | `$unrolldt`, `EXPAND`, so `$BLOCKTYPE_` (`block`, `loop`, `if`, `try_table`), `call_ref`, `STEP_READ`, `STEP` |
| The fuel group of `Heaptype_ok` (19 relations, 50 functions in one `mutual-recursion`) | The relation functions `R/%F` had the measure `(NFIX %FUEL)`, the helpers in the clique had a measure of their own or none, the entries `R` had none. ACL2 needs one measure that all agree with. Also three callees were `:program` because of the first root | `REF_OK` (`ref.cast`, so `call_indirect`), `REFTYPE_SUB` |
| `$CONCATN_` | The recursive call's argument is rebuilt by the iteration helper `$CONCATN_/ITER3`, so it is not syntactically a part of the input | `STEP_READ` (`array.new_data`) |

Which of these D5 reaches: all three. `block` reaches the first,
`call_indirect` the second. `$concatn_` is not used by any D5
instruction, but `STEP_READ` is one function per relation, so it needs
every callee in `:logic`.

`STEP` itself already had a measure (`%OM3` on the size of the
instruction list, config `:decreasing ("Step" 0 2)`), and it is admitted
with it once its callees are in `:logic`.

### The measures (item 3)

Tried first in a session on the certified books with `verify-termination`
(`data/e2-logic/probe-chain.lsp`), then put into the translator.

**Type substitution**: config entry `(:size-rank "type substitution"
:defs ("subst_typeuse"))`. The translator gives every function of the
group the measure `(%OM (ACL2-COUNT first-formal) rank)`. The rank is 0
for a function that hands its first argument to no other function of the
group, else 1 + the largest rank it hands it to; the translator reads the
"hands unchanged" edges from the bodies (`il2acl2/compile.lisp`,
`size-rank-measures`). Ranks found: `$SUBST_STORAGETYPE` 2;
`$SUBST_TYPEUSE`, `$SUBST_HEAPTYPE`, `$SUBST_VALTYPE` 1; the others 0.
Probe: 0.08 s, 43,109 prover steps.

**Fuel groups**: no config entry; every fuel group gets it
(`fuel-clique-measures`). One lexicographic measure:

| Function | Measure | Why it decreases |
|---|---|---|
| `R/%F` | `(%OM3 (NFIX %FUEL) 0 0)` | calls everything with `%FUEL - 1` |
| helper (`R/ALL<i>`, `R/SEARCH<i>`, ..., and the rule functions) | `(%OM3 (NFIX %FUEL) rank m)` | calls `R/%F` with the same fuel (rank is at least 1), a helper of smaller rank, or itself with a smaller `m`. `m` is its own measure if it had one, else the size of its first formal |
| entry `R` | `(%OM3 (1+ (%TFUEL)) 0 0)` | calls `R/%F` with `(%TFUEL)` |

Probe: 0.38 s, 114,347 prover steps.

**`$concatn_`**: config entry `(:termination "concatn_" :measure (len
%a0) :lemmas (...))`. The translator emits the lemma
`$CONCATN_/ITER3-LEN` (the helper keeps the length) before the function
and gives the function the measure. If the helper is renumbered, the
lemma fails and certification stops.

With these three, and the rules still inline: `:guards` 430, `:logic` 848,
`:program` 131. `EXPAND`, `$BLOCKTYPE_`, `HEAPTYPE_SUB` were `:logic`.
`REF_OK`, and so `STEP_READ` and `STEP`, were still `:program`.

### Failed attempt: `REF_OK` with the rules inline

Checkpoint kept as the plan asks. `REF_OK` and `REF_OK/SPLIT` had the
right measure already. `data/e2-logic/probe-refok.lsp` runs the
termination proof with the hints of `%GZ-VERSION` and a 120 s limit: it
**succeeds, in 55.88 s of proof and 37,894,051 prover steps**. The limits
of `%TRY-LOGIC-T` are 20 s and 2,000,000 steps, so the event fell back to
`:program`.

Cause: a relation function was a chain `(LET ((%R rule-1)) (IF %R %R (LET
((%R rule-2)) ...)))`. The recursive call of rule k is then governed by
the failure of rules 1 to k-1, each a nested conjunction, and the prover
splits on all of them. The proof needs only the size check that stands
right before the call.

Raising the limits was rejected: 56 s on this machine is not a bound on
another machine, and `STEP` has four recursive rules after 37 others.

### One function per rule (D4 (a); E4 item 2)

`il2acl2/compile.lisp`, `crel-1-body`. For a relation function `FN` and a
rule with id `id`:

- the rule's term is the body of `FN/R-<ID>` (id in upper case), with the
  relation's formals;
- `FN` is the same chain as before over the calls:
  `(LET ((%R (FN/R-A args))) (IF %R %R (LET ((%R (FN/R-B args))) ...)))`;
- an id that occurs twice in the relation gives `FN/R<pos>-<ID>`, an empty
  id (a relation with one unnamed rule) gives `FN/R<pos>`; `pos` counts
  the rules of the function from 0.

Examples: `STEP_PURE/R-IF-TRUE`, `STEP/R-CTXT-LABEL`,
`STEP_READ/SPLIT/R-BLOCK`, `EVAL_EXPR/R0`.

Measures in a recursive group that is not a fuel group, for inputs of
size `all` with decreasing component `dec`:

| Function | Before | Now |
|---|---|---|
| relation `R` | `(%OM3 dec (1+ all) 0)` | `(%OM3 dec (1+ all) 1)` |
| rule function | (none) | `(%OM3 dec (1+ all) 0)` |
| search inside a rule | `(%OM3 dec all c)` | `(%OM3 dec all (1+ c))` |
| memoized entry (config `:memoize`) | last component 1 | last component of `R` plus 1 |

A rule function that does not reach the group is not recursive; ACL2
rejects a measure there, so the translator removes it
(`strip-bogus-measures`).

The generated size check before a recursive premise is unchanged. The
`%RULE` tag stays inside the rule function, so the demo's rule recorder
sees the same names.

With this, `REF_OK` is admitted within the normal limits, and so is the
`STEP` clique.

### Result (item 4)

All runs on 2026-11-15, darwin arm64, `JOBS=8`, in `nix develop`.

| Check | Result |
|---|---|
| `make -C translate check` (1.0) | pass. `gen/wasm-1.0` regenerated and committed; `check-gen` (two fresh runs identical) passes |
| `make -C translate check-2.0` | pass: T3 numerics 8,724 of 8,724, T3 SIMD 528 of 528; 2 min 15 s |
| `make -C translate check-3.0` | pass: T3, T5 (46 of 46), T6 (24 of 24), `t0-modes-3.0`, stubs 0; 5 min 9 s (M9: 4 min 45 s) |
| 3.0 manifest | before `:guards` 429, `:logic` 692, `:program` 288 (1,409 functions); after `:guards` 607, `:logic` 1,402, `:program` 132 (2,141 functions). Worse: 0. Better: 175. New: 732 (`:guards` 177, `:logic` 536, `:program` 19) |
| 1.0 manifest | before `:guards` 160, `:logic` 308, `:program` 35 (503 functions); after `:guards` 205, `:logic` 414, `:program` 57 (676 functions). Worse: 0. Better: 0. New: 173 (`:program` 22) |
| The new `:program` rule functions | all belong to relations that were `:program` before (`INSTR_OK`, `INSTRS_OK`, `EXPR_OK`, `MODULE_OK/W`, ...) |
| spec-test-3, per command | 258 scripts: 257 with the same sequence of results as before, 0 different, 1 (`bulk-memory--memory_copy`) stops earlier than before, at command 4,219 (see below). 64,778 commands with the same result in both runs. Total 11 min 46 s (M9: 11 min 18 s) |
| spec-test-1, per command | 67 scripts: 65 the same, 0 different, 2 (`call`, `call_indirect`) at the time limit in both runs (this run used 900 s per script, the earlier one 3,600 s). 11,992 commands with the same result in both runs |
| `make -C demo check` | every target passes when run by name (`jscl-hello wabt-hello browser-hello vectors units host conformance-quick smoke lines chains`, exit 0; the rule chains of W8 and the 224 steps of W6 included). `check-extract` also asks for a clean `translate/` tree, so the whole gate was run on the commit: DEMOFULL |
| `make -C engine check` | pass (new gate) |

`compare-modes.py` and `compare-spec.py` in `data/e2-logic/` made the
manifest and per-command rows. The spec-test result directories are not
checked in; the comparison was against the directories of the last runs
before the change, as they stood in `translate/tests/spec/` (their totals:
spec-test-3 63,326 of 63,883; spec-test-1 10,891 of 11,611).

**`bulk-memory--memory_copy`, command 4,219.** The command is the action
`test` of module 96: about 130 `memory.fill` instructions, each of
hundreds to thousands of bytes, in one function. In the results directory
from before the change the action has no result line: it aborted, the
session went on, and the script reached its end within 600 s. The reason
for that abort is not in the output. With the new code the action does
not abort and does not finish within the limit. Run alone
(`data-3.0` script with only this module and action):

| Code | CPU time when stopped | Finished |
|---|---|---|
| new (this commit) | more than 34 min | no |
| old (`78d1584`, built in a scratch worktree) | more than 29 min | no |

So the old code does not finish this action either, and the abort of the
earlier run did not happen again with it. The 4,218 commands before it
have the same results. What the earlier abort was, and why a step costs
this much here (the driver stops after 200,000 steps), are open; the
second is a case for the E0 profile.

Step cost on the M3 benchmark (`runtime-M3-2026-11-14/bench.lsp`, ms per
step, M3 value then new): counting loop, no memory 0.012, 0.014; 1 page
0.011, 0.013; 4 pages 0.011, 0.013; with a store and a load, 1 page 0.029,
0.032; 4 pages 0.059, 0.065. `data/e2-logic/bench-bulk.lsp` (new code
only, 1 page): `memory.fill` of 400 bytes 801 steps at 0.082 ms;
`memory.copy` of 400 bytes 1,201 steps at 0.107 ms.

The 3.0 spec run is about 4 % slower than M9's. A rule is now a function
call. E0 measures the step cost on the new code.

## Hypotheses and limits

- The modes depend on a 20 s prover time limit (M9). The manifest is what
  this machine gives (darwin arm64, 8 jobs).
- The fuel bound `(%TFUEL)` = 10,000 and the size checks are part of the
  definitions, as before. A theorem about `STEP` is a theorem about these
  definitions.

## Open questions

- Why the action of `bulk-memory--memory_copy` module 96 aborted in the
  earlier spec run, and why it is so slow (above).
- 132 functions are still `:program` in 3.0. None is reachable from
  `STEPS`. `INSTR_OK`, `MODULE_OK` and the decoder (`GRAM/...`) are among
  them, so D2 (no typing hypothesis) still stands.
- The rule functions of `STEP_READ` are not all guard-verified. The engine
  does not execute them, so this costs nothing yet.

## Data

`data/e2-logic/`:

- `callgraph.lsp`, `callgraph-78d1584.txt`: the `:program` functions below
  `STEPS` before the change.
- `probe-chain.lsp`: the measures tried with `verify-termination` on the
  books of 78d1584.
- `probe-refok.lsp`: the `REF_OK` attempt with the rules inline.
- `bench-bulk.lsp`: step cost of `memory.fill` and `memory.copy`.
- `compare-spec.py`: compares two spec-test result directories command by
  command.
- `compare-modes.py`: compares two manifests (the one before is in git at
  78d1584): the functions whose mode got worse (none), better, and the new
  ones.
