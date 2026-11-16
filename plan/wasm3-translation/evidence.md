# Evidence that the generated WASM 3.0 semantics is correct, and threats to validity

Written 2026-11-16 for the ACL2 Workshop. It gathers what the notes
and recorded data of [plan.md](plan.md) (M0 to M9) show, plus the later
results of the demo and engine plans that bear on the same generated
books. Sections 1 to 5 describe the committed state: nothing was re-run
for them, and every number is copied from a note or a data file, which is
linked. Section 6 (added later the same day) reports new runs that
re-examined the failing suite commands. Its code is in a separate
worktree and is not committed or merged yet.

**In one paragraph.** `translate/gen/wasm-3.0` (25 books, about 349,000
lines) is generated from the SpecTec IL of `WebAssembly/spec@943c5df` and
certifies in ACL2. No theorem connects it to the SpecTec source: the
translator is trusted, and the evidence for correctness is testing. The
main test is the official suite: 63,326 of 63,883 spec-test-3 commands
pass (99.1%) in the committed state, with every valid module accepted and
every `assert_trap` passing. Of the 557 that failed, 446 had an
unconfirmed explanation. They were re-examined on 2026-11-16 (§6): with
five performance fixes in the translator and runtime, corrected test data
and a larger step budget, **64,005 of 64,018 pass (99.98%)**, the 446
among them, and no remaining failure is a wrong result. Most of the bugs found during the work were of
one kind, a valid derivation silently cut, and each was found only by
running tests, so the same kind of bug may remain where the tests do not
reach.

## 1. What "correct" means here

The claim under test: for the files `0.*` to `5.*` of the pinned 3.0
spec (syntax, validation, numerics, execution, binary format; 25 of 37
files, 509 rules in 85 relations), the generated ACL2 functions compute
what the SpecTec rules define, restricted to the deterministic profile
(decision D4).

Three things are outside the claim:

- The text format (`6.*`) and the soundness judgements (`7.*`) are not
  translated (deferred, plan §5).
- The semantics is a function, not a relation. Where the spec allows
  several results, one is fixed (§4.5).
- The input is SpecTec's elaborated IL, not the `.spectec` source or the
  prose. SpecTec's front end is trusted (§4.1).

## 2. Evidence

### 2.1 What ACL2 checks

| Fact | Value | Source |
|---|---|---|
| Stubs and dropped rules in scope | 0 and 0 | [M7-module-ok](notes/M7-module-ok.md), plan M6 exit |
| Reduction rules translated (`Step`, `Step_pure`, `Step_read`) | 218 of 218 | [M3-execution](notes/M3-execution.md) |
| `Instr_ok` rules translated | 110 of 110 | plan M6 |
| Certification | all 25 books, no `skip-proofs` or `defaxiom` in `gen/wasm-3.0` or `rt/` (grep, 2026-11-16) | `make check-3.0` |
| Function modes after M9 | `:guards` 429, `:logic` 692, `:program` 288 | [M9-logic-mode](notes/M9-logic-mode.md) |
| Function modes now (after engine E2) | `:guards` 607, `:logic` 1,402, `:program` 132 | `translate/tests/sem-3.0/modes-3.0.lsp`, [E2-step-logic](../wasm-engine/notes/E2-step-logic.md) |

Certification shows that the definitions are admissible (they terminate),
and for the guard-verified ones that they never call a function outside
its domain. It does not show that they say what the spec says. The
generated books contain no theorems about the semantics.

### 2.2 The official test suite (spec-test-3)

`make spec SPEC=3.0`, 258 of 259 scripts (not `skip-stack-guard-page`),
with validation on
([data](notes/data/module-M7-2026-11-15/TOTAL.txt), [M7-module-ok](notes/M7-module-ok.md)):

| Command kind | Pass / counted |
|---|---|
| `module` (valid module decodes, validates, instantiates) | 2,263 / 2,263 |
| `assert_return` | 52,117 / 52,643 |
| `assert_trap` | 4,924 / 4,924 |
| `assert_exception` | 18 / 18 |
| `action` | 357 / 357 |
| `assert_invalid` | 2,683 / 2,690 |
| `assert_malformed` (binary) | 710 / 710 |
| `assert_unlinkable` | 200 / 200 |
| `assert_uninstantiable` | 54 / 54 |
| commands that aborted (counted as failed) | 0 / 24 |
| **all** | **63,326 / 63,883** |

The run covers the whole path: the generated binary parser, `Module_ok`,
`$instantiate`, `$invoke` and `Steps`. It includes the GC and exception
scripts (`ref_test` 71/71, `ref_cast` 45/45, [M5-trans](notes/M5-trans.md)).

The 557 failures by recorded cause ([M4-conformance](notes/M4-conformance.md),
[FAILKINDS](notes/data/module-M7-2026-11-15/FAILKINDS.txt)):

| Count | Cause as recorded | Confirmed? |
|---|---|---|
| 446 | `memory_copy`, `memory_copy64`: checks after a `test` action that aborted | **No.** The action did not finish in 15 min (M4) or 34 min (E2) alone. Small copies and fills were checked by hand |
| 43 | step budget of 200,000 per action (`return_call*` to 1,000,000, fill and grow loops) | by the failure kind (`:FUEL`) |
| 33 | relaxed SIMD: wabt wrote the `either` expectations as `()` | attributed from the data; not re-run with corrected data |
| 4 | wrong result after an aborted grow | follows from the abort |
| 24 | aborted commands: large `memory.grow`/`table.grow` (14), "too many locals" (2), deep recursion (2), others (6) | listed in `ABORTED.txt` |
| 7 | `assert_invalid` with no usable binary (3 text-only, 4 that the reference interpreter also refuses to decode) | yes, against the reference interpreter |

No failure is recorded as a wrong answer of the semantics. That
statement is only as strong as the "Confirmed?" column. §6 re-runs these:
the first four rows are now confirmed or gone.

### 2.3 Numeric vectors against V8

`make check-3.0` ([M1-builtins](notes/M1-builtins.md)): 8,724 of 8,724
scalar vectors and 1,008 of 1,008 SIMD vectors agree with V8. Of the SIMD
vectors, 480 are relaxed SIMD, checked against V8 running the strict
equivalent (the deterministic profile). This is the only check of the
hand-written numerics in `rt/` besides the spec tests.

### 2.4 Hand-made validation cases

| Book | Cases | Oracle |
|---|---|---|
| `t5-subtyping-3.0` | 46 of 46 | the expected answers were read off the spec rules by the same sessions that wrote the translator ([M5-subtyping-cases](notes/M5-subtyping-cases.md)) |
| `t6-instr-typing-3.0` | 24 of 24 | V8's `WebAssembly.validate` ([M6-typing-cases](notes/M6-typing-cases.md)) |
| `t3-builtins-3.0` | 26 of 26 | hand-written expectations |

Both typing books were written before the fix they test and recorded the
failures first (35 of 46, 16 of 24). So they are known to be able to
fail.

### 2.5 Cross-checks of the test data

- The reference interpreter validates all 293 modules of the 31 scripts
  it converted and rejects all 290 `assert_invalid` ones
  ([M0b-test-data](notes/M0b-test-data.md)).
- Every decode miss of the first in-tree run (113) was given to the
  reference interpreter. In 70 cases the generated parser was right and
  the test data wrong (wabt wrote a proposal outside 3.0)
  ([M2-decode](notes/M2-decode.md)).

### 2.6 Later use of the same books

These came after M9 and were not designed as tests of the semantics.

- **Regression after two translator changes** (rule tags, one function
  per rule): spec-test-3 results compared per command, 64,778 the same,
  0 different ([E2-step-logic](../wasm-engine/notes/E2-step-logic.md),
  [W7-rule-tags](../wasm3-demo/notes/W7-rule-tags.md)). The numbers of
  §2.2 therefore still describe the current generated code, up to
  `memory_copy`, which now stops earlier.
- **A real module**: a 4.5 MB build of MuPDF (4,470 functions) passes the
  generated parser and `Module_ok`
  ([E1-mupdf-target](../wasm-engine/notes/E1-mupdf-target.md)). The full
  10 MB module's parse was stopped after 434 CPU minutes.
- **A real program**: a slide renderer compiled from C produces pixels
  identical to V8 for 7 of 7 slides
  ([E12-slides](../wasm-engine/notes/E12-slides.md)). It ran on the
  engine's list machine, which applies the generated rule functions and
  agreed with `STEP` in every differential test, but the proof that links
  the two is unfinished. Decoding and instantiation were the generated
  semantics' own.
- **Browser demo**: the semantics, ported to JavaScript, gives the same
  results as native WebAssembly on 8 example runs in two browsers
  ([W5-browser-page](../wasm3-demo/notes/W5-browser-page.md)). The port
  agrees with ACL2 on 7,087 of 7,087 commands, which is evidence about
  the port, not the semantics.
- **Proofs about `STEP`**: the engine work proved lemmas about the
  generated step functions, among them that a value, `TRAP` and an
  uncaught exception do not step
  ([E3-theorem](../wasm-engine/notes/E3-theorem.md)). The definitions can
  be reasoned about. These are not correctness theorems.

### 2.7 Bugs the process found

This list is evidence that the tests can find translation errors, and it
shows which kind of error is typical.

| Bug | Found by |
|---|---|
| Termination check cut valid derivations in the 19-relation type group (9 of 22 cases right) | running hand-made cases in a review ([review-checker-blind-spots](notes/review-checker-blind-spots.md)) |
| Same kind: `Ref_ok` (no externref had a type) | spec-test-3 (M4) |
| Same kind: `Types_ok`, `Globals_ok` (no module with two types validated) | spec-test-3 (M7) |
| Partial inverses bound an option, not its element (all float vector comparisons, 5,240 asserts) | spec-test-3 (M4) |
| Equation with a variable-free option (`br_on_non_null`) | spec-test-3 (M7) |
| `Heaptype_sub/trans` dropped, though not admissible | reading the rules, then cases (M5) |
| Generated instruction typing had no subsumption (8 of 24 valid bodies rejected) | V8 cases (M6) |
| `%FUEL` passed to functions that do not use it; `:multi` propagated into `Step` | certification |
| `$utf8` accepted surrogates (39 malformed modules accepted; also in 1.0) | spec-test-3 decode (M2) |
| SpecTec elaborates `Belem` flags 0-3 to one expression | reading the decode output (M2) |

Every one of the first seven made the semantics reject or get stuck on
something valid, and the probe and certification reported nothing for
any of them. Only the `$utf8` bug accepted something invalid. No bug
that was found produced a wrong value from a step that fired.

## 3. What is hand-written

The spec-derived part is generated. These parts are not:

| Part | Size | What supports it |
|---|---|---|
| Translator `il2acl2/` | 5,569 lines of Lisp | everything in §2; no proof |
| Runtime `rt/` (numerics, SIMD, floats, bytes, UTF-8) | 777 lines | V8 vectors (§2.3), spec tests. Not reviewed line by line ([review](notes/review-checker-blind-spots.md) §5) |
| `Instrs_ok` sequencer (`:rel-override`) | in the config | Replaces the generated sequence rules (`empty`, `seq`, `sub`, `frame`). The generated `INSTR_OK` and `RESULTTYPE_SUB` check each instruction's proposed type, but the sequencing itself is hand-written. Tests: 24 V8 cases, 2,263 valid modules, 2,683 invalid |
| `Module_ok` proposer (`:given-entry`) | about 45 lines | Proposes the two contexts; the generated rule checks every premise. A wrong proposal can only reject |
| 4 `:il-patch` entries | 1 `Belem`, 3 `Instr_ok` | Change the IL before translation. `Belem` follows the prose. The 3 `Instr_ok` patches set `x* = []`, argued equivalent by `Instrs_ok/sub` |
| 2 `:def` overrides (`utf8`, `utf8single`) | | spec-test decode; `utf8single` is called by no generated code |
| Other config entries (`:decreasing`, `:fuel`, `:split`, `:sized`, `:witness`, `:memoize`, `:builtins`, ...) | 19 entries in all, 214 lines | reviewed one by one, with a reason in the config |

## 4. Threats to validity

### 4.1 No formal link to the spec

The translator, SpecTec's elaboration and the IL printer patch are
trusted. Correctness rests on tests. A translation error in a rule that
no test exercises would not be seen. Dynamic rule coverage of the suite
was not measured: the 218/218 "coverage" in W7 says that every rule has a
tag in the generated code, not that a test fired it.

### 4.2 Silent incompleteness, the bug class that keeps recurring

Recursive relations are guarded by a generated size check or by fuel. If
the check is wrong for a rule, the rule never fires and nothing reports
it. This was found four times (§2.7), each time only by a behavioural
run. The plan says so itself: "the probe cannot tell, only behavioural
cases can" (§7). Any relation whose recursive rules the tests do not
reach may still be cut. Related:

- The type group's fuel bound (10,000) was never reached by a test. Its
  safety for the Lisp stack is an estimate.
- For `Heaptype_sub/trans`, five rule kinds are left out of the
  enumeration. Each has a written completeness argument. Two of the
  arguments (`typeidx-r`, `Deftype_sub/refl`) were made from the rules
  and are not checked by any test ([M5-trans](notes/M5-trans.md)).
- Four relations (`Instr_ok`, `Instrs_ok`, `Ref_ok`, `Externaddr_ok`)
  rely on a single witness where the spec has an existential.

### 4.3 The tests are weak in the direction where the bugs are

- `assert_invalid`, `assert_malformed` and `assert_unlinkable` pass when
  the module is rejected for any reason. A validator that rejects too
  much passes them. Only the 2,263 valid modules, the 24 V8 cases and
  one MuPDF build test acceptance. The spec-test modules are small.
- `assert_trap` checks that the action trapped, not why.
- Not counted at all: `assert_exhaustion`, text-format
  `assert_malformed`, and the script `skip-stack-guard-page`.
- 557 commands fail in the committed state. The largest group (446) had
  an unconfirmed explanation (§2.2). **Resolved in §6**: `memory_copy`
  and `memory_copy64` now finish and pass every command.
- Two scripts, `call` and `call_indirect`, are killed at a slow command
  (deep recursion), and the commands after it are never tried: about 55
  and 85 commands. They are missing from the
  denominator of the committed totals; the run of §6.2 includes them.

### 4.4 Test data and oracles

- wabt's conversions have wrong expectations in 9 scripts (`either`
  results written as `()`, one misrounded subnormal). 228 of 259 scripts
  still go through wabt. The recommendation to convert everything
  through the reference interpreter is open ([M0b-test-data](notes/M0b-test-data.md)).
  Besides the 33 known relaxed-SIMD failures, `memory_grow64` and
  `table_grow64` have the same `()` expectations. **Done in §6**: with
  every script converted by the reference interpreter, the 33 pass and
  all 2,690 `assert_invalid` are checked.
- V8 is the numeric oracle, on one machine (arm64). An error shared by V8
  and `rt/` would pass. V8 does not follow the deterministic profile for
  relaxed `madd`/`nmadd`, so those vectors use a strict equivalent chosen
  by us.
- The 46 subtyping expectations were derived by the same sessions that
  wrote the translator, from the same rules. They are not independent.

### 4.5 Determinism and rule order

- The semantics is the deterministic profile: `$ND` false, relaxed SIMD
  takes the first alternative, numeric results take the first element of
  the list a builtin returns (14 premises). It is one behaviour the spec
  allows, not the set of all of them. Nothing can be concluded from it
  about other conforming engines' NaN bits or relaxed results.
- Relations compiled as functions take the first rule that applies.
  Three kinds of silent single choice are not counted by any report
  ([review](notes/review-checker-blind-spots.md) §4).
- `Step` uses a fixed redex strategy (`:split`). It was argued to reach
  the same results as the spec's evaluation contexts, possibly in a
  different number of steps. So agreement of results is the supported
  statement, not step-for-step agreement. The argument is written, not
  proved.

### 4.6 Scale and resources

- Memory is a list of bytes. Large memories, deep recursion and long
  loops abort or exhaust the step budget (67 commands in the committed
  state). §6 shows that most of these were not the representation but
  five avoidable costs in the generated code and its runtime. What stays inherent: a
  store into memory rebuilds the byte list (about 0.6 ms a step at one
  page), a step at call depth d costs d², and a memory of gigabytes
  cannot be built. The 10 MB MuPDF module did not finish parsing.
- `Module_ok` and `Instr_ok` are among the 132 functions still in
  `:program` mode. ACL2 cannot reason about them, and their termination
  is not proved. Execution (`STEP`, `STEPS`) is in `:logic` mode.
- The mode manifest depends on the machine (20 s prover limit per
  attempt).

### 4.7 How the work was done

- The translator changes, config entries, tests and notes for M0 to M9
  were produced in about 9.5 hours of Claude Code sessions on 2026-11-14
  and 15 ([sessions.md](sessions.md)). The user made the design decisions
  (D1 to D6, M5 to M7 strategies). The notes record one review session
  (also by the model) and no line-by-line human review of `il2acl2/`,
  `rt/` or the config.
- The same sessions wrote the code, chose the tests and classified the
  failures. The classifications in §2.2 are the author's own.
- 1.0 output was kept byte-identical through every 3.0 change, and the
  1.0 and 2.0 gates stayed green. That guards against regressions in the
  shared translator, not against 3.0-only errors.
- Everything is pinned to one spec revision. 3.0 at `943c5df` is not
  necessarily the published standard text.

## 5. What would strengthen the claim

In rough order of value for the effort:

1. Finish or bound `memory_copy` (446 commands), so that no failure is
   unexplained. Done in §6.
2. Convert all scripts through the reference interpreter (removes the 33
   relaxed failures and the `()` expectations). Done in §6.
3. Measure dynamic rule coverage of spec-test-3 with the existing
   `%RULE` tags: which of the 509 rules never fire.
4. More acceptance tests for validation: valid modules from real
   compilers, and differential validation against the reference
   interpreter on generated modules.
5. Differential execution against the reference interpreter or SpecTec's
   own interpreter, step results included.
6. Theorems in ACL2: determinism of `STEP` is by construction, but
   progress or preservation for a fragment (`7.*`) would test the typing
   and execution rules against each other.
7. A human review of the sequencer, the four IL patches and the two
   untested completeness arguments.

## 6. Update 2026-11-16: the failing suite commands, re-examined

Status of this section: the changes are in the git worktree
`../wasm-acl2-specfix` (branch `spec-test-fixes`, based on `843fb43`),
**uncommitted and not merged**. The main checkout still has the code that
§2.2 describes. Data: `notes/data/suite-fixes-2026-11-16/` in that
worktree (`TOTAL.txt`, `SUMMARY.txt`, `FAILS.txt`, `ABORTED.txt`).

### 6.1 What was wrong

None of the 557 failures was a wrong result of a rule. Most came from
five performance defects of the generated code or its runtime, found by
profiling the commands that never finished or aborted:

| Defect | Effect | Fix |
|---|---|---|
| A rule whose pattern is `A ++ B` with a searched split (`val* (BR l) ++ instr*` in `br-label-zero`, `br-label-succ`, `return-label`, ...) tried every split of a label's body and built every prefix | n² conses per rule per step for a body of n instructions: 33 ms and 57 MB a step on the `test` function of `memory_copy`, which never finished | translator, config `:search-start`: the search starts at the first element that has the tag the pattern requires next to the split. Only the start value passed to the search function changes |
| `e^n` with a constant element (`0x00^(n·64Ki)` in `$growmem`, `$allocmem`; table and array fills) was a helper that recurses outside tail position | one Lisp stack frame per element: growing or allocating more than about 20 pages aborted | translator, config `:constant-iter`: the helper is `make-list` |
| `$growmem` and `$growtable` built the grown contents before testing the size limit | a `memory.grow` that must return -1 (by 65,536 pages) first built gigabytes | translator, config `:tests-first`: in the listed defs a binding moves behind the steps that do not use it |
| The termination check of `Ref_ok` (under `ref.cast`, so every `call_indirect`) takes the size of all inputs, the store among them, with `acl2-count`, which recurses once per list element | stack exhausted once the store holds a memory of some hundred pages | runtime: `%SIZE` is executed by a loop (`mbe`; logically still `acl2-count`, equality proved) |
| A count that no machine can hold (2^32 locals, a grow by 2^48 pages) | exhausted the stack, or with `make-list` the heap, which ends the session | runtime: such a list stops the evaluation of that command with an error (`%LIST-SIZE-OK`, logically `T`) |

Each change leaves the computed value the same: the first by the
argument that no smaller split can match, the others because only the
evaluation order, the way a list is built or the executable body
changes. The `%SIZE` equality is proved in ACL2. The other arguments are
written in the config, not proved.

Three more causes were in the test setup: wabt's wrong expectations
(§4.4); a step budget of 200,000 per action, below what some valid tests
need (the `memory_copy` action takes 747,881 steps); and scripts killed
at one slow command, whose later commands were never run.

### 6.2 Full run with all fixes

`make spec SPEC=3.0` in the worktree: every script converted by the
reference interpreter (258 of 259; `inline-module` stays with wabt), a
step budget of 20,000,000 and 900 CPU seconds per action, 7 sessions,
2 h 0 min (most of it the recursion tests of `call` and
`call_indirect`). All 258 scripts ran to their end, for the first time.

| Command kind | Committed (§2.2) | With the fixes |
|---|---|---|
| `module` | 2,263 / 2,263 | 2,265 / 2,265 |
| `assert_return` | 52,117 / 52,643 | 52,737 / 52,745 |
| `assert_trap` | 4,924 / 4,924 | 4,930 / 4,930 |
| `assert_exception` | 18 / 18 | 18 / 18 |
| `action` | 357 / 357 | 359 / 359 |
| `assert_invalid` | 2,683 / 2,690 | 2,732 / 2,732 |
| `assert_malformed` (binary) | 710 / 710 | 710 / 710 |
| `assert_unlinkable` | 200 / 200 | 200 / 200 |
| `assert_uninstantiable` | 54 / 54 | 54 / 54 |
| aborted commands | 0 / 24 | 0 / 5 |
| **all** | **63,326 / 63,883 (99.13%)** | **64,005 / 64,018 (99.98%)** |

The denominator grew by 135: the commands of `call` and `call_indirect`
that no earlier run reached.

What happened to the earlier failure groups:

| Group (§2.2) | Now |
|---|---|
| 446 after the aborted `memory_copy` action | pass: `memory_copy` and `memory_copy64` 4,450 of 4,450 each. "Not a semantic problem" is confirmed |
| 43 step budget | pass with the larger budget |
| 33 relaxed SIMD | pass with the reference interpreter's data. The attribution to wabt is confirmed |
| 7 `assert_invalid` without a usable binary | pass: the interpreter writes all of them in binary |
| 4 wrong results after an aborted grow | pass |
| 24 aborted commands | 5 left (below) |

### 6.3 The 13 commands that still fail

| Commands | Cause | Kind |
|---|---|---|
| 8 `assert_return` over the time budget: the four `fib` tests and `odd(200)` in `call_indirect` (5), two in `call` (one of them `odd(200)`), one in `return_call_indirect`. Six of the eight were never reached by an earlier run | recursive calls: a step at call depth d costs d² (the termination check of the context rules) | cost of the executable form; no wrong result |
| 1 aborted in `call` | not yet diagnosed (a deep-recursion test) | open |
| 2 aborted in `binary` | malformed modules that declare 2^30 and 2^32 - 1 locals. The generated parser expands the locals before the spec's bound check | the module is rejected by an error, not by the rule |
| 1 each aborted in `memory64--memory_grow64` and `memory64--table_grow64` | a grow by 2^48 - 1 pages (2^64 - 2 table entries), which the spec allows to fail or to succeed. The deterministic semantics chooses to succeed and cannot build it | inherent to the deterministic choice (§4.5) |

None is a wrong value. The engine cannot help with the last four, which
are not execution steps or have no machine representation. For the
recursion tests it could: its machine keeps a context stack and has no
d² cost. That would be evidence about the engine and its (unfinished)
proof, not about the generated semantics running by itself.

### 6.4 Gates, and what is not done

- In the worktree with all fixes: `make check` (1.0), `check-2.0` and
  `check-3.0` pass. The 3.0 mode manifest is unchanged. The 1.0
  generated definitions are byte-identical; `gen/wasm-1.0/package.lsp`
  imports the new runtime symbols, so that committed file changes.
- The engine's 14 books certify against the final generated code (no
  `skip-proofs`, 14 min), with one change: a hand-written lemma in
  `engine/rules/terminal.lisp` was dropped, because the generated one now
  proves by itself. This is the engine at commit `843fb43`. The engine
  books that another session has since changed in the main checkout were
  not tested against the new generated code.
- The demo builds and its test targets pass (numeric vectors, units,
  host, the conformance subset 6,896 of 6,896 commands agreeing with
  ACL2, stepper lines and chains, browser smoke test), after its shim
  gained the three ACL2 forms that the runtime now uses (`prog2$`, `mbe`,
  `er`). Its `check-extract` target was not run: it requires a clean
  `translate/` tree.
- A suite driver that runs each action on the engine's fast machine and
  falls back to the semantics where the engine refuses
  (`engine/fast/suite-one.lsp`) was tried on four scripts: 281 of 286
  actions were decided by the engine, all passing. It removed no abort,
  because the aborts were in generated functions that the engine also
  calls (`$growmem`). That is how the defects of §6.1 were found.
- Nothing is committed. The plan's notes index and `plan.md` are not
  updated.

### 6.5 What this changes in the assessment

- The claim "no failure is a wrong answer" no longer rests on an
  unconfirmed attribution: the 446 pass, and of the 13 failures left
  (some of them commands that no earlier run reached) 12 have a known
  cause and one is not yet diagnosed.
- The defects found are of a new kind for §2.7: the right value, at a
  cost that made valid programs unrunnable. The suite showed them only as
  timeouts and aborts, which had been filed as resource limits. "Resource
  limit" was an explanation that hid five defects.
- The threats of §4.1 to §4.3 are unchanged: these runs add passing
  commands of the same kinds, not a new kind of evidence.
- The semantics that passes 99.98% is not byte for byte the one of §2.2:
  it has three new config entries and two runtime changes, argued to
  preserve every value. The count of config entries (§3) rises from 19
  to 22.
