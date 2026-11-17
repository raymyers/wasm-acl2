# Rule tags in the translator
- Milestone: W7 (rule tags in the translator, D7)
- Date: 2026-11-15
- Repo commit: d716fa8 (parent; baseline); implementation in the W7 commit
- Status: final
- Feeds demo plan: W7, W8 (the recorder), W2 (event table sees `%RULE`)
- Incorporated in demo plan: yes (W7)

## Summary
Every IL rule of every relation, in every compiled variant, returns its
result through `(%RULE "Rel/rule-id" result)`; every grammar production
through `(%RULE "Gram/#k" result)`. In ACL2 `%RULE` is a macro of
`rt/prelude.lisp` that expands to `result`, so the translated terms (what
ACL2 stores, proves and runs) are the same as before. JSCL's shim (W8)
defines it as a recorder. One emitter change in `crule` and one in
`cprod`; no change to function definitions.

## Design (item 1)

### Where the tag goes
`il2acl2/compile.lisp`, `crule` compiles one IL rule into
`(build-steps-cx steps (list 'list out) cx)`: the steps (pattern matches,
premises, searches) guard the success expression `(list out)`, which is
evaluated only when every premise of the rule holds. The tag wraps `out`
**inside** the list:

```lisp
(list (%RULE "Step_pure/nop" out))      ; was (list out)
```

Inside, not around, because `chain-results` (and `crules`' callers)
recognize an unconditional rule by the shape `(list x)` (length 2, head
`list`): wrapping the whole `(list out)` would change which rules are
treated as unconditional, and so the shape of the generated chains. With
the tag inside, the emitted structure is the old one with `out` replaced.

`out` is the rule's output for the output modes (`(:out i)`, `:split`,
`:fun`, `:fun2`, given mode) and `t` for `:check`.

### Per relation shape
| shape | tagged? | how |
|---|---|---|
| plain clause chain (check, output variants) | yes | `crule` for every rule |
| split `Step` (config `SPLIT Step`) | yes | its rules go through `crule`; the split search is in the steps before the success expression, so the tag fires once, for the candidate that succeeds |
| search helpers (`/SEARCHn`, `:choose`) | inside | the success expression (with the tag) is inside the search body (`build-steps-cx`), evaluated only for a successful candidate |
| iteration / map helpers (`/MAPn`, `/ITERn`), match helpers (`/MATCHn`) | no tag of their own | they compute premises; the rule's tag is on its conclusion |
| enumeration variants `R/ENUMi` (`:collect`) | yes | `crule` in `(:out i)` mode; each rule's result list holds tagged values |
| kept variants (`INSTR_OK/OUT2`), `R/SPLIT` | yes | same `crule` |
| `:given-entry` (`MODULE_OK/W`) | yes | `crule` in given mode; the hand-written proposer `MODULE_OK` is not tagged |
| `:rel-override` (`Instrs_ok` sequencer) | **no** | hand-written in rt/, no IL rule (the rules `Instrs_ok/empty, instr, seq, sub, frame` have no tag) |
| per-rule stubs (`:drop-rules`, crel-partial) | no | the rule is not compiled |
| closure relations (`Steps`, mode `:closure`) | no | the fuel loop is generated without its two rules (`refl`, `trans`); every iterated `Step` call tags its own rules |
| fuel groups (`%TFUEL`) | yes | same `crule`; the fuel wrapper is outside |
| grammar productions (`cprod`) | yes | `(list (%RULE "Gram/#k" r) pv)`, see below |
| function definitions (`cclause`) | no | SpecTec `def` clauses have no ids and are not relations |

### Names
- Relations: `Rel/rule-id`, exactly the string `crules` already builds for
  error contexts and `:drop-rules` (`(concatenate 'string rel "/" id)`),
  with the IL's relation and rule ids, e.g. `Step_pure/nop`,
  `Step/ctxt-instrs`, `Step_read/call_ref-func`. The same string is what
  the probe and the generated header use for dropped rules, so coverage
  (item 5) compares like with like.
- Grammar productions have no id in the IL (`(prod params... sym exp
  prems...)`). Their tag is positional: `Gram/#k`, `k` the 1-based index of
  the production in its grammar as the IL lists it (e.g. `Binstr/#2` for
  the second production of `Binstr`). For an inlined parametric grammar the
  name is the parametric grammar's own (`:gram-name` at that point).

### Semantics in ACL2
`rt/prelude.lisp`:

```lisp
(defmacro %rule (name x) (declare (ignore name)) x)
```

ACL2 expands macros when it translates an event, and stores, proves and
compiles the translated term, so a tagged definition has the same body as
before. `%RULE` is defined in `prelude.lisp` (read by every version), and
`rt-defined-names` collects `defmacro` names from rt/, so W1T, W2T and W3T
import it like the other rt names (`package.lsp` of each version gains one
symbol). Expected effects: generated text larger (one string per rule
result), no change in modes, guards or results. Item 4 checks exactly
that.

### For W8 (the recorder), noted here
A tag fires when its rule's conclusion is built, after its premises. A
premise can succeed (and record) inside a rule whose later premise then
fails, so the recorder sees stale names from failed attempts. The chain of
one `step` is recovered from the end: the last `Step*` name recorded is the
outermost rule; the `Step*` name recorded last before it is the rule of its
`Step` premise, and so on (in a `Step` rule the `Step` premise is the last
`Step*` call before the conclusion). W8 tests this against hand-written
chains.

## Implementation (items 2 and 3)
- `rt/prelude.lisp`: `(defmacro %rule (name result) (declare (ignore name)) result)`.
- `il2acl2/compile.lisp`: `crule` returns
  `(list (%RULE "Rel/id" out))`; `cprods` passes each production's
  position (`:prod-total` from the two callers `cgram`, `cinline-gram`;
  `:prod-k` to `cprod`), and `cprod` returns `(list (%RULE "Gram/#k" r) rest)`.
- `make gen` for 1.0, 2.0, 3.0. Tags: 1.0 457, 2.0 927, 3.0 1,434
  (1,147 distinct, of which 498 `Binstr/#k`). `gen/wasm-1.0`: 5 files
  change (4,033 insertions, 2,623 deletions: the tags and re-indentation by
  the pretty-printer), `package.lsp` imports `WRT::%RULE`.
- Tried first in a git worktree (`make gen SPEC=3.0`, 46 s) so that the
  baseline spec runs, which certify against the working tree, stayed on the
  parent commit; the main tree's regenerated `gen/wasm-3.0` is identical to
  the worktree's.

## Gates (item 4)
| gate | before (d716fa8, 050fa11 run) | after (tags) |
|---|---|---|
| `make -C translate check` | exit 0, 5 s (nothing to recertify) | exit 0, 71 s (1.0 books recertified) |
| `check-2.0` | exit 0, 141 s | exit 0, 140 s |
| `check-3.0` | exit 0, 284 s | exit 0, 279 s (wasm3 M9: 4 min 38 s) |

`check-gen` (determinism, part of `check`) passes. `t0-modes` and
`t0-modes-3.0` certify against the unchanged manifests
(`gen/wasm-1.0/modes.lsp`, `tests/sem-3.0/modes-3.0.lsp`: not modified).
3.0 test lines unchanged: T3 numerics 8,724/8,724, SIMD 1,008/1,008 (full
profile 480/480), builtins 26/26, T5 46/46, T6 24/24.

### Spec runs, per command
Baseline at the parent commit d716fa8 (`make spec-data`, `make spec`, for
1.0 and 3.0), kept outside the tree: `/Users/Apple/dev/wasm-acl2-w7-baseline/`
(`results/`, `results-3.0/`, `COMMIT`, logs, `run.sh`). After the change,
same targets: `/Users/Apple/dev/wasm-acl2-w7-after/` (3.0 669 s, 1.0
3,603 s). `data/w7/compare-spec.sh` compares the `T7-CMD` lines script by
script (`data/w7/compare-3.0.out`, `compare-1.0.out`):

| spec | scripts with identical `T7-CMD` sequence | differing | `T7-CMD` lines before / after |
|---|---|---|---|
| 3.0 | 258 of 258 | 0 | 65,009 / 65,009 |
| 1.0 | 67 of 67 | 0 | 11,964 / 11,964 |

Totals (for the record, not compared): 3.0 63,326/63,883 commands pass,
256 done, 2 crashed (`T7-EXIT 137`: killed 30 s after the TERM of the
timeout); 1.0 10,891/11,611, 60 done, 2 timeout, 5 crashed. The same in
both runs.

Scripts not ending with `T7-EXIT 0`, the same in both runs:
- 3.0: `bulk-memory--memory_copy`, `call_ref`, `memory64--memory_copy64`
  (124: timeout), `call`, `call_indirect` (137: KILL after the timeout).
- 1.0: `call`, `call_indirect` (124), `data`, `elem` (1: SBCL heap
  exhausted, 32 GB, in `W1T::$INITDATA`, same backtrace before and after).

Each of them rerun once with a doubled TIMEOUT (3.0: 1,200 s, 1.0:
7,200 s), before (a worktree at d716fa8 with `gen/wasm-3.0` regenerated
there, untagged) and after (this tree), outside the results directories
(`<baseline|after>/rerun-3.0/`, `rerun-1.0/`; `data/w7/rerun.sh`,
`rerun-all.sh`). Compared by `data/w7/compare-rerun.sh`
(`compare-rerun-3.0.out`, `compare-rerun-1.0.out`): two complete runs
must be identical; when the timeout cut one or both, the shorter sequence
must be a prefix of the longer one (the runs stop at different commands
under different load).

| spec | script | before (exit, `T7-CMD` lines) | after | verdict |
|---|---|---|---|---|
| 3.0 | `call_ref` | 0, 35 | 0, 35 | identical (completes at 1,200 s) |
| 3.0 | `call_indirect` | 137, 76 | 137, 76 | identical |
| 3.0 | `call` | 124, 33 | 137, 35 | same on the first 33 |
| 3.0 | `bulk-memory--memory_copy` | 124, 4,218 | 124, 4,449 | same on the first 4,218 |
| 3.0 | `memory64--memory_copy64` | 124, 4,218 | 124, 4,449 | same on the first 4,218 |
| 1.0 | `call` | 124, 31 | 124, 31 | identical |
| 1.0 | `call_indirect` | 124, 89 | 124, 89 | identical |
| 1.0 | `data` | 1, 34 | 1, 34 | identical (heap exhausted again, same place) |
| 1.0 | `elem` | 1, 27 | 1, 27 | identical (heap exhausted again, same place) |

The 1.0 `call`/`call_indirect` reruns took 21,722 s of wall clock for a
7,200 s limit: the machine slept during them (power log: wake 15:04), so
those two are cut at an unknown share of the limit. They are still the same
before and after. Against the first runs (`data/w7` reruns vs `results*/`,
both sides): every rerun sequence and the first run's agree on their common
prefix, except 3.0 `call_ref`. There, in the first run (8 sessions at a
time), the 25th command printed `T7-TRY` and no `T7-CMD`: it exhausted a
Lisp resource and aborted alone (t7-lib-3.0.lisp's per-command form; a
command of kind CRASH for summarize-3.0.sh, one of its 24, not a crashed
script), on both sides. In the reruns (less
load) it passes on both sides, and the script completes: 35 lines against 34.

**Item 4 result**: green. All three gates, unchanged manifests, `check-gen`,
and identical per-command spec results for every script (258 + 67), with
the timed-out and crashed ones identical on their common prefix at the
doubled timeout.

## Coverage (item 5)
`data/w7/coverage.mjs` (IL reader + tags in `gen/wasm-3.0`): Step 36/36,
Step_pure 79/79, Step_read 103/103: **218/218**, none missing
(`data/w7/coverage.out`).

## Open questions
- None for the design.
