# WASM 3.0 Translation

> **Goal**: a machine-checked WASM 3.0 semantics in ACL2, generated from the
> SpecTec source by the translator in `translate/`, as WASM 1.0 was
> ([wasm1 plan](../wasm1-translation/plan.md)): decode → instantiate →
> invoke → run, then validation, then logic mode and proofs.
>
> **Status: ready to start** (written 2026-11-14 at the end of
> [wasm3-translation-prep](../wasm3-translation-prep/plan.md) P7; revised
> the same day after the mode-table design and a readiness review with the
> user). The user decided D1-D6 (§1) and the M5 choices.
> Every number below comes from a probe or test run and cites the note
> that holds it. Per-session procedure: [step.md](step.md).
>
> **Source of truth**: `specification/wasm-3.0/*.spectec` at the pinned rev
> `WebAssembly/spec@943c5df` (flake input), `0.*`-`5.*` (25 of 37 files).

---

## Current state

- **Last updated**: 2026-11-14
- **Milestones**: M0 ✅ (3.0 is a target: IL checked in, `make check-3.0`
  certifies `gen/wasm-3.0` in-tree in :program mode, 1 min 32 s,
  [M0-target](notes/M0-target.md)); M0b ✅ (259 of 259 spec-test-3 scripts
  converted, 31 through the reference interpreter, among them 16 of 17 GC,
  [M0b-test-data](notes/M0b-test-data.md)); M1 ✅ (every builtin defined, in
  `rt/builtins-3.0.lisp`; 1 stub left, `Module_ok`; 8,724/8,724 numeric and
  1,008/1,008 SIMD vectors incl. 480 relaxed, [M1-builtins](notes/M1-builtins.md)); M2 ✅ (spec-test-3 decodes in-tree: every
  well-formed module but 4 that wabt writes malformed, every malformed one
  rejected, [M2-decode](notes/M2-decode.md)); M3 ✅ (218 of 218 reduction rules; a step
  costs 0.011 ms with or without memory, was 5.39 ms at 1 page;
  [M3-execution](notes/M3-execution.md)); M4 ✅ (`make spec SPEC=3.0`: spec-test-3
  `assert_return` + `assert_trap` outside gc/ 56,460 of 56,986, all commands
  60,447 of 61,193, 10 min 37 s, [M4-conformance](notes/M4-conformance.md)); M5 ✅ (exit met: `Heaptype_sub/trans` through
  an enumeration variant, the type group complete, 46 of 46 subtyping cases,
  [M5-trans](notes/M5-trans.md)); M5 items 1 and 2 (mode table design
  and core; `trans` triage) ✅; M6 items 1 and 2 (design session;
  decision) ✅
- **New config entries in M0 (for the user)**: `:program` (every
  generated 3.0 event in :program mode; reason: one guard proof ran
  more than 15 min, the step limits do not bound wall time; M9 removes
  it), and `:recursive nil` in the 3.0 `:memoize` entry (memoize used to
  recompile the huge `Instr_ok` body at every include, 22 s × 12 books;
  memoization still works: 0.01 s against more than 300 s unmemoized).
  Two translator changes: a builtin that `rt/` lacks becomes a listed stub
  (27 stubs in `gen/wasm-3.0` until M1), and `%FUEL` goes only to
  functions that use it (an M5 bug that only certification showed). 1.0
  output is byte-identical
- **Decided by the user (2026-11-14)**: instruction typing by option C
  ([M6-instruction-typing-strategy](notes/M6-instruction-typing-strategy.md)):
  a hand-written sequencer proposes each instruction's type and the
  generated rules check every step. Generated 3.0 instruction typing has
  no subsumption and cannot get it mechanically
- **Found by the review (2026-11-14)**: in the 19-relation type group the
  generated termination check cuts valid derivations (delegation, context
  lookups): 9 of 22 type cases right, e.g. `valtype_sub (ref i31) <: (ref
  null i31)` was rejected. Fixed with the user's go-ahead: the group
  terminates by fuel (config `:fuel`); 20 of 22 right, the 2 left need
  `trans` ([review-checker-blind-spots](notes/review-checker-blind-spots.md))
- **Waiting for the user**: the `Module_ok` strategy
  ([M7-module-ok-strategy](notes/M7-module-ok-strategy.md)). Recommended:
  hand-written code proposes the contexts `C'` and `C`, the generated rule
  checks them (measured: with both given, the rule compiles with 0 errors)
- **3.0 probe now** (after M1): **1** stub (`Module_ok`), 0 builtins missing in `rt/`, **3** dropped rules (`Instrs_ok/sub` is new
  and honest), 0 declared modes
- **Next action**: M6 item 3 (the sequencer, option C), as planned in the M6
  strategy note's update of 2026-11-15: step 1 done (kept whole-type variant
  `INSTR_OK/OUT2`, new config kind `:keep-variant`; 18 rules for the table);
  next `:rel-override` of `Instrs_ok` inside its rec group, the
  callers passing `t_2*`, then the sequencer. **For the user before step 3**:
  (a) sub-component output positions (as recommended) or (b) five `:il-patch`
  entries with `x* = []`, equivalent by `Instrs_ok/sub` and cheaper. The V8
  cases record 16 of 24 before it. M7 waits for
  the user's decision above. M8 needs M7; the execution side is ready for it.
  Optional: M5 hand-over items 1, 3, 4 (not needed for the exit)
- **Changed in M5 (for the user)**: translator feature "enumeration variants"
  (`R/ENUM<i>`, collecting searches, made on demand inside a rec group), used
  for `Heaptype_sub/trans` as you decided; no new config entry. Five rule
  kinds are left out of the enumeration, each with a completeness argument in
  [M5-trans](notes/M5-trans.md) (two of them argued from the rules only)
- **For the user (M4)**: new config KIND `:il-variant` and the entry
  `$instantiate_unchecked` (TEST-ONLY: `$instantiate` without `Module_ok` and
  `Externaddr_ok`, decision D6; remove with M7); new `:decreasing` pair
  `("Ref_ok" . 1)` (the size check cut `Ref_ok/extern`, so no externref had a
  type). Translator: a partial inverse (result `X?`, e.g. `$inv_isize`) is now
  unwrapped; it broke every float vector comparison and the lane, splat and
  extend loads. 1.0 output byte-identical. The relaxed-SIMD failures (33) are
  wabt's `either` data again (see the M0b recommendation)
- **Changed in M3 (for the user)**: the 3.0 `:decreasing` entry has a new
  pair `("Step" 0 2)` (a path: the instructions of the configuration),
  reason in the config. Translator: an inverse equation may solve for a
  middle argument, and `:multi` no longer propagates into the step
  relation of a closure (`Step` stays `:fun`; `Step_read` is now `:multi`,
  its output variant drops no rule). The decode run's M2 totals missed the
  end of `binary` (corrected in M2-decode)
- **For the user (M2)**: new config entry `:il-patch "Belem"` (reason in the
  config): SpecTec elaborates `ELEM rt (REF.FUNC y)*` (flags 0-3) as one
  expression holding every `ref.func`; the patch gives one expression per
  function index, as the prose does. 2.0's IL has the same shape and is
  not patched (2.0 is a regression target; your call). Also open: the 1.0
  parser rejects 54 spec-test-1 modules that the reference interpreter
  decodes (mostly import sections; outside the 3.0 milestones). The UTF-8
  fix is in the shared `rt/` and also fixes 1.0 (638/638 malformed
  rejected); the 3.0 wast2json flags no longer include compact imports
- **For the user (M1)**: new config entry `:def utf8single` (reason in the
  config). D4 read as: the semantics is the deterministic profile (`$ND`
  false, as in SpecTec's interpreter). `$R_*` record V8's choices on
  arm64 (`R_fmadd` 1, the rest 0) and change no result. V8 is not
  deterministic (it fuses `relaxed_madd`), so the relaxed vectors carry
  both the deterministic result and V8's, and the test checks both
- **Recommendation for the user (M0b, for M8)**: convert all 259 scripts
  through the reference interpreter. wabt's data already in use has
  wrong expectations in 9 scripts (`either` results written as `()` in 8,
  a misrounded f64 subnormal in `simd_lane`). The interpreter agrees on
  217 of 228 scripts and is right in 10 of the 11 others
- **Readiness review (2026-11-14)**: added [step.md](step.md), M0b (GC and
  exception test data early), behavioural exits for M5 and M6, design
  sessions before M6 and M7, `assert_invalid` moved to M7, and the
  dependency section
- **Decided by the user (2026-11-14)**: the `:witness` config kind and
  entries stay; `trans` is translated with an enumeration variant, after
  M0 and M1 (its three parts are in the note)
- **Notes**: [notes/](notes/README.md)
- **Start from**: `make -C translate probe SPEC=3.0 EXCLUDE='X.* 6.* 7.*'`,
  `make -C translate check-2.0` and `make -C translate check-3.0` (both
  gates green, 2026-11-14)

---

## 1. Decisions

| # | Decision | State | Effect on this plan |
|---|---|---|---|
| D1 | 2.0 as a stepping stone | **decided (2026-11-14): yes**, and done: 2.0 certifies with 1 stub, 8,724 scalar + 528 SIMD vectors agree with V8 ([P4-wasm2-result](../wasm3-translation-prep/notes/P4-wasm2-result.md)) | 2.0 stays a regression target (`make check-2.0`) |
| D2 | One tree, per-version `il/`, `config/`, `gen/`, package; shared `rt/` | **decided (2026-11-14)**, implemented: `SPEC=`, `W<major>T`, `rt/` in package `WRT` ([P2-layout](../wasm3-translation-prep/notes/P2-layout.md)) | none, if confirmed |
| D3 | 3.0 scope: `0.*`-`5.*`; `X.*` out; `6.*` text and `7.*` soundness deferred | **decided (2026-11-14)**, implemented in the flake (`wasm3-il`) | §5 lists deferred milestones |
| D4 | Nondeterminism: deterministic profile, choices fixed to V8 | **decided (2026-11-14): deterministic, V8** (the 11 choice parameters are classified, [P3-builtin-inventory](../wasm3-translation-prep/notes/P3-builtin-inventory.md)) | M1 implements the choices |
| D5 | Hints via a SpecTec printer patch | **decided (2026-11-14)**, implemented (`nix/spectec-ast-print-hints.patch`, [P3-hints](../wasm3-translation-prep/notes/P3-hints.md)) | offering it upstream is open |
| D6 | Execution first, typing second | **decided (2026-11-14)** | milestone order of §5 |

## 2. Where 3.0 stands (probe, D3 scope, 2026-11-14)

From `make probe SPEC=3.0 EXCLUDE='X.* 6.* 7.*'`
([data](../wasm3-translation-prep/notes/data/probe-P4-gate-2026-11-14/report-3.0-core.txt)):

| | Value | Prep baseline (P0) |
|---|---|---|
| Spec files / lines | 25 / 7,008 | |
| IL forms / hint forms | 795 / 640 | |
| Rules / relations | 509 / 85 | |
| Schema errors | 0 | 3 (full 3.0) |
| Phase-1 events | 1,240 | 993 |
| Stubs | **1**: `Module_ok` since M1 (2 before: `$utf8single` is now a config override, [M1-builtins](notes/M1-builtins.md)) | 35 |
| Relations emitted without some rules | 3, with 3 rules dropped (`Heaptype_sub/trans`, `Step_read/array.new_data-num`, and since the M6 session `Instrs_ok/sub`) ; since M3: **2** (`Step_read` complete); since M5: **1** (`Instrs_ok/sub`) | (whole-relation stubs) |
| Reduction rules (`Step`, `Step_read`, `Step_pure`) failing | **1 of 218**; since M3: **0** | about 10 |
| Clause-less defs | 89 = 77 numeric + 11 choice + 1 host; since M1 all defined in `rt/` (13 numeric were missing) | |
| Defs with function parameters | 16, replaced by 53 specializations | 16 compiled wrongly |
| Decode experiment (spec-test-3) | 4,562 of 4,639 well-formed modules decode (98.3%), 604 of 643 malformed rejected; in-tree since M2: 5,228 of 5,232 and 643 of 643 ([M2-decode](notes/M2-decode.md)) | not measurable |

Full 3.0 (all 37 files): 76 stubs, 69 of them text grammars (`6.*`).

## 3. Work list (the gaps left), by proposal

From the P1 gap list as updated through P4
([P1-gap-list](../wasm3-translation-prep/notes/P1-gap-list.md),
[P4-generic-gaps](../wasm3-translation-prep/notes/P4-generic-gaps.md)):

| Proposal | Item | Gap | Milestone |
|---|---|---|---|
| core | `Module_ok` stub (tags, recursive types, staged contexts) | S4 | M7 |
| core | `$utf8single` stub (result defined arithmetically) | S5 | M1 ✅ |
| core | malformed UTF-8 in names accepted (39 decode cases; also in 1.0, 39 spec-test-1 failures) | `$utf8` inverse too lenient | M2 ✅ |
| GC | `Heaptype_sub/trans`: existential intermediate, dropped. **Not admissible**: `I31 <: ANY`, `deftype <: EQ` have no other derivation ([M5-mode-table](notes/M5-mode-table.md)) | enumeration variant or override | M5 ✅ |
| GC | `Step_read/array.new_data-num`: `c*` under `$concatn_($zbytes_(zt, c)^n)` | nested inverse (S1) | M3 ✅ |
| GC / bulk memory | builtins `$zbytes_ $cbytes_ $inv_zbytes_ $inv_cbytes_ $inv_concatn_` | S7 | M1 ✅ |
| relaxed SIMD | builtins `$irelaxed_q15mulr_ $irelaxed_laneselect_ $frelaxed_min_ $frelaxed_max_ $frelaxed_madd_ $frelaxed_nmadd_ $relaxed_trunc__`; 11 choice parameters (`$ND`, `$R_*`) | S6, D4 | M1 ✅ |
| numerics | builtin `$ceilz` | S7 | M1 ✅ |
| exceptions, tail calls, memory64, multi-memory, bulk memory, extended const | no translation gap found; conformance data partial (wabt) | — | M8 |

## 4. Translation-scheme delta against wasm1 §2

- **Layout and packages** (P2): one translator; `SPEC=1.0|2.0|3.0`;
  `config/wasm-<v>.lsp`; output `gen/wasm-<v>/`, one book per spec file,
  chained in IL order; package `W<major>T` importing `*acl2-exports*` minus
  clashes plus the names of `rt/` (package `WRT`).
- **Hints** (P3): the IL carries `(hint ...)` forms. Inverse pairs come from
  `hint(inverse)`; builtins are classified from `hint(builtin)` plus one
  counted `:builtins` entry.
- **Function arguments** (G1): specialization as an IL pre-pass (`f.g`); no
  higher-order code is generated.
- **Modes** ([M5-mode-table](notes/M5-mode-table.md)): a mode is a set of
  output positions. Inference per group: all `:fun`; demote failing
  members to `:check` until stable; `:multi`; else the attempt with the
  fewest failing rules. Output variants `R/OUT<i>..` for any positions are
  made on demand for relations of earlier forms. A premise that takes a
  value from an output variant that drops rules is an error ("witness
  choice") unless a counted `:witness` entry accepts the relation. 3.0
  declares **0** modes (22 before); the witness sources are `Instr_ok`,
  `Instrs_ok`, `Ref_ok`, `Externaddr_ok`.
- **Granularity** (P1): per-rule stubs. A relation is emitted without the
  rules that do not compile, and they are listed in the header.
- **Patterns** (P4): retry of sequence elements (G9); counted iterations
  without domains or with output domains (G3, G4); elided projections.
- **Typed recognizers** (S8): unchanged; type arguments are still dropped.
- **Nondeterminism**: D4, decided: the deterministic profile with the
  choices fixed to V8; M1 implements them.

## 5. Milestones (D6 order)

Each ends with 1.0 `make check` and 2.0 `make check-2.0` green, and from
M0 on also `make check-3.0`.

### M0: 3.0 as a target
- [x] Check in `il/wasm-3.0.il.sexp` and its decls; `check-il SPEC=3.0`;
      promote `config/wasm-3.0.lsp` from provisional (its entries are all
      validated today). Done 2026-11-14 ([M0-target](notes/M0-target.md))
- [x] `make check-3.0` like `check-2.0`. Done 2026-11-14: regenerates and
      certifies `gen/wasm-3.0` in-tree in **1 min 32 s** (certification
      1 min 26 s). Needed: builtins missing in `rt/` emitted as stubs (27
      stubs: the probe's 2 + 13 numeric + 11 choice + `$hostcall`), config
      `:program`, `%FUEL` only where used (a translator bug from M5), and
      `:memoize ... :recursive nil` (without it 7 min 6 s)

**Exit**: `make gen SPEC=3.0` and a scratch-free certification of
`gen/wasm-3.0` in `:program` mode (today: 97 s in the experiment of
[P5-conformance](../wasm3-translation-prep/notes/P5-conformance.md)).
**Met 2026-11-14**: 1 min 26 s in-tree, no scratch tree ([M0-target](notes/M0-target.md)).

### M0b: Test data for GC and exceptions
- [x] Build the reference interpreter's script converter in the flake (the
      pinned spec checkout has the interpreter) and convert the spec-test-3
      scripts that `wast2json` cannot: 31 of 259, among them 16 of 17
      GC scripts and 3 of 5 exception scripts ([P5-conformance](../wasm3-translation-prep/notes/P5-conformance.md))
      Done 2026-11-14 ([M0b-test-data](notes/M0b-test-data.md)): `.#wasm-ref-interp`;
      `wasm -d S.wast -o S.bin.wast` for the 31, all 31 convert
- [x] Same output format as `wasm3-spec-tests`, so the driver reads both.
      Done: `gen-spec-tests.mjs` reads the `.bin.wast`; one `index.lsp`;
      the old 228 are byte-identical. Cross-check on the 228: 217 the same,
      10 of the 11 others are wabt errors (`either` results lost in 8
      scripts, a subnormal misrounded in `simd_lane`)

**Exit**: converted scripts recorded as N of 259 (228 today); the GC
scripts are available to M5, M6 and M7 as test data.
**Met 2026-11-14**: **259 of 259** (31 through the reference interpreter);
293 instantiated modules validate, 290 `assert_invalid` modules are rejected.

### M1: Numerics and builtins
- [x] The 13 builtins of §3 in `rt/`; the 11 choice parameters per D4;
      `$hostcall` as a driver hook. Done 2026-11-14 ([M1-builtins](notes/M1-builtins.md)):
      in `rt/builtins-3.0.lisp` (read for 3.0 only, so 1.0 and 2.0 do not
      change); `$ND` false, `R_fmadd` 1 and the other `$R_*` 0 (V8 on arm64);
      `$hostcall` an attachable hook (`defattach`)
- [x] `$utf8single`: override like 1.0 `$utf8`. Done: config `:def utf8single`
- [x] Oracle vectors: extend `gen-numeric-vectors.mjs` / `gen-simd-vectors.mjs`;
      the oracle source of every clause-less def is in the inventory table of
      [P3-builtin-inventory](../wasm3-translation-prep/notes/P3-builtin-inventory.md)
      (relaxed SIMD via V8)
      Done: `gen-simd-vectors.mjs 3.0` adds 480 relaxed vectors with two
      results, the deterministic profile (V8 running strict equivalents) and
      V8's relaxed instruction, which fuses `relaxed_madd` on arm64

**Exit**: 0 builtins missing in `rt/`; 3.0 numeric and SIMD vectors agree with V8.
**Met 2026-11-14**: 0 missing (1 stub left: `Module_ok`); 8,724/8,724 numeric,
1,008/1,008 SIMD (480 relaxed, deterministic profile); in the full profile
480/480 relaxed vectors give V8's own result; 26/26 builtin cases.

### M2: Binary decode
- [x] Decode run on spec-test-3 in-tree (today 98.3% / 93.9% by
      experiment); fix the `table_copy` misses (36) and stricter UTF-8.
      Done 2026-11-14 ([M2-decode](notes/M2-decode.md)): `make decode SPEC=3.0`
      (23 s). The `table_copy` misses and 34 more were wabt writing compact
      imports (`--enable-all`; flake fixed); UTF-8: `rt/` `$utf8` no longer
      encodes non-characters (1.0 gains: 638/638 malformed rejected); config
      `:il-patch "Belem"` (elem segments of flags 0-3 decoded to one expression)

**Exit**: every well-formed spec-test-3 module decodes; every binary
malformed one is rejected, or the misses are listed with causes.
**Met 2026-11-14**: 2,250/2,250 modules, 200/200 unlinkable, 54/54
uninstantiable and 2,724/2,728 invalid decode; 643/643 malformed are rejected.
The 4 left are binary-malformed as wabt wrote them (no data count section),
as the reference interpreter also says.

### M3: Execution
- [x] `Step_read/array.new_data-num` (nested inverse). Done 2026-11-14
      ([M3-execution](notes/M3-execution.md)): the inverse case solves for the one
      unbound argument (`$inv_concatn_(k, s)`); behaviour checked in M4 (GC
      `array_new_data`)
- [x] Runtime: generated termination checks that ignore the store
      ([P6-runtime-baseline](../wasm3-translation-prep/notes/P6-runtime-baseline.md):
      about 19 traversals of the configuration per step, 10.4 ms per 64 KiB
      page per step today)
      Done: `:decreasing` path `("Step" 0 2)`; 1 page: **5.39 → 0.011 ms/step**
      (no memory 0.012)
- [x] Driver limits for huge locals and memory growth (the 5 spec-test-1 crashes).
      Decoder done (each module its own form; "too many locals" reported as
      crashed, 2 in spec-test-3); the execution limits (`memory.grow`, segment
      bounds) move to M4, whose driver they belong to

**Exit**: 218 of 218 reduction rules translated; a 1-page memory step
within a small factor of the no-memory step (0.03 ms).
**Met 2026-11-14**: 218 of 218; 0.011 ms/step at 1 page, the same as with no memory.

### M4: Instantiation and invocation
- [x] `$instantiate` without `Module_ok` as a test-only path (D6). Done 2026-11-15
      ([M4-conformance](notes/M4-conformance.md)): new config kind `:il-variant`;
      `$instantiate_unchecked` (no `Module_ok`, no `Externaddr_ok`)
- [x] Execution limits in the 3.0 driver (from M3 item 3): a `memory.grow` or
      `table.grow` above a bound, and segment bounds at instantiation, reported
      as a resource limit (like `assert_exhaustion`), not run (P6: two spec-test-1
      crashes each). Done as containment: each command its own form, an aborted
      one is a failure of kind CRASH (24 in spec-test-3); 200,000 steps per action;
      `timeout -k`
- [x] 3.0 driver values: `v128` lanes, references, exceptions (the data is
      already converted, [P5-conformance](../wasm3-translation-prep/notes/P5-conformance.md)).
      Done: `tests/spec/t7-lib-3.0.lisp`, `make spec SPEC=3.0` (10 min 37 s)

**Exit**: spec-test-3 `assert_return`/`assert_trap` for the non-GC scripts
recorded as N/M.
**Met 2026-11-15**: **56,460 of 56,986** (99.1%); all commands 60,447 of 61,193.
The run found and fixed two translator-level bugs (partial inverses; `Ref_ok`
cut by the size check). What fails: 446 after an aborted `memory_copy` action,
43 step budget, 33 relaxed SIMD (wabt data), 4 after an aborted grow.

### M5: Type validation and subtyping (mode table)
- [x] Mode table design (Fable): inference per relation, any output
      positions (generalizes `:fun2`), existentials beyond the `:check`-mode
      searches the prep added (G5, G8: index and finite-type searches).
      Done 2026-11-14 ([M5-mode-table](notes/M5-mode-table.md)): 3.0 declared
      modes 22 → 0 with the same 2 stubs and 2 dropped rules; 2.0 declared
      modes 2 → 0; 1.0 definitions byte-identical; 9 single-witness rules
      listed for 3.0, 8 accepted by the `:witness` entry and `trans` rejected
- [x] Triage `Heaptype_sub/trans`: **not admissible** (same note), so it
      cannot stay dropped
- [x] **Termination of the type group by fuel** instead of the size
      check, chosen per group by a config entry (`:fuel`; 1.0 and 2.0
      unchanged). Done 2026-11-14: the 22 cases of
      `data/typing-M6-2026-11-14/cases-3.0-types.lsp` went from 9 right to
      **20**; the 2 left are `trans`. Open: the bound of 10,000 was not
      exercised by a search that runs to it
      ([review-checker-blind-spots](notes/review-checker-blind-spots.md))
- [x] Translate `Heaptype_sub/trans` with an enumeration variant (user
      decision, 2026-11-14): rules with several results, a fuelled transitive
      `HEAPTYPE_SUB/UP` that keeps the group's size-check measure, and the
      argument for the rules that cannot be enumerated. After M0 and M1, so
      that it can be run
      Done 2026-11-15 ([M5-trans](notes/M5-trans.md)): `HEAPTYPE_SUB/ENUM2` and
      `DEFTYPE_SUB/ENUM2` (collecting searches, made on demand in the group);
      `Heaptype_sub` 21/21; the left-out rules argued in the note
- [x] Behavioural cases, in a test book that calls the generated
      relations directly (`tests/sem-3.0/`, as 1.0 `t6-typing`): subtyping
      and type-validity cases with the expected answer taken from the spec
      rules or the reference interpreter. At least: `I31 <: ANY`,
      `STRUCT <: ANY`, `deftype <: EQ`, `NONE <: I31`, `REC i` against a
      declared supertype and its supertype, a `_IDX` on each side, a mutable
      field (invariant) and an immutable one, a function type (contravariant
      parameters), and one negative case per abstract hierarchy. Write the
      book before `trans`, so that it records the failures first
      Done 2026-11-15 ([M5-subtyping-cases](notes/M5-subtyping-cases.md)):
      `tests/sem-3.0/t5-subtyping-3.0.lisp`, in `make check-3.0`; **35 of 46**
      right, the 11 wrong ones all need `trans`. With `trans`: **46 of 46**
- [ ] Hand-over items 1, 3, 4 of the note (demand inside a `rec` group,
      `c(a, b)` halves as positions, the list of `:fun` relations called with
      a bound output). Not needed for the exit

**Exit**: the 19-relation type group has no dropped rule, or each dropped
rule has a written completeness argument; and the behavioural cases pass,
recorded as N of M.
**Met 2026-11-15**: no dropped rule in the group; 46 of 46 cases.

### M6: Instruction typing
- [x] **Design session** (go/no-go), held 2026-11-14
      ([M6-instruction-typing-strategy](notes/M6-instruction-typing-strategy.md)).
      Measured on 23 cases run on the generated code: 13 right before, 18
      after a mechanical fix made in the session (the output variant now
      takes the input stack of the three-part 3.0 arrow; 1.0 `gen/`
      byte-identical). The rest is subsumption (no mechanical reading:
      `Instrs_ok/sub` is now a visibly dropped rule), dead code and
      `trans`. **No-go** for check + output variant alone
- [x] **User decision (2026-11-14): option C**: a hand-written sequencer
      proposes each instruction's type, the generated `INSTR_OK` and
      `RESULTTYPE_SUB` check every step
- [ ] Translator support for it, namely `:rel-override` for a member of a
      `rec` group, sub-component output positions, and a kept whole-type
      variant of `Instr_ok`; then the sequencer and its table for the 10
      rules the output variant drops
- [x] Behavioural cases in `tests/sem-3.0/`, calling `INSTRS_OK` directly
      on instruction sequences with a given context and type: one accepted
      and one rejected case for each of the six rules above, subsumption at
      a block end and at a call, an uninitialized non-defaultable local,
      and dead code after `unreachable`, `br` and `throw`. Expected answers
      from V8 (`WebAssembly.validate` on a module that wraps the sequence)
      Done 2026-11-15 ([M6-typing-cases](notes/M6-typing-cases.md)): 24 bodies through
      `EXPR_OK`, `make check-3.0`; **16 of 24** agree with V8, the 8 wrong ones are
      valid bodies rejected (subsumption 3, dead code 3, `br` with a value, an
      initialized local); none accepted wrongly
- [ ] Certify instruction typing (all 110 `Instr_ok` rules translate since
      the prep, G5 included) and make the cases pass under the chosen
      strategy. Start from the 23 cases of the note's data directory

**Exit**: the strategy decision recorded; 110 of 110 `Instr_ok` rules (or
the validator, under Strategy B); behavioural cases N of M.

### M7: `Module_ok`
- [x] **Design session**, held 2026-11-14
      ([M7-module-ok-strategy](notes/M7-module-ok-strategy.md)): two
      cycles through the context `C` (function types; data and element
      types). Experiment: in the new mode `(:given "C" "C'")` the generated
      rule compiles with 0 errors (29 before)
- [ ] **User decision**: proposer and checker (recommended: about 60 to 80
      hand-written lines compute `C'` and `C`; the generated `MODULE_OK/W`
      checks them on every call), or a plain override as in 1.0 (about 110
      lines, tied to the rule by tests only)
- [ ] Implement the choice: a config kind for "entry function plus given
      variables", the proposer; `$instantiate` with validation switched on
- [ ] Module-level validation on spec-test-3, GC and exception scripts
      included (M0b): `assert_invalid` rejected, and every module that the
      scripts instantiate accepted

**Exit**: no stub in the D3 scope; `assert_invalid` N/M and valid modules
accepted N/M, each miss listed with its cause.

### M8: Conformance
- [ ] spec-test-3 at scale: every script M0b converts (228 with `wast2json`
      alone, P5)

**Exit**: N/M for spec-test-3 recorded; estimate 1.5-2 h wall with 8
sessions at today's speed (P6).

### M9: Logic mode and proofs
- [ ] `%TRY-LOGIC` time limits: one 3.0 guard proof ran >15 min (P5)
- [ ] Mode manifest for 3.0 (`modes.lsp`, as 1.0), including the
      `R/OUT..` variants made on demand

**Exit**: a recorded logic / guards / program count, compared by a test book.

### Order and dependencies

```
M0 ──┬─ M0b ─────────────────────────────┐
     ├─ M1 ─┬─ M2 ── M3 ── M4 ───────────┼─ M8 ── M9
     │      └─ M5 ── M6 ── M7 ───────────┘
```

- M0 first: nothing in 3.0 can be certified or run before it.
- M0b and M1 need only M0 and can run in parallel.
- Execution (M2, M3, M4) and typing (M5, M6, M7) are independent after
  M1. D6 puts execution first, but a typing design session (M6, M7) can
  be held at any time, since it produces a note and a decision.
- M5 `trans` and every behavioural test need M0 and M1 (generated 3.0
  code must load). The GC cases of M5 to M7 need M0b.
- M6 needs M5 (instruction typing calls subtyping, and under option C the
  sequencer needs `Heaptype_sub` complete, so `trans` first). M7 needs M6.
- M8 needs M4 and M7 and M0b. M9 last; the `trans` design keeps the type
  group's termination measure for it.

### Deferred
- Text format (`6.*`, 69 grammar stubs: `text` terminals, G6).
- Soundness judgements (`7.*`: `Context_ok`, `Frame_ok`, `Moduleinst_ok` stubs;
  `ImmutReachable` G8).

## 6. Config budget

Today `config/wasm-3.0.lsp` has 12 entries: `:def utf8` (with `:inverse`), since M1 `:def utf8single`, since M2 `:il-patch "Belem"`, since M4 `:il-variant "instantiate"` (test-only, removed with M7),
`:split Step ctxt-instrs`, `:decreasing`, `:memoize` (since M0 with
`:recursive nil`), `:sized`, `:builtins` (11 choice + 1 host +
`$s33_to_u32`), `:witness` (4 relations), since M5 `:fuel` (the type
group), and since M0 `:program` (certification mode, removed in M9), 12 in all. The `:decreasing` entry has gained `("Step" 0 2)` (M3) and `("Ref_ok" . 1)` (M4). The `:modes` entry (22 pairs at the end of the prep) is gone
since the mode table. 1.0 has 8 (the `:witness` entry is new), 2.0 has 9
(two `:il-patch` for a 2.0 source bug; `:witness` replaced `:modes`).
Expected additions for 3.0: `:rel-override Module_ok` unless M7 avoids it,
possibly `:rel-override Heaptype_sub` (M5), about 12 or 13 entries in total (M7 removes `:il-variant`, M9 `:program`)
(M9 removes `:program`).

## 7. Risks and go/no-go points

| Risk | Evidence | Go/no-go |
|---|---|---|
| The size-check termination discipline does not fit 3.0 types | 13 of 22 type cases wrong ([review-checker-blind-spots](notes/review-checker-blind-spots.md)) | M5: fuel for the type group; if a relation outside it shows the same shape, the probe cannot tell, only behavioural cases can |
| Typing complete only with hand-written parts | `trans` is not admissible and is dropped today, so GC subtyping through abstract heap types is rejected; 8 rules rely on one witness ([M5-mode-table](notes/M5-mode-table.md)) | after M5: `trans` by enumeration or override. After M6: if one witness is not enough under subsumption, Strategy B (AL) for instruction typing |
| Runtime too slow for spec-test-3 | 10.4 ms per page per step (P6); since M3 0.011 ms per step at 1 page (store not traversed); since M4 spec-test-3 runs in 10 min 37 s with 8 sessions | M3's store-free termination check; without it, run with a time budget and a skip list |
| Certification time in logic mode | one guard proof >15 min (P5) | M9: per-event wall-clock limits, or `:program` for the decoder |
| Conformance data for GC/exceptions | wabt converts 1/17 GC, 2/5 exception scripts (P5); resolved by M0b, 259/259 | wabt's data has wrong expectations in 9 scripts ([M0b-test-data](notes/M0b-test-data.md)): M8 should convert everything through the reference interpreter (recommended, the user decides) |
| `Step` split completeness (wasm1 T8) inherited, plus `ctxt-handler` | wasm1 W13 | carried; Strategy B (AL) remains the fallback for `Step` |

## 8. Notes consumed

Every note of the prep's index, and where it went: see
[the prep notes index](../wasm3-translation-prep/notes/README.md) ("Incorporated" column).
Notes of this plan: [notes/README.md](notes/README.md).
