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
- **Milestones**: M5 items 1 and 2 (mode table design and core; `trans`
  triage) ✅; M6 items 1 and 2 (design session; decision) ✅
- **Decided by the user (2026-11-14)**: instruction typing by option C
  ([M6-instruction-typing-strategy](notes/M6-instruction-typing-strategy.md)):
  a hand-written sequencer proposes each instruction's type and the
  generated rules check every step. Generated 3.0 instruction typing has
  no subsumption and cannot get it mechanically
- **3.0 probe now**: 2 stubs, **3** dropped rules (`Instrs_ok/sub` is new
  and honest), 0 declared modes
- **Next action**: M0, then M0b and M1 (see "Order and dependencies")
- **Readiness review (2026-11-14)**: added [step.md](step.md), M0b (GC and
  exception test data early), behavioural exits for M5 and M6, design
  sessions before M6 and M7, `assert_invalid` moved to M7, and the
  dependency section
- **Decided by the user (2026-11-14)**: the `:witness` config kind and
  entries stay; `trans` is translated with an enumeration variant, after
  M0 and M1 (its three parts are in the note)
- **Notes**: [notes/](notes/README.md)
- **Start from**: `make -C translate probe SPEC=3.0 EXCLUDE='X.* 6.* 7.*'`
  and `make -C translate check-2.0` (the 2.0 gate, green)

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
| Stubs | **2**: `Module_ok`, `$utf8single` | 35 |
| Relations emitted without some rules | 3, with 3 rules dropped (`Heaptype_sub/trans`, `Step_read/array.new_data-num`, and since the M6 session `Instrs_ok/sub`) | (whole-relation stubs) |
| Reduction rules (`Step`, `Step_read`, `Step_pure`) failing | **1 of 218** | about 10 |
| Clause-less defs | 89 = 77 numeric (13 not in `rt/`) + 11 choice + 1 host | |
| Defs with function parameters | 16, replaced by 53 specializations | 16 compiled wrongly |
| Decode experiment (spec-test-3) | 4,562 of 4,639 well-formed modules decode (98.3%), 604 of 643 malformed rejected | not measurable |

Full 3.0 (all 37 files): 76 stubs, 69 of them text grammars (`6.*`).

## 3. Work list (the gaps left), by proposal

From the P1 gap list as updated through P4
([P1-gap-list](../wasm3-translation-prep/notes/P1-gap-list.md),
[P4-generic-gaps](../wasm3-translation-prep/notes/P4-generic-gaps.md)):

| Proposal | Item | Gap | Milestone |
|---|---|---|---|
| core | `Module_ok` stub (tags, recursive types, staged contexts) | S4 | M7 |
| core | `$utf8single` stub (result defined arithmetically) | S5 | M1 |
| core | malformed UTF-8 in names accepted (39 decode cases; also in 1.0, 39 spec-test-1 failures) | `$utf8` inverse too lenient | M2 |
| GC | `Heaptype_sub/trans`: existential intermediate, dropped. **Not admissible**: `I31 <: ANY`, `deftype <: EQ` have no other derivation ([M5-mode-table](notes/M5-mode-table.md)) | enumeration variant or override | M5 |
| GC | `Step_read/array.new_data-num`: `c*` under `$concatn_($zbytes_(zt, c)^n)` | nested inverse (S1) | M3 |
| GC / bulk memory | builtins `$zbytes_ $cbytes_ $inv_zbytes_ $inv_cbytes_ $inv_concatn_` | S7 | M1 |
| relaxed SIMD | builtins `$irelaxed_q15mulr_ $irelaxed_laneselect_ $frelaxed_min_ $frelaxed_max_ $frelaxed_madd_ $frelaxed_nmadd_ $relaxed_trunc__`; 11 choice parameters (`$ND`, `$R_*`) | S6, D4 | M1 |
| numerics | builtin `$ceilz` | S7 | M1 |
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
- [ ] Check in `il/wasm-3.0.il.sexp` and its decls; `check-il SPEC=3.0`;
      promote `config/wasm-3.0.lsp` from provisional (its entries are all
      validated today)
- [ ] `make check-3.0` like `check-2.0`

**Exit**: `make gen SPEC=3.0` and a scratch-free certification of
`gen/wasm-3.0` in `:program` mode (today: 97 s in the experiment of
[P5-conformance](../wasm3-translation-prep/notes/P5-conformance.md)).

### M0b: Test data for GC and exceptions
- [ ] Build the reference interpreter's script converter in the flake (the
      pinned spec checkout has the interpreter) and convert the spec-test-3
      scripts that `wast2json` cannot: 31 of 259, among them 16 of 17
      GC scripts and 3 of 5 exception scripts ([P5-conformance](../wasm3-translation-prep/notes/P5-conformance.md))
- [ ] Same output format as `wasm3-spec-tests`, so the driver reads both

**Exit**: converted scripts recorded as N of 259 (228 today); the GC
scripts are available to M5, M6 and M7 as test data.

### M1: Numerics and builtins
- [ ] The 13 builtins of §3 in `rt/`; the 11 choice parameters per D4;
      `$hostcall` as a driver hook
- [ ] `$utf8single`: override like 1.0 `$utf8`
- [ ] Oracle vectors: extend `gen-numeric-vectors.mjs` / `gen-simd-vectors.mjs`;
      the oracle source of every clause-less def is in the inventory table of
      [P3-builtin-inventory](../wasm3-translation-prep/notes/P3-builtin-inventory.md)
      (relaxed SIMD via V8)

**Exit**: 0 builtins missing in `rt/`; 3.0 numeric and SIMD vectors agree with V8.

### M2: Binary decode
- [ ] Decode run on spec-test-3 in-tree (today 98.3% / 93.9% by
      experiment); fix the `table_copy` misses (36) and stricter UTF-8

**Exit**: every well-formed spec-test-3 module decodes; every binary
malformed one is rejected, or the misses are listed with causes.

### M3: Execution
- [ ] `Step_read/array.new_data-num` (nested inverse)
- [ ] Runtime: generated termination checks that ignore the store
      ([P6-runtime-baseline](../wasm3-translation-prep/notes/P6-runtime-baseline.md):
      about 19 traversals of the configuration per step, 10.4 ms per 64 KiB
      page per step today)
- [ ] Driver limits for huge locals and memory growth (the 5 spec-test-1 crashes)

**Exit**: 218 of 218 reduction rules translated; a 1-page memory step
within a small factor of the no-memory step (0.03 ms).

### M4: Instantiation and invocation
- [ ] `$instantiate` without `Module_ok` as a test-only path (D6)
- [ ] 3.0 driver values: `v128` lanes, references, exceptions (the data is
      already converted, [P5-conformance](../wasm3-translation-prep/notes/P5-conformance.md))

**Exit**: spec-test-3 `assert_return`/`assert_trap` for the non-GC scripts
recorded as N/M.

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
- [ ] Translate `Heaptype_sub/trans` with an enumeration variant (user
      decision, 2026-11-14): rules with several results, a fuelled transitive
      `HEAPTYPE_SUB/UP` that keeps the group's size-check measure, and the
      argument for the rules that cannot be enumerated. After M0 and M1, so
      that it can be run
- [ ] Behavioural cases, in a test book that calls the generated
      relations directly (`tests/sem-3.0/`, as 1.0 `t6-typing`): subtyping
      and type-validity cases with the expected answer taken from the spec
      rules or the reference interpreter. At least: `I31 <: ANY`,
      `STRUCT <: ANY`, `deftype <: EQ`, `NONE <: I31`, `REC i` against a
      declared supertype and its supertype, a `_IDX` on each side, a mutable
      field (invariant) and an immutable one, a function type (contravariant
      parameters), and one negative case per abstract hierarchy. Write the
      book before `trans`, so that it records the failures first
- [ ] Hand-over items 1, 3, 4 of the note (demand inside a `rec` group,
      `c(a, b)` halves as positions, the list of `:fun` relations called with
      a bound output). Not needed for the exit

**Exit**: the 19-relation type group has no dropped rule, or each dropped
rule has a written completeness argument; and the behavioural cases pass,
recorded as N of M.

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
- [ ] Behavioural cases in `tests/sem-3.0/`, calling `INSTRS_OK` directly
      on instruction sequences with a given context and type: one accepted
      and one rejected case for each of the six rules above, subsumption at
      a block end and at a call, an uninitialized non-defaultable local,
      and dead code after `unreachable`, `br` and `throw`. Expected answers
      from V8 (`WebAssembly.validate` on a module that wraps the sequence)
- [ ] Certify instruction typing (all 110 `Instr_ok` rules translate since
      the prep, G5 included) and make the cases pass under the chosen
      strategy. Start from the 23 cases of the note's data directory

**Exit**: the strategy decision recorded; 110 of 110 `Instr_ok` rules (or
the validator, under Strategy B); behavioural cases N of M.

### M7: `Module_ok`
- [ ] **Design session first** (a decision for the user): how to
      translate `Module_ok`. Its context is built in stages from the
      outputs of its own premises (types, then imports, then functions and
      globals), now with tags and recursive types. Options: staged modes
      in the translator (a context that grows premise by premise), or a
      counted `:rel-override` as in 1.0 (about 80 lines there; estimate
      the 3.0 size before choosing). Variants on demand do not help
      ([M5-mode-table](notes/M5-mode-table.md), hand-over item 6)
- [ ] Implement the choice; `$instantiate` with validation switched on
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

Today `config/wasm-3.0.lsp` has 7 entries: `:def utf8` (with `:inverse`),
`:split Step ctxt-instrs`, `:decreasing`, `:memoize`, `:sized`,
`:builtins` (11 choice + 1 host + `$s33_to_u32`), `:witness` (4
relations). The `:modes` entry (22 pairs at the end of the prep) is gone
since the mode table. 1.0 has 8 (the `:witness` entry is new), 2.0 has 9
(two `:il-patch` for a 2.0 source bug; `:witness` replaced `:modes`).
Expected additions for 3.0: `:def utf8single` (S5), `:rel-override
Module_ok` unless M7 avoids it, possibly `:rel-override Heaptype_sub`
(M5), about 9 or 10 entries in total.

## 7. Risks and go/no-go points

| Risk | Evidence | Go/no-go |
|---|---|---|
| Typing complete only with hand-written parts | `trans` is not admissible and is dropped today, so GC subtyping through abstract heap types is rejected; 8 rules rely on one witness ([M5-mode-table](notes/M5-mode-table.md)) | after M5: `trans` by enumeration or override. After M6: if one witness is not enough under subsumption, Strategy B (AL) for instruction typing |
| Runtime too slow for spec-test-3 | 10.4 ms per page per step (P6) | M3's store-free termination check; without it, run with a time budget and a skip list |
| Certification time in logic mode | one guard proof >15 min (P5) | M9: per-event wall-clock limits, or `:program` for the decoder |
| Conformance data for GC/exceptions | wabt converts 1/17 GC, 2/5 exception scripts (P5) | M0b: build the reference interpreter's converter, before the typing milestones need the data |
| `Step` split completeness (wasm1 T8) inherited, plus `ctxt-handler` | wasm1 W13 | carried; Strategy B (AL) remains the fallback for `Step` |

## 8. Notes consumed

Every note of the prep's index, and where it went: see
[the prep notes index](../wasm3-translation-prep/notes/README.md) ("Incorporated" column).
Notes of this plan: [notes/README.md](notes/README.md).
