# WASM 3.0 Translation

> **Goal**: a machine-checked WASM 3.0 semantics in ACL2, generated from the
> SpecTec source by the translator in `translate/`, as WASM 1.0 was
> ([wasm1 plan](../wasm1-translation/plan.md)): decode → instantiate →
> invoke → run, then validation, then logic mode and proofs.
>
> **Status: DRAFT** (written 2026-11-14 at the end of
> [wasm3-translation-prep](../wasm3-translation-prep/plan.md) P7). Two things
> are missing before it is final: the user's decisions D1-D6 (§1 lists
> them as *assumed*, with the prep work already built on D2, D3 and D5),
> and the mode-table design, which the prep plan assigns to a Fable session
> ([suggested model choice](../wasm3-translation-prep/suggested-model-choice.md)).
> Every number below comes from a probe or test run and cites the prep note
> that holds it.
>
> **Source of truth**: `specification/wasm-3.0/*.spectec` at the pinned rev
> `WebAssembly/spec@943c5df` (flake input), `0.*`-`5.*` (25 of 37 files).

---

## Current state

- **Last updated**: 2026-11-14
- **Milestones**: none started; this plan is a draft (see the status note)
- **Next action**: user confirms or changes D1-D6 (§1); a Fable session
  designs the mode table (M5 depends on it)
- **Start from**: `make -C translate probe SPEC=3.0 EXCLUDE='X.* 6.* 7.*'`
  and `make -C translate check-2.0` (the 2.0 gate, green)

---

## 1. Decisions

| # | Decision | State | Effect on this plan |
|---|---|---|---|
| D1 | 2.0 as a stepping stone | **assumed yes**, and done: 2.0 certifies with 1 stub, 8,724 scalar + 528 SIMD vectors agree with V8 ([P4-wasm2-result](../wasm3-translation-prep/notes/P4-wasm2-result.md)) | 2.0 stays a regression target (`make check-2.0`) |
| D2 | One tree, per-version `il/`, `config/`, `gen/`, package; shared `rt/` | **assumed**, implemented: `SPEC=`, `W<major>T`, `rt/` in package `WRT` ([P2-layout](../wasm3-translation-prep/notes/P2-layout.md)) | none, if confirmed |
| D3 | 3.0 scope: `0.*`-`5.*`; `X.*` out; `6.*` text and `7.*` soundness deferred | **assumed**, implemented in the flake (`wasm3-il`) | §5 lists deferred milestones |
| D4 | Nondeterminism: deterministic profile, choices fixed to V8 | **open** (the 11 choice parameters are classified, [P3-builtin-inventory](../wasm3-translation-prep/notes/P3-builtin-inventory.md)) | M1 implements the choices |
| D5 | Hints via a SpecTec printer patch | **assumed**, implemented (`nix/spectec-ast-print-hints.patch`, [P3-hints](../wasm3-translation-prep/notes/P3-hints.md)) | offering it upstream is open |
| D6 | Execution first, typing second | **assumed** | milestone order of §5 |

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
| Relations emitted without some rules | 2, with 2 rules dropped (`Heaptype_sub/trans`, `Step_read/array.new_data-num`) | (whole-relation stubs) |
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
| GC | `Heaptype_sub/trans`: existential intermediate (dropped under `:check`) | triage | M5 |
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
- **Modes**: the 1.0 inference (three attempts per `rec` group), plus
  declared modes (`:modes`, counted) and `:fun2` (two outputs, last two
  components). The 3.0 config declares 21 relations: the type group
  `:check`, instruction typing `:multi`, and `Eval_expr` `:fun2`. The
  remaining design (M5) is inference per relation, outputs in any
  position, and decided existentials.
- **Granularity** (P1): per-rule stubs. A relation is emitted without the
  rules that do not compile, and they are listed in the header.
- **Patterns** (P4): retry of sequence elements (G9); counted iterations
  without domains or with output domains (G3, G4); elided projections.
- **Typed recognizers** (S8): unchanged; type arguments are still dropped.
- **Nondeterminism**: D4, open.

## 5. Milestones (D6 order)

Each ends with 1.0 `make check` and 2.0 `make check-2.0` green.

### M0: 3.0 as a target
- [ ] Check in `il/wasm-3.0.il.sexp` and its decls; `check-il SPEC=3.0`;
      promote `config/wasm-3.0.lsp` from provisional (its entries are all
      validated today)
- [ ] `make check-3.0` like `check-2.0`

**Exit**: `make gen SPEC=3.0` and a scratch-free certification of
`gen/wasm-3.0` in `:program` mode (today: 97 s in the experiment of
[P5-conformance](../wasm3-translation-prep/notes/P5-conformance.md)).

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
- [ ] Mode table design (Fable): inference per relation, any output
      positions (generalizes `:fun2`), existentials (G5, G8)
- [ ] Triage `Heaptype_sub/trans` (admissible? then drop with the argument written)

**Exit**: the 19-relation type group has no dropped rule, or each dropped
rule has a written completeness argument.

### M6: Instruction typing
- [ ] G5 rules; local-initialization tracking; subsumption (`Instrtype_sub`)

**Exit**: 110 of 110 `Instr_ok` rules; spec-test-3 `assert_invalid` N/M.

### M7: `Module_ok`
- [ ] Generic modes for the staged contexts, or a counted override as in 1.0

**Exit**: no stub in the D3 scope.

### M8: Conformance
- [ ] spec-test-3 at scale: 228 convertible scripts (P5); GC and exception
      scripts need the reference interpreter's converter (wabt converts 1 of 17
      GC scripts)

**Exit**: N/M for spec-test-3 recorded; estimate 1.5-2 h wall with 8
sessions at today's speed (P6).

### M9: Logic mode and proofs
- [ ] `%TRY-LOGIC` time limits: one 3.0 guard proof ran >15 min (P5)
- [ ] Mode manifest for 3.0 (`modes.lsp`, as 1.0)

**Exit**: a recorded logic / guards / program count, compared by a test book.

### Deferred
- Text format (`6.*`, 69 grammar stubs: `text` terminals, G6).
- Soundness judgements (`7.*`: `Context_ok`, `Frame_ok`, `Moduleinst_ok` stubs;
  `ImmutReachable` G8).

## 6. Config budget

Today `config/wasm-3.0.lsp` has 7 entries: `:def utf8` (with `:inverse`),
`:split Step ctxt-instrs`, `:decreasing`, `:memoize`, `:sized`,
`:builtins` (11 choice + 1 host + `$s33_to_u32`), `:modes` (21 relations).
1.0 has 7, 2.0 has 9 (two `:il-patch` for a 2.0 source bug). Expected
additions for 3.0: `:def utf8single` (S5), `:rel-override Module_ok` unless
M7 avoids it, about 9 entries in total. Each `:modes` pair is meant to
disappear with the mode table.

## 7. Risks and go/no-go points

| Risk | Evidence | Go/no-go |
|---|---|---|
| Typing complete only with hand-written parts | `trans` single witness vs dropped; G5/G8 existentials ([P1-typing-root-causes](../wasm3-translation-prep/notes/P1-typing-root-causes.md)) | after M5: if the type group needs more than its existentials hand-decided, accept "sound but incomplete" with listed rules, or Strategy B (AL) for typing |
| Runtime too slow for spec-test-3 | 10.4 ms per page per step (P6) | M3's store-free termination check; without it, run with a time budget and a skip list |
| Certification time in logic mode | one guard proof >15 min (P5) | M9: per-event wall-clock limits, or `:program` for the decoder |
| Conformance data for GC/exceptions | wabt converts 1/17 GC, 2/5 exception scripts (P5) | M8: build the reference interpreter's converter |
| `Step` split completeness (wasm1 T8) inherited, plus `ctxt-handler` | wasm1 W13 | carried; Strategy B (AL) remains the fallback for `Step` |

## 8. Notes consumed

Every note of the prep's index, and where it went: see
[the prep notes index](../wasm3-translation-prep/notes/README.md) ("Incorporated" column).
