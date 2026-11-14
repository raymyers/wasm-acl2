# WASM 3.0 Translation: Prep

> **Goal of this plan**: do the groundwork that lets us write
> `plan/wasm3-translation/plan.md` with measured numbers, known blockers, and
> decided scope, and lets that plan start from a pipeline that already
> handles a second spec version. This plan does **not** translate WASM 3.0.
>
> **Deliverable**: `plan/wasm3-translation/plan.md` (written in P7), plus the
> translator and plumbing changes in P0-P6 that it depends on.
>
> **Starting point**: [plan/wasm1-translation/plan.md](../wasm1-translation/plan.md).
> T0-T6 are done; T7 (spec-test-1 driver), T8 (split-strategy proof) and T9
> (float equivalence, false as stated) are partial.
>
> **Source of truth**: `specification/wasm-3.0/*.spectec` at the SpecTec rev
> already pinned in `flake.nix` (`WebAssembly/spec@943c5df`). The same
> checkout also holds `wasm-2.0` and `wasm-latest`.

---

## Current state

Update this block at the end of every session, in the same commit as the work.
A new session starts here.

- **Last updated**: 2026-11-14
- **Milestones**: P0 ✅, P1 ✅, P2 ✅, P3 ✅, P5 ✅, P6 ✅. P4: exit ✅ (2.0
  certifies with 1 stub; 8,724 scalar + 528 SIMD vectors agree with V8);
  G1, G3, G4, G5, G8, G9, declared modes and `:fun2` done (3.0 D3 scope: 2
  stubs, 2 dropped rules); the mode-table inference
  (W1/G2 general form) open. P7 🔶: the wasm3 plan exists as a **draft**
  ([plan/wasm3-translation/plan.md](../wasm3-translation/plan.md)); every
  note is incorporated
- **Next action**: the user decides D1-D6 ([decisions](notes/decisions.md));
  a Fable session designs the mode table and reviews the wasm3 draft. After
  that the draft becomes final and the wasm3 plan starts at its M0
- **In progress / uncommitted**: nothing. The old single-book driver
  `translate/tests/spec/t7-spec.lisp` (untracked, the user's) is superseded
  by `t7-lib.lisp` + `run-all.sh` and was left in place
- **Decisions D1-D6**: none confirmed by the user. Assumed and built on:
  D1, D2 (incl. `rt/` in package `WRT`), D3, D5, D6; D4 open
- **Blocked on**: the user's decisions (D1-D6) for the final wasm3 plan
- **Regressions**: `make -C translate check` (1.0), `make -C translate check-2.0`
  (2.0), flake checks `translate-il`, `translate-gen-wasm1`

### Where things are written down

| What | Where |
|---|---|
| Plan, gap analysis, milestone checkboxes | this file |
| Intermediate findings, designs, raw data, and the index of them | [notes/](notes/README.md) |
| Which model to use for which task | [suggested-model-choice.md](suggested-model-choice.md) |
| Per-session procedure | [step.md](step.md) |
| The user's prompts that shaped this plan, in order | [seed.md](seed.md) (the user's file; do not edit) |

Findings that are only in a conversation or a scratch directory are lost on
resume. Every milestone item below that produces a finding names the note it
goes to, and P7 consumes the notes index row by row.

---

## 1. Probe (2026-11-14): what happens today

Everything in §2-§4 comes from running the existing pipeline, unmodified, on
the 2.0 and 3.0 sources. The scripts and raw outputs are in
[notes/P0-probe-2026-11-14.md](notes/P0-probe-2026-11-14.md); reproduction is in §8.

### 1.1 Size

| | WASM 1.0 | WASM 2.0 | WASM 3.0 |
|---|---|---|---|
| `.spectec` files / lines | 10 / 2,353 | 10 / 4,175 | 37 / 9,353 |
| IL (`--ast --all-passes`) lines / bytes | 13,309 / 315 KB | 34,341 / 798 KB | 66,179 / 1.57 MB |
| Top-level IL forms | 318 | 470 | 974 |
| `typ` / `def` / `rel` / `gram` (rec members counted) | 90 / 132 / 36 / 61 | 145 / 214 / 41 / 71 | 208 / 462 / 125 / 232 |
| Rules | 137 | 265 | 567 |
| `Step_pure` / `Step_read` / `Step` rules | 29 / 13 / 13 | 56 / 47 / 23 | 79 / 103 / 36 |
| `Instr_ok` rules | 31 | 74 | 110 |
| Clause-less defs (builtins) | 45 | 64 (63 `hint(builtin)`) | 93 (88 `hint(builtin)`) |
| `hint(inverse)` in source | 4 | 12 | 16 |
| Defs taking `def` (function) parameters | 0 | 0 | 16 |
| Defs taking type parameters | 4 | 8 | 17 |
| Largest `rec` group | 2 relations | 2 relations | 19 relations |
| Grammars: binary `B*` / text `T*` | 61 / 0 | 71 / 0 | 90 / 142 |
| Official test suite (`spectec/test-interpreter`) | spec-test-1: 75 files | spec-test-2 | spec-test-3: 259 `.wast` |

### 1.2 Pipeline result per stage

| Stage | 2.0 | 3.0 |
|---|---|---|
| Stock `spectec --ast --all-passes` | ✅ | ✅ (all 37 files; also works with the `X.*`, `6.*`, `7.*` files left out) |
| ACL2 reader on the IL | ✅ | ✅ (strings now contain `\"` and `\\`; both read correctly) |
| T1 schema check (`il-check`) | ✅ 0 errors | ❌ 3 errors, all in `Tchar` (see §2) |
| Mangling | ✅ injective, 19 renames | ✅ injective, 27 renames, no tag collisions |
| New IL node kinds vs 1.0 | none | `alt` and `text` terminals (grammars), `equiv`, `list1` |
| Translator phase 1 (compile), 1.0 config minus the `Module_ok` override and the `Bmodule` patch | 631 events, **10 stubs** | **crashes** (control stack exhausted) on one form. With that form skipped: 1,268 events, **110 stubs**, 1,079 logged errors, 0.5 s |
| Phase 2, certification, any test | not run | not run |

**After P0** (`make probe`, [P0-probe-tool](notes/P0-probe-tool.md)): 3.0
schema ✅ 0 errors; phase 1 no longer crashes: 1,269 events, **111 stubs**
(the extra one is the zero-arity notation relation, now a clean stub), 1,080
errors. With the D3 scope (`EXCLUDE='X.* 6.* 7.*'`): 993 events, **35 stubs**,
249 errors. 1.0 and 2.0 are unchanged.

"0 stubs" for a form means only that the compiler accepted it. Nothing from
2.0 or 3.0 has been certified or executed.

2.0 stubs: `Step`, `Step_read`, `Step_pure`, `Module_ok`, `Instrs_ok`,
`Instr_ok`, `$vrelop_`, `$vextunop__`, `$vextbinop__`, `GRAM/Binstr`.

3.0 stubs, by cluster (41 outside the text format + 69 text grammars):

| Cluster | Stubs | Count |
|---|---|---|
| Reduction | `Step_pure`, `Step_read`, `Step` | 3 |
| Instruction and module typing | `Instr_ok`, `Instrs_ok`, `Module_ok` | 3 |
| Type validation (one 19-relation `rec` group) | `Heaptype_ok`, `Valtype_ok`, `Typeuse_ok`, `Resulttype_ok`, `Storagetype_ok`, `Comptype_ok`, `Subtype_ok2`, `Rectype_ok2`, `Deftype_ok` | 9 |
| Subtyping | `Valtype_sub`, `Heaptype_sub`, `Deftype_sub`, `Comptype_sub` | 4 |
| Numerics (mostly SIMD) | `$vunop_`, `$vbinop_`, `$vternop_`, `$vrelop_`, `$vshiftop_`, `$vswizzlop_`, `$vextunop__`, `$vextbinop__`, `$fvrelop_`, `$ivbitmaskop_`, `$ivadd_pairwise_`, `$ivdot_`, `$ivdot_sat_`, `$utf8single` | 14 |
| Instantiation | `$evalexprs`, `$evalglobals` | 2 |
| Soundness appendix (`7.*`) | `Context_ok`, `Moduleinst_ok`, `ImmutReachable`, `Store_ok`, `Extend_store` | 5 |
| Notation (`X.*`) | `NotationTypingScheme` (+ the crash) | 1 |
| Text format (`6.*`) | 69 of the 142 `T*` grammars | 69 |

The binary grammar (`5.*`, 90 grammars) compiles with no stubs.

---

## 2. Gap analysis: SpecTec formalism

What the translator supports today versus what the 3.0 IL uses. "Sites" are
counts from the 3.0 error log; a stubbed form logs every failing rule, so
counts overstate the number of distinct problems.

### 2.1 Hard gaps (construct not supported at all)

| # | Construct | 3.0 use | Today | Needed |
|---|---|---|---|---|
| G1 | **Function-valued arguments** (`(def "f")` as a call argument; `def` parameters) | 16 defs take them (`$ivunop_`, `$fvbinop_`, `$ivrelopsx_`, ...), 53 call sites in 8 SIMD dispatchers | `cargs` rejects: "higher-order argument" | Specialize the callee per function argument (all 53 sites pass a constant name), or pass a tag and dispatch. Specialization keeps everything first-order and logic-mode |
| G2 | **Relation premises with several outputs** | `Eval_expr: z; expr ~>* z'; val*` (store and values both produced) in `$evalexprs`, `$evalglobals` | `:fun` mode fixes "last component = output" | Per-relation mode declarations with any set of output positions (see W1) |
| G3 | **Iterated premise with a counter and no list domain** (`(if ...)^(i<n)`, `(R ...)^(a<\|s.TAGS\|)`) | 34 sites: `Extend_store` 30, `Store_ok` 3, one `Step_read` array rule | "premise" | Bounded-quantifier loop over `0..n-1`, as `citer` already does for expressions |
| G4 | **Iterated premise where every domain is an output of a non-relation premise** (`(if $ibytes_(K, j) = ...)^(k<M)` binding `j*`) | one `Step_read` vector-load rule | "iterated premise without inputs" | Extend the existing output-list machinery from `rule` premises to `if` premises |
| G5 | **Disjunction whose branches bind a variable differently** | 3 sites in `Instr_ok` (`t' = numtype \/ t' = vectype`, `select`) | "disjuncts bind different variables" | Treat as a membership test after `t'` is bound, or enumerate branches |
| G6 | **Text grammar**: `text` terminals, character-code literals above `0xFF`, `alt` | 736 sites, 67 grammars | "grammar symbol"; the schema also rejects `(num 0xD7FF)` because `hexbyte-p` wants exactly two digits | Only if the text format is in scope (D3). The schema fix is needed regardless, or the `6.*` files must be left out |
| G7 | **Relation with zero rules and an empty tuple** (`NotationTypingPremisedots`) | 1 (in `X.2`) | Translator **crashes** with stack exhaustion | Exclude `X.*` from the input, and make the compiler fail cleanly on this shape |
| G8 | **Existentially quantified index** (found in P1): a variable bound only by `i < \|l\|`, used as `l[i]` (`Deftype_sub/super`, `Heaptype_sub/rec-sub`; `ImmutReachable` in `7.*`) | 2 rules in `0.*`-`5.*`, 3 in `7.*` | "condition with unbound variables" | Bounded existential search over `0..\|l\|-1`. See [P1-typing-root-causes](notes/P1-typing-root-causes.md) |
| G9 | **Binding order inside a list pattern** (found in P1; mechanism probable): `CONST $lunpack(Lnn) c_1` is matched before the later element `VSPLAT (Lnn X M)` binds `Lnn` | 2 rules (`Step_pure/vsplat`, `vreplace_lane`) | "unbound variable" | Defer call patterns inside list patterns, as `cpat-args-defer` does for arguments |

### 2.2 Soft gaps (supported in 1.0, but the mechanism does not stretch)

| # | Area | What 3.0 does | Why today's mechanism falls short |
|---|---|---|---|
| S1 | **Inverse functions** (*the 16 hinted pairs are read from the IL since P3; the `inv_*` defs still need builtins*) | 16 `hint(inverse)` pairs; `Step_read` load rules solve `$nbytes_(nt, c) = bytes`, `$vbytes_`, `$zbytes_`, `$concatn_`, and SIMD rules solve `N = $jsize(Jnn)` for `Jnn` and `$ibits_(32, c) = ...` for `c` | `--ast` drops hints, so pairs are copied by hand into the config (5 today). Two inverses are also *used directly* in the spec (`$inv_lanes_`, `$inv_concat_`) and are builtins. Inverses of non-builtins (`$isize`, `$jsize`: finite functions) must be generated, not hand-written |
| S2 | **Mode inference for relations** | 125 relations; `: OK` and `<:` judgements whose last component is the subject, not an output | **Root causes isolated in P1** ([P1-typing-root-causes](notes/P1-typing-root-causes.md)): mode selection, not missing constructs. Failing rules for `:fun` / `:check` / `:multi`: type group 22 / 9 / **2** (both G8), `Instr_ok` 15 / 9 / **3** (all G5). An all-`:check` assignment is never tried. Some rules compile and are still incomplete: `Heaptype_sub/trans` picks a single witness `ht'` from `Heaptype_ok`'s split variant |
| S3 | **Instruction typing** | 110 rules. New stack-polymorphic rules (`return_call*`, `throw`, `throw_ref`), subsumption through `Instrtype_sub`, local-initialization tracking in the instruction type (`t_1* ->_(x*) t_2*`) | The `R` / `R/SPLIT` multi-mode trick assumed the last component splits as `c(a, b)`. With the `x*` component and subtyping it needs re-validation. In the probe's attempt 14 `Instr_ok` rules were dropped from the split variant, including non-polymorphic ones (`array.new_data`, `extern.convert_any`) |
| S4 | **`Module_ok`** | Different shape from 1.0: tags, recursive types, staged contexts `C'`, `Globals_ok`/`Types_ok` as separate relations | The 75-line hand-written `:rel-override` is 1.0-specific and must be redone. Since 3.0 sequentializes more, check first whether generic modes now cover it |
| S5 | **Equations defining a result arithmetically** | `$utf8single` (the 1.0 `$utf8` problem, renamed) | Config `:def` override + hand-written inverse. Carry over |
| S6 | **Nondeterminism** | `$ND`, `$relaxed2/4`, ten `$R_*` parameters (relaxed SIMD); float ops; `memory.grow`/`table.grow` | 1.0 policy was "first applicable rule; one float result; canonical NaN". 3.0 makes the choice points explicit builtins, so the policy must be a stated decision (D4) |
| S7 | **Builtins** | 93 clause-less defs. About 30 new numeric ones: `trunc_sat__`, `narrow__`, `iavgr_`, `iq15mulr_sat_`, `ibitselect_`, `fpmin_/fpmax_`, `frelaxed_*`, `lanes_`/`inv_lanes_`, `ibits_`/`fbits_`, `vbytes_`/`zbytes_`/`cbytes_`, `ceilz`, `s33_to_u32`, ... | Hand-written in `rt/builtins.lisp` (319 lines for 45). Several clause-less defs are **not** numeric builtins: `hostcall`, `allocX`, `dots`, `instrdots`, `ieee_`, `ND`, `R_*`. "Clause-less = builtin" no longer classifies them; each needs an explicit category |
| S8 | **Type families and type parameters** | 17 defs with type parameters (`$concat_(syntax X, ...)`, `$relaxed2`, `$disjoint_`); families indexed by other families (`lane_($lanetype(shape))`) | Type arguments are dropped and type parameters are unchecked in recognizers. Sound for execution, but recognizers for such types are vacuous, which matters for guards and for any typed theorem |
| S9 | **Subtype patterns** (`sub t1 t2 e` in pattern position) | 1,314 `sub` nodes vs 260; deeper hierarchies (`ref <: val`, `addrref <: ref`, `typeuse <: heaptype`, `deftype <: typeuse`) | Compiled to a recognizer call on the scrutinee: cost grows with type depth, and it relies on recognizers being exact (see S8) |
| S10 | **`||G||` (byte length of a match)** | Still written `len = \|\|BX\|\|` in the source (2 sites); the 3.0 IL was not re-checked | Config `:sized`, keyed by grammar and variable name. Carry over after checking the IL and the names |

### 2.3 Things that turn out not to be gaps

- No new expression, type, path or premise node kinds in the core (`0.*`-`5.*`).
- `real` literals: none. `else`, `let`, `cvt`, `ext`, `upd`, `slice`, `comp`,
  `mem`, `lift`, `unopt`: all present in 3.0 and already handled.
- The 1.0 `Bmodule` version bug is fixed in the 3.0 source (`Bversion` is four
  literal bytes), so that `:il-patch` goes away.
- No variant mixes an atom-free case with other cases, so newtype elision
  stays unambiguous.
- Translator speed is not an issue (0.5 s for the whole 3.0 IL).

---

## 3. Gap analysis: plumbing

Weaknesses in how the pipeline is built, independent of any single construct.

| # | Weakness | Evidence | Consequence for 3.0 |
|---|---|---|---|
| W1 | **Modes are guessed, three shots per `rec` group** (`:fun` = last component is the output, then `:check` for members that failed, then `:multi` for the whole group). There is no per-relation mode table and no way to state a mode | `crel-form-1` | In the 19-relation type group one unresolvable member stubs every member that failed the `:fun` shot, which is every `: OK` judgement. No relation can have two outputs (G2) |
| W2 | **Stub granularity is the whole relation** (or `rec` member). *Fixed for relations in P1* | 3 `Step*` stubs for roughly 10 failing rules out of 218 | Cannot report "N of M rules translated", cannot run a partial semantics, cannot bring up features one proposal at a time |
| W3 | **Misleading diagnostics** (*fixed in P1*): after all modes fail, the log holds the `:fun` attempt's errors; errors carry the function name but not the rule id | The 3.0 log blames `Valtype_ok` for "unbound variable numtype", a `:fun`-mode artifact | Root-causing S2 from the log is guesswork. This is the first thing to fix |
| W4 | **Single-spec hard-coding**: `il/wasm-1.0.il.sexp`, `gen/wasm1.lisp`, package `W1T`, flake outputs `wasm1-il` / `wasm1-spec-tests`, header text, the count `318` in `t1-il` | `run.lsp`, `emit.lisp`, `Makefile`, `flake.nix` | No second target without copying the tree. The spec file list is a glob over one directory, with no way to leave out `X.*`, `6.*`, `7.*` |
| W5 | **Config references are unchecked and version-specific** | Running with the 1.0 config on 3.0 raised no complaint, although `$utf8`, the `Module_ok` override and the patch target do not apply | A stale or misspelled entry silently does nothing. Entries must fail when their target is missing, and config must be per spec version |
| W6 | **Hints are lost at the hand-off** (`backend-ast/print.ml` ignores `HintD` and case/field hints) | `hint(inverse)`, `hint(builtin)`, `hint(partial)` | Hand-copied inverse table (5 → 16+ pairs), and no way to tell `hint(builtin)` from "declared, defined nowhere" (S7) |
| W7 | **One generated book** for everything | `gen/wasm1.lisp`: 37 K lines, 473 events; the 3.0 probe produced 1,268 | Any change recertifies everything; no parallelism; one failure hides the rest. Needs a split along IL order (syntax / numerics / typing / execution / binary) |
| W8 | **`%try-logic` hides regressions**: an event that stops being admitted in logic mode silently becomes `:program` | Counts are recorded by hand in the plan | Need a generated, checked-in mode manifest (logic / guard-verified / program per function) that `check-gen` diffs |
| W9 | **Untyped runtime is slow and unsafe at the edges**: memory is a byte list (each step O(memory)), records are alists, `nth` out of range returns `nil`, `:program` code can crash SBCL on ill-formed input | T5: slowest vector 8 s for 40 loop iterations; fuel 10^6 | spec-test-3 has 259 scripts, with GC heaps, 64-bit memories and SIMD loops. Needs a measured baseline and a plan before committing to a pass-rate target |
| W10 | **Conformance driver is unfinished and 1.0-shaped** | T7 is open; `tests/spec/` and `gen-spec-tests.mjs` are uncommitted; the driver disables every post-1.0 feature in `wast2json` and skips scripts using old NaN assertion syntax | 3.0 needs the driver before anything else can be validated at scale, with multi-value, reference values, `v128`, exceptions and GC values in assertions |
| W11 | **Oracle coverage is 1.0-only** | 8,015 numeric vectors, 515 invoke vectors, 13 modules | No oracle for the ~50 new builtins. Node/V8 can produce SIMD and saturating-conversion vectors the same way |
| W12 | **Determinism is checked only locally** | No CI workflow in the repo; `nix flake check` covers the IL but not `check-gen` | Add `check-gen` as a flake check per target |
| W13 | **Open 1.0 obligations that 3.0 inherits** | T8: completeness of the `ctxt-instrs` `:redex` split is unproved; the typing clique (25 functions) is still `:program`; multi-mode typing is incomplete for mid-sequence dead code | 3.0 adds a second evaluation context (`Step/ctxt-handler`) and triples the typing clique. Decide which of these block 3.0 and which are carried |

---

## 4. Decisions needed before the wasm3 plan is written

Recommendations are first. Each one changes the size of the wasm3 plan.
When the user decides one, record it with the date in `notes/decisions.md`
and in "Current state".

| # | Decision | Recommendation | Alternative |
|---|---|---|---|
| D1 | **Is 2.0 a stepping stone?** | Yes, as a prep gate only (P4). It passes the schema today, has 10 stubs, and exercises G1, S1 and SIMD without GC types or exceptions | Go straight to 3.0 |
| D2 | **One tree or one per version?** | One translator, one `rt/`, per-version `il/`, `config/`, `gen/` and package (`W1T`, `W3T`). 1.0 stays as the regression target | Fork `translate/` to `translate3/` |
| D3 | **Scope of 3.0 files** | In: `0.*`-`5.*` (syntax, validation, numerics, execution, binary). Out: `X.*` (notation). Deferred, each as its own milestone: `6.*` text format (a generated `.wat` parser), `7.*` soundness judgements (valuable later as the statement of type soundness) | Everything |
| D4 | **Nondeterminism policy** | Deterministic profile: `$ND` false, `$R_*` fixed to the values V8 uses, canonical NaN, growth succeeds when within limits. Each choice is a named builtin, listed in the generated header | Set-valued semantics |
| D5 | **How to get hints** | Small upstream-able patch to `backend-ast/print.ml` that prints hint definitions, applied in the flake (W6). Keeps "no fork" in spirit: a 20-line patch file against a pinned rev | Keep copying hints into config |
| D6 | **Validation target for 3.0** | Execution first (decode → instantiate without `Module_ok` as a test-only path → invoke), typing second. In 1.0 typing was the hardest part and 3.0 typing is 3x larger with subtyping | Typing and execution together |

---

## 5. Milestones

Each milestone ends with 1.0 still passing `make -C translate check`
byte-identically, unless the milestone says the output changes.

### P0: Probe as a tool ✅ (2026-11-14, [P0-probe-tool](notes/P0-probe-tool.md))
- [x] `make -C translate probe SPEC=3.0`: builds the IL into a scratch
      directory and prints the §1.2 table (schema errors, mangle report,
      events, stubs by cluster, error kinds). No files under `gen/` change.
      *Done: `.probe/<v>/report.txt`, stubs grouped by source file, plus the
      §1.1 IL statistics; `EXCLUDE='X.* 6.*'` leaves files out. 13 s for 3.0*
- [x] Fix G7 so the probe needs no skip list: zero-rule relations compile to a
      clean error, never a crash. *Done: arity 0 is a logged error and a stub
      (cause: `gsyms-prefixed` called with -1)*
- [x] Schema: accept grammar character codes wider than one byte (G6, schema
      part only). *Done: 3.0 schema errors 3 → 0*

**Exit** ✅: the probe reproduces the §1 numbers for 1.0, 2.0 and 3.0 in one
command each (except the `hint(inverse)` counts, which are not in the IL: P3).
It found one miscount (3.0 has 37 files, not 39). 1.0 `make check` passes
byte-identically.
**Notes**: probe output per spec version stored under `notes/data/`, and re-stored after every later milestone that changes it.

### P1: Diagnostics and granularity (W2, W3) ✅ (2026-11-14, [P1-gap-list](notes/P1-gap-list.md), [P1-typing-root-causes](notes/P1-typing-root-causes.md))
- [x] Every logged error carries relation, rule id and attempted mode.
      *Done: `(fn what x :rule "Rel/id" :pos k :mode m)`; `:pos` because rule
      ids need not be unique*
- [x] On total failure, report the errors of the attempt that got furthest
      (fewest failing rules), not always `:fun`. *Done; the probe also prints
      every group's scores per attempt*
- [x] Per-rule stubs: a rule that does not compile is dropped and listed; the
      relation is still emitted. The generated header and the probe report
      "rules translated / rules total" per relation. *Done for relations
      (defs and grammars stay whole-unit stubs). Header and probe list the
      partial relations only, so 1.0's header is unchanged. A relation that
      would lose every rule stays a stub. Decision: the emitted mode is
      `:fun` whenever dropping rules saves it, the interface the old stub
      had, so this milestone changes granularity, not modes (P4 owns modes).
      3.0 D3 scope: stubs 35 → 21, 14 relations emitted without 42 rules;
      2.0: stubs 10 → 5, 5 relations without 20 rules*
- [x] Re-run the probe and replace the S2 row with real root causes for the
      type-validation and subtyping groups. *Done: mode selection; in
      `:multi` only 2 type-group rules (G8, new) and 3 `Instr_ok` rules (G5)
      fail; `Heaptype_sub/trans` compiles with a single witness (incomplete)*

**Notes**: `notes/P1-gap-list.md` (the per-rule list: rule id, cause, gap id
from §2, proposal) and `notes/P1-typing-root-causes.md`.

**Exit** ✅: a per-rule gap list for 3.0 exists, each entry with a rule id
and one cause (14 rules in the best attempt, D3 scope, plus 16 defs). 1.0
output is unchanged: `make check` passes, `gen/` byte-identical.

### P2: Multi-spec plumbing (W4, W5, W7, W8, W12) ✅ (2026-11-14, [P2-layout](notes/P2-layout.md))
- [x] Spec target as a parameter: `SPEC=1.0|2.0|3.0` selects the source file
      list (with excludes), `il/wasm-<v>.il.sexp`, `config/wasm-<v>.lsp`,
      `gen/wasm<v>/`, and the package name. Flake outputs become
      `wasm-il.<v>`; `SPEC_REV` records the file list.
      *Done 2026-11-14 ([P2-layout](notes/P2-layout.md)): `gen/wasm-<v>/`,
      `W<major>T`; flake outputs are `wasm1-il`/`wasm2-il`/`wasm3-il`, since
      `packages` cannot nest. 1.0 definitions byte-identical (2 header lines
      changed), `make check` and `make compare` pass. 2.0/3.0 generate (688 /
      1,086 events) but cannot certify: `rt/` is in package `W1T` (open,
      with D2)*
- [x] Config entries are validated: an entry whose def, relation, rule or
      grammar does not exist in the IL is a hard error. *Done 2026-11-14
      ([P2-layout](notes/P2-layout.md)): 1.0 clean; one stale entry in the
      2.0/3.0 configs (`bytes_` inverse) removed. Found: 3.0 declares all 16
      `inv_*` inverses as defs, so S1 is mostly missing pairs (P3)*
- [x] Generated output split into several books in IL order, with a generated
      `top.lisp`. *Done 2026-11-14 ([P2-layout](notes/P2-layout.md)): one
      book per source file (decls map checked in next to the IL), chained in
      IL order; the top book stays `wasm1.lisp`. 1.0 events byte-identical,
      10 parts; 3.0 24 parts, of which `5.3-binary.instructions` is 68% of
      the lines*
- [x] Generated mode manifest (`gen/.../modes.lsp`: logic / guards / program
      per function, stubs, dropped rules), checked in and compared by `check-gen`.
      *Done 2026-11-14 ([P2-layout](notes/P2-layout.md)) with one change: modes
      exist only after certification, so a test book (`t0-modes`, in `make
      check`) compares them, and `make modes` rewrites the file; stubs and
      dropped rules stay in the header that `check-gen` compares. 1.0: 503
      functions, 160 guards / 308 logic / 35 program*
- [x] `check-gen` per target as a flake check. *Done 2026-11-14:
      `checks.<system>.translate-gen-wasm1` (8 s); `translate-il` also
      compares the decls file. Only 1.0 has a checked-in target*

**Exit** ✅: 1.0 regenerates through the parameterized pipeline; its
generated definitions are byte-identical apart from file boundaries (10
parts) and two header lines; `make check` (now with `t0-modes`) and
`make compare` pass.

**Notes**: `notes/P2-layout.md` (final directory, package and flake naming).

### P3: Hints at the hand-off (W6, S1, S7, D5) ✅ (2026-11-14)
- [x] Patch `backend-ast/print.ml` to emit hint definitions; schema and reader accept them.
      *Done 2026-11-14 ([P3-hints](notes/P3-hints.md)): 15-line patch in
      `nix/`; 1.0 IL +244 hint lines, otherwise identical; generated code
      unchanged. 3.0 IL carries all 16 inverse pairs*
- [x] `:inverse` config entries are replaced by pairs read from the IL.
      *Done 2026-11-14 ([P3-hints](notes/P3-hints.md)): the `utf8` override
      declares its own inverse; 1.0 code unchanged. 2.0 stubs 5 → 2, 3.0
      (D3 scope) 21 → 16; 3.0 failing reduction rules 10 → 4 of 218*
- [x] Builtin classification from `hint(builtin)`: numeric builtin (must be in
      `rt/`), choice parameter (D4), host hook (`hostcall`), notation
      (ignored). A clause-less def in no category is a hard error.
      *Done 2026-11-14 ([P3-builtin-inventory](notes/P3-builtin-inventory.md)):
      one counted `:builtins` entry per 2.0/3.0 config; the translator lists
      numeric builtins with no definition in `rt/`. 3.0 (D3 scope): 89 =
      77 numeric (34 missing in `rt/`) + 11 choice + 1 host; 2.0: 64 (21
      missing); 1.0: 45 (0 missing), output unchanged*
- [x] Generated inverses for finite functions (`$isize`, `$jsize`, `$fsize`, `$jsizenn`).
      *No work needed: the 2.0/3.0 spec defines `inv_isize`, `inv_jsize`,
      `inv_fsize`, `inv_jsizenn` with clauses, and they compile. The other
      12 `inv_*` are clause-less builtins in the inventory*

**Notes**: `notes/P3-builtin-inventory.md` (every clause-less def of 3.0:
category, status in `rt/`, oracle source).

**Exit** ✅: the 1.0 config loses its `:inverse` entry and the generated 1.0
code is unchanged. The 3.0 probe shows no "pattern" errors caused by a
missing inverse pair. *Met 2026-11-14: the 17 remaining "pattern" errors are S5, S4,
`:fun` typing artifacts and text grammars ([P3-hints](notes/P3-hints.md))*

### P4: Generic translator gaps, gated on 2.0 (G1-G5, D1) 🔶
- [x] G1 function arguments by specialization. *Done 2026-11-14
      ([P4-generic-gaps](notes/P4-generic-gaps.md)): IL pre-pass; 16 defs
      replaced by 53 specializations; 3.0 (D3 scope) stubs 16 → 8. Found:
      the 16 defs had compiled silently wrong (calls to `%UNKNOWN-f_`)*
- [ ] W1/G2: explicit mode table per relation (input and output positions),
      inferred where the current heuristic works, overridable by a counted
      config entry; modes solved per relation, not per attempt per group.
      *First step done 2026-11-14 ([P4-generic-gaps](notes/P4-generic-gaps.md)):
      declared modes (counted `:modes` entry) and a printed mode table.
      With the type group `:check` and instruction typing `:multi`, 3.0 (D3
      scope) has 4 stubs and 7 dropped rules (was 8 and 36); 2.0 has 2
      stubs and 1 dropped rule. Inference per relation and several outputs
      (G2) are the Fable design session. `:fun2` (last two components
      out) declared for `Eval_expr`: 3.0 D3-scope stubs 4 → 2*
- [x] G3, G4 iterated premises; G5 disjunctions. *G3 done 2026-11-14
      (count-only iteration, an aux loop; full 3.0 stubs 83 → 81). G5 is not
      mechanical: `t'` is existential, so it goes with the mode table
      ([P4-generic-gaps](notes/P4-generic-gaps.md)). G4 done too
      (`Step_read` 102/103). G9 (list-pattern order) done: 3.0 reduction
      failures 1 of 218; 2.0 reduction relations complete. G5 (pure tests,
      finite existentials) and G8 (index search, deferred tests in the loop)
      done: 3.0 D3 scope has 2 dropped rules left; `Instr_ok` 110/110. Was: G8 goes with
      the mode table*
- [x] 2.0 as a full target: builtins for SIMD, saturating truncation and sign
      extension in `rt/`; Node/V8 numeric vectors for them (W11).
      *Done 2026-11-14 ([P4-wasm2-result](notes/P4-wasm2-result.md)): 21
      builtins added; 2.0 certifies with 1 stub (`Module_ok`); 8,724/8,724
      scalar and 528/528 SIMD vectors agree with V8; `make check-2.0`*

**Notes**: `notes/P4-mode-table-design.md` (design, alternatives rejected),
`notes/P4-wasm2-result.md` (2.0 numbers), and an updated `notes/P1-gap-list.md`.

**Exit** ✅ (2026-11-14): 2.0 translates with stubs limited to `Module_ok` (pending its
override) or fewer, certifies, and passes the 2.0 numeric vectors. The 3.0
probe is re-run and its stub and dropped-rule counts recorded.

### P5: Conformance driver (W10) ✅ (2026-11-14, [P5-conformance](notes/P5-conformance.md))
- [x] Finish wasm1 T7: commit the driver, record N/M for spec-test-1.
      *Done: one ACL2 session per script (a crash costs one script);
      **10,848 of 11,606 commands reached pass** (of 12,014 countable);
      40 of 67 scripts pass completely, 2 time out, 5 hit resource limits;
      578 of the 758 failures are 9 scripts whose module instantiation
      rejects (likely the dead-code typing incompleteness, W13)*
- [x] Parameterize it by spec version and feature flags; assertion values for
      multi-value, references and `v128`. *Done for the data: flake
      `wasm1-spec-tests` (output unchanged) and `wasm3-spec-tests`;
      `make spec-data SPEC=<v>`; the converter emits v128 lanes, references,
      `assert_exception` and `:UNSUPPORTED` for the unknown. Comparing those
      values in ACL2 needs a running 3.0 semantics*
- [x] Dry run on spec-test-3: how many scripts `wast2json` converts, how many
      modules the generated 3.0 binary parser accepts (the parser already
      compiles; this is its first real test). *Done 2026-11-14: 228 of 259
      scripts convert (5,365 modules; GC 1 of 17). Decode experiment (scratch
      `rt/` in `W3T`, missing builtins stubbed, `:program` mode): **4,562 of
      4,639 well-formed modules decode (98.3%)**, 604 of 643 malformed ones
      rejected (the 39 misses are invalid UTF-8). Found and fixed a
      translator bug (aux functions using the enclosing relation's formals);
      found a certification-time risk (`5_2-binary_types` guard proof
      >15 min)*

**Notes**: `notes/P5-conformance.md` (pass counts, skipped scripts and why).

**Exit** ✅: spec-test-1 result recorded; a decode-only pass rate for
spec-test-3 recorded (98.3%, by experiment: the `rt/` question is still open).

### P6: Runtime baseline (W9) ✅ (2026-11-14, [P6-runtime-baseline](notes/P6-runtime-baseline.md))
- [x] Measure steps per second and the cost per memory access on the 1.0
      corpus; profile one spec-test-1 script that is slow. *Done: 0.03 ms
      per step without memory, about 10.4 ms per 64 KiB page per step with
      memory (1 page 15 ms, 16 pages 181 ms), about 19 whole-configuration
      `%SIZE` traversals per step (the termination checks), memory access
      itself about 1 ms; spec-test-1 averages 0.22 s CPU per command*
- [x] Decide and write down the 3.0 approach: keep the byte-list encoding
      (spec-faithful) with an execution-only fast path proved or tested
      equal, or accept a time budget and a skip list. *Recommended: keep
      byte lists; make the generated `Step` termination checks ignore the
      store (expected about 300× at 1 page), else `mbe` with a proof;
      driver limits for huge locals and growth*
- [x] List the places where `:program`-mode code can crash on ill-formed
      input, and whether guards or a well-formedness check in the driver covers them.
      *Done: the 5 spec-test-1 crashes are all list-size limits in logic
      code (locals, `memory.grow`, segment bounds); the 35 `:program`
      functions get only parser output; a `MODULE-P` check in the driver is
      proposed*

**Notes**: `notes/P6-runtime-baseline.md`.

**Exit** ✅: a time estimate for running spec-test-3, with the measurements
behind it: about 1.5-2 h wall with 8 sessions at today's speed, plus a tail
of about 7 scripts at the 1 h limit.

### P7: Write `plan/wasm3-translation/plan.md` 🔶 (2026-11-14: [draft](../wasm3-translation/plan.md))
- [x] Walk the index in `notes/README.md` row by row. Each note is either
      incorporated (record the wasm3 plan section in its header and index
      row) or dropped with a reason. No row may stay at `no`. *Done: all 12
      notes incorporated in the draft*
- [ ] Record D1-D6 as decided (from `notes/decisions.md`). *Recorded as
      assumed/open in [decisions](notes/decisions.md) and the draft's §1;
      waits for the user*
- [x] Refreshed probe table, and the per-rule gap list from P1/P4 as the work
      list, grouped by proposal (SIMD, bulk memory, reference types, tail
      calls, exceptions, GC, memory64, multi-memory, relaxed SIMD). *Draft §2, §3*
- [x] Translation-scheme delta against wasm1 §2: modes, function arguments,
      nondeterminism policy, typed recognizers, package and layout. *Draft §4*
- [x] Milestones with exit criteria in the wasm1 style, in the D6 order:
      syntax, numerics and builtins, binary decode, execution, instantiation,
      type validation and subtyping, instruction typing, `Module_ok`,
      conformance, logic mode and proofs. Deferred: text format, soundness judgements.
      *Draft §5 (M0-M9)*
- [x] Builtin inventory with an oracle source for each. *Draft §3/M1, table in P3-builtin-inventory*
- [x] Config budget: expected counted overrides, each tied to a gap in §2. *Draft §6*
- [x] Risks, with the go/no-go points (instruction typing with subtyping is
      the likely one; Strategy B from wasm1 §1 remains the fallback for `Step`). *Draft §7*

**Exit**: the wasm3 plan exists, every number in it comes from the probe or a
test run and cites its note, and every row of the notes index is `yes` or `dropped`.
*Met for the draft; the plan becomes final when D1-D6 are decided (and,
per the model-choice note, after a Fable review of it and the mode-table design)*

### Order and dependencies

```
P0 ─▶ P1 ─▶ P4 ─▶ P7
 └──▶ P2 ─▶ P3 ─┘
P5, P6 need only P2 and can run alongside P3/P4.
```

---

## 6. What the wasm3 plan can already assume

- Stock SpecTec at the pinned rev elaborates 3.0; the `--ast` hand-off holds.
- The IL core vocabulary is unchanged; the reader, mangler and (after P0) the
  schema need no redesign.
- Syntax recognizers, plain defs and the binary grammar are close: no stubs
  among the 208 types or the 90 binary grammars, and 16 stubs among 462 defs.
- Execution is closer than typing: 1 of 218 reduction rules fails in `:fun`
  after P4 (10 in P1; the 6 S1 inverses were missing pairs; G3, G4, G9 fixed):
  a nested inverse in `array.new_data-num`. Since P1 the rest of
  `Step`, `Step_read`, `Step_pure` is emitted.
- Typing is mostly a mode problem (P1): in `:multi` the type-validation and
  subtyping group fails 2 rules (G8) and instruction typing 3 (G5). The
  risk moves from "does it compile" to "is it complete": `Heaptype_sub/trans`
  compiles with a single witness.

---

## 7. Risks to the prep itself

| Risk | Mitigation |
|---|---|
| P4's mode table turns into a redesign of the relation compiler | Keep the three existing strategies as the inference fallback; the table only adds declared modes and multiple outputs. 1.0 byte-identity is the guard |
| Per-rule stubs (P1) change 1.0 output | They must not: 1.0 has no failing rules. Any diff is a bug |
| The hint patch (P3) does not apply cleanly at a later SpecTec rev | It touches one printer file; offer it upstream. The fallback is today's config table |
| 2.0 gate (P4) costs more than it saves | Time-box it: if 2.0 is not certified after G1-G5 land, record its probe numbers and move on |
| Prep grows into doing 3.0 | P7's exit is a document. Anything 3.0-specific beyond the probe (GC builtins, the new `Module_ok`) belongs in the wasm3 plan |

---

## 8. Reproducing the probe

Run from `translate/` inside `nix develop ..`:

```bash
make probe SPEC=1.0      # or 2.0, 3.0; EXCLUDE='X.* 6.* 7.*' leaves files out
```

The report is `.probe/<v>/report.txt`, every logged error is in
`.probe/<v>/errors.lsp`. The probe ignores the 1.0-only config entries
(`:rel-override`, `:il-patch`) for every version except 1.0; set
`PROBE_DROP=` to keep them. The scripts are `il2acl2/probe.lsp` and
`il2acl2/probe-names.sh`. The hand-run procedure of the baseline is in
[notes/P0-probe-2026-11-14.md](notes/P0-probe-2026-11-14.md).
