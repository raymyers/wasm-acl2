# Generic translator gaps (G1, G3-G5, G8, G9)

- Milestone: P4 (items: G1 function arguments by specialization; G3, G4
  iterated premises; G5 disjunctions; and the P1-found G8, G9)
- Date: 2026-11-14
- Repo commit: 3d79703 plus this note's commit
- Status: draft (G1, G3, G4, G5, G8, G9 done; the mode-table inference open)
- Feeds wasm3 plan: scheme delta (function arguments), gap list, config budget
- Incorporated in wasm3 plan: yes (draft plan, §3, §4 (modes, patterns), §5 M5)

## Summary

G1 is done as an IL pre-pass (`il2acl2/specialize.lisp`): 16 defs with
function parameters are replaced by **53 specializations**, one per
constant function argument, matching the 53 call sites of the baseline.
In 3.0 (D3 scope) the stubs fall from 16 to **8**: all 8 SIMD dispatchers
now compile, and no "higher-order argument" error remains. Before G1 the 16
defs did not stub. They compiled **silently wrong**, calling
`|%UNKNOWN-f_|`, which no report showed. 1.0 is unchanged.

## Findings

### G1: function-valued arguments

- Pass (before compilation, after `:il-patch`): for a top-level def f with
  `def` parameters, every call that passes constant function names
  `(def "g")` becomes a call of `"f.g"` without them (mangled `$F.G`). `f.g`
  is f with the parameters substituted: binders `(def p ...)` and argument
  patterns `(def p)` removed, `(call p ...)` to `(call g ...)`, and `(def p)`
  passed to another such def becomes `(def g)`, which is specialized in turn.
  Each specialization is placed just before the first form that needs it
  (after its own needs), so every function it calls is defined earlier. The
  unspecialized f is dropped.
- 3.0: dropped `ivunop_ fvunop_ ivbinop_ ivbinopsx_ ivbinopsxnd_ fvbinop_
  ivternopnd_ fvternop_ ivrelop_ ivrelopsx_ fvrelop_ ivshiftop_
  ivshiftopsx_ ivswizzlop_ ivextunop__ ivextbinop__`; 53 specializations
  (`fvunop_.fabs_`, `ivunop_.iabs_`, `ivbinop_.iadd_`, ...), listed in the
  generated header. A spot check: `$IVUNOP_.IABS_/ITER2` calls `$IABS_`
  where the unspecialized version called `|%UNKNOWN-f_|`.
- No `|%UNKNOWN-...|` call is left anywhere in the generated 3.0 code.
- Probe, 3.0 D3 scope: stubs 16 → 8 (left: `Module_ok`, the 4 typing
  relations that lose every rule in `:fun`, `$evalexprs`, `$evalglobals`,
  `$utf8single`); errors 227 → 174; events 1,103 → 1,200. Full 3.0: stubs
  91 → 83.
- 1.0 and 2.0 have no defs with function parameters: the pass returns the
  forms unchanged. `make check` passes, `gen/wasm-1.0/` byte-identical.
- Limits: a def with function parameters inside a REC group, or a call with
  a non-constant function argument, is left as it was (none in 3.0).

### Not done in this session

- W1/G2 mode table: the design is flagged for a Fable session
  (model-choice item 1). G2 (`$evalexprs`, `$evalglobals`) depends on it.
- G3: done (section below). G4 (iterated `if` binding a list,
  1 rule), G5 (3 rules; not mechanical, see below), G8 (existential index, 2 rules),
  G9 (list-pattern binding order, 2 rules): open; see
  [P1-gap-list.md](P1-gap-list.md).
- 2.0 as a full target (builtins, oracle vectors, certification): needs the
  `rt/` package decision.

## Data

`data/probe-P4-G1-2026-11-14/`: `report-3.0.txt`, `report-3.0-core.txt`,
`rules-3.0-core.txt` (`make probe SPEC=3.0 [EXCLUDE='X.* 6.* 7.*']`).

## 2026-11-14: G3 (iterated premise with a count and no domain)

- `compile.lisp` `cprem`: `(ITER prem (LISTN n ["k"]))` with no list domain
  holds iff `prem` holds for k = 0 .. n-1. It compiles to an aux function
  `<fn>/UPTO (k n free-vars...)` with measure `n - k`. If the inner premise
  would bind variables, that is an error ("iterated premise with a count
  binds variables"), not a guess. An unbound `n` gives "iterated premise
  with an unbound count".
- Effect (full 3.0): no "premise" error is left (34 sites before, from
  `Extend_store`, `Store_ok` and one `Step_read` rule). Stubs 83 → 81:
  `Store_ok` and `Extend_store` (`7.1`) now compile. In the D3 scope the
  stub count stays 8 and errors fall 174 → 173.
- `Step_read/array.new_data-num` still fails, for its second cause: `c*`
  is bound only inside an iterated inverse, `$concatn_(byte,
  $zbytes_(zt, c)^n, ...)`. That is a nested S1 case, which the inverse
  mechanism (it solves `f(a.., x) = v` for a variable `x`) does not cover.
- 1.0: no such premise; `make check` passes, `gen/` byte-identical.

## 2026-11-14: G5 is not a plain test (correction to P1-gap-list)

P1 said of `Instr_ok/select-impl`, `array.new_data` and `array.init_data`:
"`t'` is bound by then: compile the disjunction as a test". That is wrong.
In `select-impl`, `t'` occurs only in `Valtype_sub: C ⊢ t <: t'` and in
`t' = numtype ∨ t' = vectype`, so it is existential. Neither premise
binds it in check mode, and the disjunction's branches bind the fresh
`numtype` / `vectype`. Translating it needs either an enumeration of the
finite types `numtype` ∪ `vectype`, or the split variant of `Valtype_sub`
as a single witness (incomplete, as with `Heaptype_sub/trans`). That is a
mode and premise-ordering decision, so it goes with the mode table (W1),
not with G5's mechanical fix.

## 2026-11-14: G4 (counted iteration whose domains are outputs)

- `cprem`: `(ITER prem (LISTN n ["k"]) (dom x xs)...)` with every domain an
  output (no input list) loops over k = 0 .. n-1 with an aux `<fn>/UPTO`.
  It runs the inner premise with k bound and collects each iteration's
  outputs into the output lists, like the existing list case (`/MAP`).
- Effect, 3.0 D3 scope: `Step_read/vload-pack-val` compiles
  (`Step_read` 101 → 102 of 103); errors 173 → 170. Reduction rules failing
  in 3.0: **3 of 218** (`Step_pure/vsplat`, `vreplace_lane`: G9;
  `Step_read/array.new_data-num`: nested inverse).
- 1.0 unchanged; `make check` passes.

## 2026-11-14: G9 (binding order inside a fixed-length sequence pattern)

- Cause confirmed: in `Step_pure/vsplat` the instruction list pattern is
  `[CONST $lunpack(Lnn) c_1, VSPLAT (Lnn X M)]`. Element 1 needs `Lnn`,
  which only element 2 binds, and `$lunpack` has no inverse.
- `compile.lisp` `cpat-elems`: the elements of a fixed-length sequence are
  independent positions. An element that fails to compile is rolled back
  (errors and aux functions) and retried once after the others, with the
  larger environment, the same way `cpat-args-defer` handles arguments.
  When every element matches in order, nothing changes. Spot check of
  the generated `vsplat` code: `:VSPLAT` is matched and `LNN` bound
  first, then the `:CONST` element is tested against `($LUNPACK LNN)`.
- Effect: 3.0 `Step_pure` 79/79 (was 77/79); **1 of 218** 3.0 reduction rules
  still fails (`Step_read/array.new_data-num`, the nested inverse). D3-scope
  errors 170 → 156. 2.0: `Step`, `Step_read`, `Step_pure` all complete; 2.0
  is left with 2 stubs (`Module_ok`, `GRAM/Binstr`) and instruction typing
  in `:fun` (`Instr_ok` 67/74, `Instrs_ok` 3/5).
- 1.0 unchanged; `make check` passes.
- Data: `data/probe-P4-G9-2026-11-14/` (`report-3.0.txt`,
  `report-3.0-core.txt`, `rules-3.0-core.txt`, `report-2.0.txt`).

## 2026-11-14: G8 deferred to the mode-table work

G8 (`Deftype_sub/super`, `Heaptype_sub/rec-sub`; `ImmutReachable` in
`7.*`) needs a bounded search over `i` that runs the *rest* of the rule for
each candidate: continuation-style compilation like the existing split
searches (`/SEARCHn`). Its rules fail only in `:multi`. The emitted mode for
typing is `:fun` until the mode table exists, so fixing G8 now changes no
emitted code. Do it together with the mode table.

## 2026-11-14: W1 first step, declared modes

Not the mode table design (still a Fable session, model-choice item 1),
only its "overridable by a counted config entry" part:

- Config `(:modes "label" :pairs (("Rel" . :fun|:check|:multi) ...) :reason ...)`,
  validated (relation exists, mode known). `set-modes`/`set-mode-ids` apply
  a declared mode in every attempt, so the inference varies only the
  undeclared members. The probe prints the final mode of every relation.
  1.0 (nothing declared): 13 `:fun`, 15 `:check`, 7 `:multi`, 1 `:closure`;
  output unchanged.
- 3.0 experiments (D3 scope, data in `data/probe-P4-modes-2026-11-14/`):

| Declared | Stubs | Dropped rules | Errors |
|---|---|---|---|
| nothing (before) | 8 | 36 | 156 |
| type group (19) `:check` | 4 | 26 | 135 |
| type group (19) `:multi` | 4 | 18 | 105 |
| type group `:check`, `Instr_ok`/`Instrs_ok` `:multi` (**committed**) | **4** | **7** | **68** |

  `:check` was chosen over `:multi` for the type group: under `:check`,
  `Heaptype_sub/trans` fails visibly (its intermediate is unbound), while
  `:multi` compiles it with a single witness (P1-typing-root-causes).
- Left in 3.0 (D3 scope): stubs `Module_ok` (S4), `$evalexprs` and
  `$evalglobals` (G2, two outputs), `$utf8single` (S5); dropped rules
  `Deftype_sub/super`, `Heaptype_sub/rec-sub` (G8), `Heaptype_sub/trans`
  (existential), `Instr_ok/select-impl`, `array.new_data`,
  `array.init_data` (G5), `Step_read/array.new_data-num` (nested inverse).
  Full 3.0: 78 stubs (69 of them text grammars, `6.*`).
- 2.0 with `Instr_ok`/`Instrs_ok` `:multi`: 2 stubs (`Module_ok`,
  `GRAM/Binstr`), 1 dropped rule (`Instr_ok/select-impl`, G5), 32 errors.
- What the mode table still has to do: infer these instead of declaring
  them, allow several outputs (G2), and decide existentials (G5, G8,
  `trans`).

## 2026-11-14: G2 for the last two components (`:fun2`)

- Declared mode `:fun2`: the last two components are outputs; the
  relation returns `(list (list out1 out2))`; a calling premise binds both
  with a tuple pattern. `crel-1-body`, `crule`, `rel-stubs` and
  `crule-premise` handle it; config validation accepts it.
- 3.0 config declares `("Eval_expr" . :fun2)` (`z; expr ~>* z'; val*`).
  Generated: `EVAL_EXPR (z expr)` returns `(z' vals)`, and `$evalexprs` /
  `$evalglobals` destructure it. Effect, D3 scope: stubs 4 → **2**
  (`Module_ok`, `$utf8single`), errors 68 → 56. Full 3.0: stubs 76 (69 text
  grammars, 5 in `7.*`/`X.*`, plus the 2).
- Not general G2: outputs must be the last components, and only two. Any
  set of output positions is the mode table's (W1) job.
- 1.0 unchanged; `make check` passes.

## 2026-11-14: G8 in `:check` mode (supersedes the deferral above)

The deferral above assumed that G8 rules fail only in `:multi`. Since the
type group is declared `:check`, they are dropped from emitted code, so G8
now matters.

- `cprems`: when no premise is ready and the rule is compiled in `:check`
  mode, a premise `if v < |l|` (v bound by nothing else, l bound) becomes
  "there is a v below |l| for which the other premises hold". An aux
  `<fn>/SOME (v n free-vars...)` loops over v (measure n - v); the other
  premises may not bind new variables. v is not visible after the loop.
- Effect, 3.0 D3 scope: `Deftype_sub/super` compiles (`Deftype_sub` 2/2);
  dropped rules 7 → 6; errors 56 → 53. `Heaptype_sub/rec-sub` still fails:
  its j is also used in the conclusion (`typeuse*[j]`), a deferred pattern
  test outside the loop. That needs the deferred tests inside the search
  (mode-table work).
- The real 3.0 books (shared `rt/` in `WRT`) certify through
  `2_1-validation_types`, `DEFTYPE_SUB/SOME` included, in 8.5 s.
- 1.0 `make check` and 2.0 `make check-2.0` pass, outputs unchanged.

## 2026-11-14: G5 done; G8 rest done (supersedes the G5/G8 deferrals above)

- G8, deferred tests: `crule` passes its deferred conclusion tests to
  `cprems` (cx `:dfr`); the `:check`-mode index search runs those that
  mention its variable inside the loop and takes the formals they compare
  with as extra parameters. `Heaptype_sub/rec-sub` compiles
  (`typeuse*[j]` in the conclusion).
- G5, pure tests: a disjunction whose branches bind different variables
  that occur nowhere else in the rule (counted occurrences, cx `:rule-occ`)
  compiles to `(or branch1 branch2)` with no bindings: `Instr_ok/array.new_data`,
  `array.init_data`.
- G5, finite existential: in `:check` mode, a disjunction `v = y1 ∨ v = y2`
  whose v is otherwise unbound and whose yk are of variant types with
  nullary cases only (`numtype`, `vectype`: values from the IL type
  definitions, cx `:typ-defs`) becomes a search over those values: all
  premises (with the disjunction, now a test) hold for some v.
  `Instr_ok/select-impl` compiles; `Instr_ok` 110/110.
- Effect, 3.0 D3 scope: dropped rules 5 → **2** (`Heaptype_sub/trans`,
  `Step_read/array.new_data-num`), errors 52 → 47; stubs 2. 2.0:
  `select-impl` compiles too; left `Instrs_ok/sub` (1 rule), 1 stub.
- The real 3.0 books certify through `2_3-validation_instructions` (41 s)
  with the new search functions (`HEAPTYPE_SUB/SOME`, `INSTR_OK/SOME`).
- 1.0 `make check` and 2.0 `make check-2.0` pass.
- Data: `data/probe-P4-G5G8-2026-11-14/`.
