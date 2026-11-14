# Generic translator gaps (G1, G3-G5, G8, G9)

- Milestone: P4 (items: G1 function arguments by specialization; G3, G4
  iterated premises; G5 disjunctions; and the P1-found G8, G9)
- Date: 2026-11-14
- Repo commit: 3d79703 plus this note's commit
- Status: draft (G1 done; the rest open)
- Feeds wasm3 plan: scheme delta (function arguments), gap list, config budget
- Incorporated in wasm3 plan: no

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
- G3 (counter-only iterations, 1 rule), G4 (iterated `if` binding a list,
  1 rule), G5 (disjunctions, 3 rules), G8 (existential index, 2 rules),
  G9 (list-pattern binding order, 2 rules): open; see
  [P1-gap-list.md](P1-gap-list.md).
- 2.0 as a full target (builtins, oracle vectors, certification): needs the
  `rt/` package decision.

## Data

`data/probe-P4-G1-2026-11-14/`: `report-3.0.txt`, `report-3.0-core.txt`,
`rules-3.0-core.txt` (`make probe SPEC=3.0 [EXCLUDE='X.* 6.* 7.*']`).
