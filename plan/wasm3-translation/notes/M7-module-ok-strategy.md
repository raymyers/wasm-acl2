# `Module_ok` for 3.0: why it is a stub, and the strategy

- Milestone: M7 (item 1: design session, how to translate `Module_ok`)
- Date: 2026-11-14
- Repo commit: 3220d7b plus this note's commit
- Status: final for the analysis and the experiment; the strategy is a
  **recommendation waiting for the user's decision**
- Feeds wasm3 plan: §3 (work list), §5 M7, §6 (config budget)

## Summary

`Module_ok` cannot be scheduled because its premises depend on each
other in two cycles through the context `C`. Measured: when `C` and `C'`
are given as inputs, the generated rule compiles with **0 errors**. So
the recommendation is the same split as for instruction typing: a short
hand-written function proposes the two contexts, and the generated rule
checks everything, including that the contexts are the right ones.

## Findings

### The two cycles

```
C' = {TYPES dt'*, GLOBALS gt_I*, FUNCS dt_I* dt*, REFS x*}
C  = C' ++ {TAGS jt_I* jt*, GLOBALS gt*, MEMS mt_I* mt*, TABLES tt_I* tt*,
            DATAS ok*, ELEMS rt*}
```

| Value | Comes from | Which needs |
|---|---|---|
| `dt*` (function types, in `C'`) | `(Func_ok: C |- func : dt)*` | `C`, which needs `C'` |
| `ok*`, `rt*` (in `C`) | `(Data_ok: C |- data : ok)*`, `(Elem_ok: C |- elem : rt)*` | `C` |

Everything else has an order: types, imports, the five projections of
the import types, `x*`, then `C'`, then tags, globals, memories, tables,
then `C`, then the checks.

Both cycles are only apparent. The three outputs can be read off the
syntax without checking anything: `Func_ok` returns `C.TYPES[x]`,
`Elem_ok` returns the element type written in the segment, `Data_ok`
returns `OK`. The declarative rule does not have to say so; an input and
output schedule does.

### Why the translator's present mechanisms do not reach it

- Variants on demand make a variant with other outputs. Here the inputs
  are the problem: `Func_ok` is needed before its input `C` exists.
- A generic solution needs two things the translator does not have:
  records whose fields are bound one at a time (`C.TYPES` is known long
  before `C`), and a variant that computes a rule's output from the
  conclusion alone, to be checked later. Both are real work, and in the
  D3 scope only this rule would use them.

### Experiment: the rule with its contexts given

New mode `(:given "v" ...)` in `compile.lisp`: as `:fun`, with the named
rule variables as extra inputs (function `R/W`). Declared for `Module_ok`
with `"C"` and `"C'"` in a scratch config:

| | Today | With `C`, `C'` given |
|---|---|---|
| `Module_ok` | stub, 29 errors in 6 kinds | **compiles, 0 errors** |
| Logged errors in the probe (D3 scope) | 49 | 21 |

(`$instantiate` becomes a stub in the experiment only because nothing
provides the one-argument `Module_ok` it calls.) With both contexts
bound, the two equations above compile to equality tests, by the same
code that turns any `x = e` with nothing unbound into a test. The
generated function was not run: no 3.0 module value exists to run it on
before M2.

## The strategy

| Option | Hand-written | Checked against the rule by | Verdict |
|---|---|---|---|
| Override, as in 1.0 | everything, about 110 lines (1.0: about 80 for 11 premise groups; 3.0 has 13 and 9 equations) | tests only | Works; nothing ties it to the rule |
| Staged modes in the translator | nothing | the translator | Field-wise records and conclusion-only variants, for one rule |
| **Proposer and checker** | a function computing `C'` and `C`, about 60 to 80 lines | the generated `MODULE_OK/W`, on every call | **Recommended** |

Line counts are estimates, not measurements.

### Proposer and checker in detail

- The translator compiles `Module_ok` in mode `(:given "C" "C'")` to
  `MODULE_OK/W (module C C')`. Done; in the tree, used by no config yet.
- A config entry supplies the entry function `MODULE_OK (module)`: it
  computes the two contexts and calls `MODULE_OK/W`. To compute them it
  calls generated functions (`TYPES_OK`, `IMPORT_OK`, the `$..xt`
  projections, `$funcidx_nonfuncs`, `TAG_OK`, `GLOBALS_OK`, `MEM_OK`,
  `TABLE_OK`) and reads `dt*`, `rt*` and `ok*` off the syntax.
- A wrong proposal makes `MODULE_OK/W` fail, because the rule's own
  equations for `C'` and `C` are tests in it. So a mistake in the
  hand-written part rejects valid modules, which the M7 tests against
  spec-test-3 show. It cannot accept an invalid one.

What is left to build (M7):

1. A config kind for "entry function plus given variables" (the present
   `:rel-override` replaces the whole relation). About 25 lines in
   `cform` and the config validation.
2. The proposer for 3.0.
3. The M7 behavioural exit: `assert_invalid` rejected, instantiated
   modules accepted.

The same could replace the 1.0 override (its 80 lines would shrink and
become checked). Optional; it changes 1.0 output.

## Open questions

- Decision: proposer and checker, or the plain override.
- Does `MODULE_OK/W` do the checks in a workable order? The schedule is
  the generic one; a slow order would show up only when run.

## Data

`data/module-M7-2026-11-14/`: `report-3.0-core-given.txt`, its rules
file, and `run.sh`.
