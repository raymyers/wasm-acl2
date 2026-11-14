# WASM 1.0 → ACL2 by Deterministic Translation

> **Goal**: Generate the WASM 1.0 ACL2 semantics *mechanically* from the
> SpecTec source, using the same parse → IL → backend pipeline that SpecTec's
> other backends (LaTeX, prose, interpreter) use. Re-running the generator on
> the same SpecTec input must produce byte-identical ACL2.
>
> **Source of truth**: [WASM 1.0 SpecTec](https://github.com/WebAssembly/spec/tree/main/specification/wasm-1.0)
> (10 files, 2353 lines). Same input as [WASM1_PLAN.md](WASM1_PLAN.md).
>
> **Relationship to WASM1_PLAN.md**: WASM1 was an *agentic* translation, with
> `execution.lisp` and `validation.lisp` written by hand or by an agent and
> shaped to fit the Kestrel skeleton. This plan is a separate, independent
> artifact. It shares **no code** with WASM1: it does not include
> `execution.lisp`, does not use the Kestrel `WASM` package, and lives in its
> own directory. The two sit side by side so we can compare them (see T9).

---

## 0. Feasibility spike (done 2026-11-13)

Before writing this plan I checked that the pipeline actually works with
stock, unmodified SpecTec.

| Check | Result |
|---|---|
| Build SpecTec (`spectec 0.5`) from `WebAssembly/spec@943c5df` (2026-11-10) | ✅ via Nix (`ocaml-ng.ocamlPackages_5_4`: ocaml, dune_3, menhir, menhirLib, zarith, findlib) + `../interpreter` copied in, as `spectec/Makefile` does |
| `spectec specification/wasm-1.0/*.spectec` (frontend + elaboration + IL validation) | ✅ passes |
| `spectec --ast --all-passes wasm-1.0/*.spectec` | ✅ 13,309 lines / 315 KB of IL as S-expressions |
| Can the ACL2 reader read that output? | ✅ Outside string literals it uses only `[A-Za-z0-9_()]` and whitespace. No `\|`, `#`, `;`, quotes, or backslashes. Identifiers are all in strings (`"Step_pure"`, `"%~>%"`, `"n'*"`) |
| Top-level IL forms | 88 `typ`, 110 `def`, 31 `rel`, 58 `gram`, 31 `rec` groups |
| Hand-supplied primitives (`hint(builtin)` in source) | 45, all in `3-numerics.spectec`: `$wrap__ $extend__ $trunc__ $demote__ $promote__ $convert__ $reinterpret__`, `$ibytes_ $fbytes_ $bytes_` and their inverses, `$inot_ … $ipopcnt_` (bitwise ops), every `$f*_` float op, and `$truncz` |
| `spectec --print-al --test-version 1` (the deterministic "algorithmic" form behind the interpreter) | ✅ 1,244 lines. No S-expr printer for it, though (see Strategy B) |

Sample of the IL we will consume (`rule Step_pure/select-true`):

```lisp
(rule
  "select-true"
  (exp "val_1" (var "val"))
  (exp "val_2" (var "val"))
  (exp "c" (var "val_" (exp (case "I32" (tup)))))
  "%~>%"
  (tup
    (list
      (sub (var "val") (var "admininstr") (var "val_1"))
      (sub (var "val") (var "admininstr") (var "val_2"))
      (case "CONST" (tup (case "I32" (tup)) (var "c")))
      (case "SELECT" (tup)))
    (list (sub (var "val") (var "admininstr") (var "val_1"))))
  (if (cmp ne bool (proj (uncase (var "c") "%") 0) (num (nat 0)))))
```

**Conclusion**: we do not need our own SpecTec parser, and we do not need to
fork SpecTec. Its existing `--ast` backend is the hand-off point.

---

## 1. Strategy

```
wasm-1.0/*.spectec
   │  spectec --ast --all-passes        (stock OCaml tool, pinned commit, built by Nix)
   ▼
translate/il/wasm-1.0.il.sexp           (checked in; the IL is the contract)
   │  il2acl2                            (our translator, written in ACL2 :program mode)
   │    + translate/builtins.lisp       (hand-written: the 45 builtins only)
   │    + translate/il2acl2-config.lsp  (small, reviewed table of per-rule overrides)
   ▼
translate/gen/*.lisp                    (generated ACL2 books; checked in; never hand-edited)
   │  cert.pl
   ▼
certified, executable WASM 1.0 semantics
```

### Why this shape

1. **Use SpecTec's frontend; don't write our own.** Parsing `.spectec` is
   the easy part. The hard part is elaboration (`frontend/elab.ml`): resolving
   mixfix notation, inferring the types of meta-variables, inserting subtype
   coercions, and expanding iterations (`x*`) into explicit `iter … dom`
   forms. Reimplementing that would be the riskiest work in the project and
   would add nothing.
2. **Use stock `--ast`; don't write an OCaml `backend-acl2` (for now).** The
   S-expression IL can be read directly by ACL2, so the translator can be
   written in Lisp and reason about Lisp. It also means no fork to rebase.
   An OCaml backend stays available as a fallback (Strategy C) if the
   S-expression dump turns out to drop something we need. The one known gap
   is that `--ast` does not print `hint(...)` annotations; we only need them to
   recognize builtins, and a clause-less `def` already tells us that.
3. **Translate from IL after `--all-passes`.** In this SpecTec version that
   means `totalize` and `sideconditions`. `totalize` turns partial functions
   into total functions returning an option. `sideconditions` makes implicit
   well-formedness premises explicit. Both remove guesswork from the
   translator.
4. **Write the translator in ACL2 `:program` mode.** It reads the IL with the
   ACL2 reader and writes books with ACL2's printer. That means one toolchain
   and one Nix closure, and the translator can later be moved into logic mode
   if we want to prove things about it. (An SBCL script would also work. The
   choice matters little as long as the output is deterministic.)
5. **Check in both the IL and the generated books.** Diffs then show exactly
   what changed when SpecTec or the translator changes. CI regenerates both and
   fails if the result differs from what is checked in. That CI check is how we
   enforce determinism.

### Rules of the game

- **No hand edits to `translate/gen/`.** Ever. If the output is wrong, fix the
  translator or the config.
- Hand-written ACL2 is limited to `builtins.lisp` (the 45 SpecTec builtins)
  and a thin runtime prelude. Everything else is generated.
- Every entry in `il2acl2-config.lsp` is a counted, named exception, keyed by
  SpecTec rule or def id and stating why it exists. The number of entries is a
  headline metric (T9), and the target is to keep it as low as possible.
- **Pinned inputs.** The SpecTec commit is pinned in the flake. Bumping it
  should produce a reviewable IL diff and a reviewable ACL2 diff.

### Strategies considered

| | Strategy | Verdict |
|---|---|---|
| **A** | Stock `spectec --ast` IL → ACL2 translator | **Primary.** Shown to work in the spike |
| B | `il2al` AL (algorithmic language) → ACL2 | **Fallback for execution only.** AL is already deterministic step code (`Pop`/`Push`/`If`), so it is easy to make executable. But it is the interpreter's view of the spec, not the relations themselves, and it needs a new S-expr printer (~200 lines of OCaml, possibly upstreamable). Use it if mode analysis of `Step` (T4) gets stuck |
| C | `backend-acl2` written in OCaml inside SpecTec, the way Coq/Isabelle-style backends are done | Fallback if the `--ast` dump turns out to lose information. Costs a fork |
| D | Our own `.spectec` parser | Rejected: we would have to reimplement elaboration |

---

## 2. Translation scheme (the contract between IL and ACL2)

Everything here is a pure function of the IL. Where the IL leaves a choice
open, the rule for making that choice is written down here, not left to
whoever happens to implement it.

### 2.1 Package and naming

- New package **`W1T`** (defined in `translate/package.lsp`). It does **not**
  use `kestrel/wasm/portcullis`, which avoids symbol clashes with WASM1's
  `WASM::instrp` and friends.
- Name mangling is a fixed, documented, injective function. Examples:
  `$iadd_` → `W1T::$IADD_`; syntax `instr` → recognizer `W1T::INSTR-P`;
  relation `Step_pure` → `W1T::STEP_PURE`; rule `Step_pure/select-true` →
  `W1T::STEP_PURE/SELECT-TRUE`. Case-folding collisions (`N` vs `n` are both
  types in `0-aux`) are resolved by a deterministic suffix, and the mangle
  table is emitted as a comment block at the top of each generated book.

### 2.2 Values: one untyped universe

SpecTec types include **families indexed by values** (`iN(N)`,
`val_(valtype)`, `fN(N)`). FTY `deftypes` cannot express those, so we do not
use FTY. All object-level values are plain ACL2 objects, and each type is
represented only by a generated recognizer.

| IL | ACL2 encoding |
|---|---|
| `nat` / `int` / `rat` | ACL2 integer or rational |
| `bool` | `t` / `nil` |
| `text` | string |
| `(case MIXOP (tup a₁ … aₙ))` | `(:TAG a₁ … aₙ)`, where the keyword `:TAG` is derived from the atoms of the mixop (`"CONST"` → `:CONST`, `"LABEL_%{%}%"` → `:LABEL_`, `"%;%"` → `:SEMI`) |
| A variant with a single atom-free case (`"%"`), e.g. `iN` | **elided**: encoded as its payload (so an `i32` is just a natural number) |
| `tup` | list |
| `iter … list` / `list1` / `listn` | list |
| `iter … opt` | `nil` or `(list x)` |
| record (`str`) | `(:%REC (:FIELD . v) …)`, fields in declaration order. The `:%REC` marker is needed because `comp` (`++`) has no type info and must tell records from lists of tagged values |
| `sub e t₁ t₂` | the same object (variants share tags under subtyping) |
| `cvt` (nat↔int↔rat) | identity |

Recognizers are generated for every `typ`. Family recognizers take the index
as an extra argument (`(IN-P N x)`, `(VAL_-P vt x)`). Families defined
case-by-case with `inst` become a `cond` on the index.

### 2.3 Functions (`def`)

- Each `def` becomes a `defun`. Each `rec` group becomes a `mutual-recursion`.
- Clauses are tried **in order**. Argument patterns compile to `case-match`
  plus explicit equality checks. `if` premises become conjuncts. `let`
  premises become `let*` bindings. `else` becomes the final `t` branch.
- After `totalize`, every partial function returns an option, so falling
  through every clause yields `nil`. That makes it a total function in ACL2.
- `iter e (dom x xs)…` becomes a lifted auxiliary recursive function
  `F/ITERk` (free variables passed as extra arguments). Trivial maps (`x` over
  `xs`) simplify to `xs`. Not `loop$`: it needs badges/warrants even in
  `:program` mode (found in T2).
- Clauses compile to nested `and`/`let*` returning `(list result)` or `nil`;
  the def body chains them, so there is no exponential duplication.
- Premises are **scheduled**: SpecTec lists them out of dependency order
  (`$allocfunc` uses `x` before the premise that binds it), so the compiler
  always takes the first premise that compiles under the current bindings.
  `if a = e` with `a` unbound is a binding; `if a /\ b` is split in two.
- A form hitting an unsupported construct becomes an explicit **stub**
  (body signals an error) listed in the generated header.
- Every event is wrapped in `(%try-logic …)`: logic mode if ACL2 admits it
  (default measures, guards not verified), else `:program`.
- Clause-less `def`s are **builtins**. The generator emits nothing for them and
  checks that `builtins.lisp` defines each one with the expected arity. Any
  missing builtin is a hard error.

### 2.4 Builtins (`translate/builtins.lisp`, hand-written)

These are the 45 `hint(builtin)` functions, implemented on top of
`kestrel/bv` and `kestrel/floats/ieee-floats-as-bvs`. The float
representation must match the spec's `fN` syntax (`POS`/`NEG` with
`NORM m exp | SUBNORM m | INF | NAN m`). That fixes our encoding as
`(:POS (:NORM m e))` and so on; it is **not** WASM1's encoding with
`:f32.+0` atoms. Writing these fresh, without copying from WASM1, is
deliberate: it keeps the comparison in T9 honest.

### 2.5 Relations (`rel`): mode analysis

ACL2 has no inductive predicates, so each relation gets a **mode**: which
positions are inputs and which are outputs. The translator works the modes out
from the rule shapes, and the config can override them.

| Relation(s) | Mode | Generated form |
|---|---|---|
| `Step_pure`, `Step_read`, `Step` | config → config | `(STEP cfg)` returns the **list** of successor configs (one per applicable rule; WASM determinism means at most one in practice). Each rule becomes its own function `STEP/<rule>`, combined by `append` in rule order |
| `Steps`, `Eval_expr` | config →* config | `(STEPS fuel cfg)`: clocked iteration, stops on a terminal config or `TRAP` |
| `Instr_ok`, `Instrs_ok`, … (typing) | all positions as inputs | `(INSTR_OK-P C instr ft)`: a checker. Types that occur only in the conclusion (`unreachable : t₁* → t₂*`) are universally satisfiable, so checking them is decidable |
| `*_ok` with output types (`Module_ok`, `Func_ok`) | inputs → output | the translator infers output-mode functions where every output variable is fixed by matching or by a `let`. If it cannot, it falls back to a checker plus a config hint |

**Known hard case: sequence splitting.**
`rule Step/ctxt-instrs: z; val* admininstr* admininstr_1* ~> …` matches the
instruction list against a concatenation of three unknown sublists. Two ways
to handle it:

- Generic: enumerate all splits (O(n²)) and keep the first one whose premise
  succeeds. This is correct but slow.
- Config strategy `:values-prefix-then-head`: `val*` is the longest prefix
  of values, `admininstr*` is a single instruction, and `admininstr_1*` is
  the rest. This is what `il2al` does implicitly. The config entry records the
  justification, and a generated `defthm` (T8) proves that the strategy finds a
  split whenever the generic enumeration does.

This is the main technical risk. If it blocks progress, the Strategy B
fallback (AL) applies to `Step` alone.

### 2.6 Grammars (`gram`, `A-binary.spectec`)

There are 58 binary-format productions. Translating them into a byte-list
parser (`(PARSE-MODULE bytes)` returning a module or `nil`) gives a binary
decoder generated straight from the spec. That replaces WASM1's
`wasm2acl2.js` and Kestrel's `parse-binary.lisp`. It is a stretch goal (T7).

---

## 3. Directory layout

```
translate/                     # fully independent of the WASM1 tree
  Makefile                     # il / gen / cert / check-determinism / test
  package.lsp  cert.acl2
  il/wasm-1.0.il.sexp          # spectec --ast --all-passes output (checked in)
  il/SPECTEC_REV               # pinned commit + exact command line
  il2acl2/                     # the translator (ACL2 :program mode)
    read.lisp  schema.lisp  mangle.lisp  top.lisp (T1 checks)
    compile.lisp (exp/pattern/premise/type/def compiler)  emit.lisp  run.lsp
  il2acl2-config.lsp           # counted overrides (modes, split strategies, measures)
  gen/                         # GENERATED — do not edit
    package.lsp  portcullis.*  # W1T package (imports computed from generated names)
    wasm1.lisp                 # all types + defs in IL order (types call defs such
                               # as $size and $utf8, so they cannot be split by kind)
  rt/                          # hand-written: prelude.lisp (records), builtins.lisp
  tests/                       # assert-event tests over gen/
  compare/                     # T9: books that include BOTH trees (the only place they meet)
```

`flake.nix` gains new outputs: `spectec` (pinned), `wasm1-translated`, and a
`checks.translate-determinism` check. The existing `wasm-acl2` output is
left as it is.

---

## 4. Milestones

### T0: Toolchain and pinned IL ✅ (2026-11-13)
- [x] Nix derivation for SpecTec at the pinned rev (recipe from the spike:
      ocaml 5.4 + dune + menhir + menhirLib + zarith, `interpreter/` copied to
      `src/backend-interpreter/reference-interpreter`)
- [x] `make -C translate il` regenerates `il/wasm-1.0.il.sexp`; check it in
- [x] CI: regenerating gives byte-identical output. `nix flake check` runs
      `checks.translate-il` (two runs agree and both equal the checked-in IL);
      `make -C translate check-il` does the same locally

**Exit**: `nix build .#spectec` works, and the IL is checked in and reproducible.

### T1: IL reader and schema ✅ (2026-11-13)
- [x] `read.lisp`: read every top-level form of the `.sexp` with the ACL2 reader
- [x] `schema.lisp`: a recognizer for the IL S-expr grammar, mirroring
      `spectec/src/il/ast.ml` and `backend-ast/print.ml`. It rejects any form
      it does not know, so a SpecTec upgrade that changes the IL fails loudly
- [x] `mangle.lisp`: injective naming, plus a collision report
- [x] Dependency order: the IL is already topologically sorted and `rec` groups
      are explicit. Assert this; don't recompute it

**Exit**: all 318 top-level forms parse and pass the schema check.

**Result** (`make -C translate test` certifies `tests/t1-il.lisp`): 318 top-level
forms, 0 schema or order errors. Counting `rec` members (the §0 spike
counted top-level forms only): 90 typ, 132 def, 36 rel, 61 gram; 137 rules,
359 variables, 118 constructor atoms. Mangling is injective and needs only 13
suffixes (`t` → `T^R`, `state` → `STATE^R`, type `N` → `N^U-P` beside `n`, …);
no two mixops share a tag. Notes for T2: mangled names that clash with
`*acl2-exports*` are `STATE-P` (fn) and `LEN LOCAL TABLE TYPE CHAR W` (vars),
so the generated `W1T` package must leave those out of its imports. Unnamed
rules (`rule Limits_ok:`) mangle to `LIMITS_OK/`.

### T2: Syntax → recognizers (`gen/wasm1.lisp`) ✅ (2026-11-13)
- [x] All 90 `typ` definitions: variants, records, aliases, and indexed families
      (families take the index as extra arguments: `(VAL_-P x vt)`; inst
      clauses match the index by pattern; type parameters are unchecked)
- [x] Newtype elision rule (§2.2) applied uniformly (atom-free mixop ⇒ payload;
      checked: such a case is always the only case of its variant)
- [x] Certifies; every recognizer is in logic mode (`%try-logic`). Guard
      verification is deferred to T8. (Correction, found in T4: the mode
      count first reported here, "0 `:program` fallbacks", came from a buggy
      script; see the T4 result for the real numbers.)

**Exit**: `(INSTR-P '(:CONST (:I32) 7))` holds, and both books certify.

**Result**: `make -C translate check` passes: `check-gen` (two fresh runs are
byte-identical to the checked-in `gen/`) and `tests/sem/t2-syntax.lisp`
(bytes, uN/sN, floats incl. NaN payload and exponent bounds, records, names via
`$utf8`, `val_` family, instructions incl. the `STORE` `Inn?` premise, `$size`,
`$signed_`). Note `loadop_` is mixop `%_%`, so its tag is `:_`: `(:_ 8 (:U))`.
The compiler also already handles all def clauses (T3, first item); remaining
compile errors are confined to two stubs, `$instantiate` and `$allocmodule`
(relation premises, T5). One config override so far: `$utf8` (its multi-byte
clauses are defined by an arithmetic equation on the result).

### T3: Functions and builtins (`gen/wasm1.lisp`, `rt/builtins.lisp`) ✅ (2026-11-13)
- [x] Clause compilation (§2.3): patterns, `if`/`let`/`else` premises,
      lifted aux functions for iteration (done in T2)
- [x] The 45 builtins, in pure ACL2 (no community books; exact rational
      arithmetic + one round-to-nearest-even; sqrt via integer sqrt + sticky
      bit). Simpler than Kestrel bv/IEEE and keeps `rt/` independent of WASM1.
      Float ops return one result; for NaN results the canonical NaN
- [x] `%try-logic` admits each event in logic mode when possible, else
      `:program`; the count is recorded (T4 result: 312 logic / 20 `:program`)
- [x] Unit tests: `$iadd_`, `$idiv_` (trap cases via option), `$signed_`, `$fadd_` NaN/Inf/±0
      (`tests/sem/t3-units.lisp`)

**Exit**: every generated `def` evaluates, and numerics tests pass.

**Result**: `tests/sem/t3-numerics.lisp` runs **8015/8015** oracle vectors
(`make vectors`: Node/V8 executes every WASM 1.0 numeric instruction, i32/i64/
f32/f64 incl. all conversions, on edge cases + seeded random bit patterns;
NaN results compared as "is NaN", reinterprets bit-exact) through the
*generated* dispatchers `$binop_ $unop_ $testop_ $relop_ $cvtop__` and the
builtins. Every generated def evaluates except the two module stubs
(`$instantiate`, `$allocmodule`, T5).

### T4: Reduction relations (`gen/wasm1.lisp`) ✅ (2026-11-13)
- [x] Mode analysis (§2.5) for `Step_pure`, `Step_read`, `Step`: every
      relation is first compiled `:fun` (last component = output; returns
      `(list out)` or `nil`, first applicable rule wins), retried as `:check`
      if that fails, and stubbed if both fail. `Steps` is recognised by its
      refl/trans shape (`:closure`)
- [x] `ctxt-label`, `ctxt-frame`, `ctxt-instrs` (the split strategy). Generic
      split search for `cat` patterns with no fixed-length side (the rest of
      the rule runs inside a lambda-lifted search function, so later
      failures backtrack). `ctxt-instrs` uses the config `:redex` strategy
- [x] `STEPS` with fuel: `STEPS(x)` iterates `STEP` to a normal form, at most
      `(%FUEL)` = 10^6 steps
- [x] Hand-built configs run factorial and fibonacci to completion

**Exit**: all 58 reduction rules are translated and the M2-style control-flow programs run.
**Go/no-go**: if the `ctxt-instrs` split cannot be handled without an
unreasonable amount of config, switch `Step` to Strategy B (AL).

**Result**: go: no Strategy B needed. `Step_pure`, `Step_read`, `Step`,
`Steps` and `Eval_expr` translate with no stubs. `tests/sem/t4-reduction.lisp`
(16 checks) runs arithmetic, wraparound, div-by-zero trap, select, block/br,
nested br, if/else, factorial(5)=120, factorial(10), fibonacci(10)=55, a call
through the store, return through labels, memory store/load (incl. a full
64 KiB page with `memory.size`), and an out-of-bounds trap.
New generic machinery: linear-arithmetic patterns (`BR(l+1)`,
`(n·64)·Ki = |bytes|`), `c <- e` bindings (first element), disjunctive
premises that bind (`block`'s `(t?=ε ∧ n=0) ∨ (t?≠ε ∧ n=1)`), elided-newtype
projections in patterns, premise scheduling that runs cheap tests before
relation calls. Config now has 3 entries: `$utf8` override, the
`ctxt-instrs` `:redex` split, and the 4 `hint(inverse)` pairs (`--ast` drops
hints) used by the load rules. Modes: 312 generated functions in logic mode,
20 in `:program` (`$concat_`, the `STEP` group and its callers `STEPS`,
`EVAL_EXPR`, alloc/init defs): termination is T8. Remaining stubs: the
typing relations (T6), `Externaddr_ok`, `Module_ok`, `$instantiate` (T5).
Bug found and fixed on the way: a `:fun` relation must return `(list out)`,
since `NOP ~> ε` has an empty output. Note: `:program` code runs without
safety checks, so feeding it an ill-formed configuration (e.g. a module
instance with no memory address) can crash SBCL instead of failing cleanly.

### T5: Module instantiation and invocation (`gen/module.lisp`)
- [ ] `9-module.spectec`: alloc*, instantiate, invoke (5 rules plus defs)
- [ ] A test harness that builds IL-encoded modules from the existing
      `tests/oracle/*.wat` corpus. The *inputs* are shared; no WASM1 code is used
- [ ] Results checked against Node.js, as the existing oracle does

**Exit**: the oracle `.wat` programs run through instantiate + invoke and agree with Node.

**Status (2026-11-13): blocked on T6.** `$invoke` and the alloc/init defs
translate (except `$allocmodule`), and T4 already runs calls through a
hand-built store. But `$instantiate` has the premise
`Module_ok: |- module : xt_I* -> xt_E*`, where the module type is an *output*,
so T5 cannot be completed as specified until `Module_ok` exists in an
inference mode (T6).

### T6: Typing (`gen/wasm1.lisp`) 🔶 Partial (instruction typing done; `Module_ok` blocked)
- [~] All 76 typing rules as checkers or output-mode functions (§2.5).
      Every typing relation translates except `Module_ok` and
      `Externaddr_ok`. Instruction typing uses option 2 below, now
      implemented: a **multi-mode** translation. `Instr_ok`/`Instrs_ok` get a check
      variant `R` (all components given) and a split variant `R/SPLIT`
      (output = second half of the last component `t_1* -> t_2*`). Premise
      calls use the check variant when everything is bound, so polymorphic
      instructions type in checking positions (end of a block/loop/function
      body). Only `unreachable`, `br`, `br_table`, `return` are dropped, and
      only from the split variants (listed in the generated header). So the
      checker is sound and incomplete only for dead code after a polymorphic
      instruction in the middle of a sequence. Recursion uses the
      lexicographic check (instruction size, total size) from config
      `:decreasing`, which also removes the `seq`/`frame` cycles.
      `tests/sem/t6-typing.lisp` (16 checks): straight-line code, ill-typed
      underflow/mismatch/wrong result, locals, `br` at the end of a block,
      label out of range, `unreachable` at an arbitrary type, `Expr_ok`, and
      `Func_ok` on factorial plus an ill-typed variant. The typing clique (15 functions) is
      still `:program`: termination of its list-split searches needs more
      measure work
- [ ] `Module_ok` on the oracle corpus: blocked by the context cycle below

**Exit**: every oracle module validates, and the deliberately ill-typed
negative tests are rejected.

**Status (2026-11-13)**: the generic mode analysis translates the
*non-instruction* typing relations: `Limits_ok`, `Functype_ok`,
`Globaltype_ok`, `Tabletype_ok`, `Memtype_ok`, `Externtype_ok`, the `*_sub`
relations, `Expr_ok`, `Instr_const`/`Expr_const`, `Type_ok`, `Func_ok`,
`Global_ok`, `Table_ok`, `Mem_ok`, `Data_ok`, `Start_ok`, `Import_ok`,
`Export_ok`, `Externidx_ok` (several of these call the stubs below, so they
only work as far as those do). Stubs: `Instr_ok`, `Instrs_ok`, `Elem_ok`,
`Module_ok`, `Externaddr_ok`.

**Blocker**: the instruction typing rules are declarative in a way that no
input/output mode makes deterministic:
- `Instrs_ok/seq` splits the sequence at an unknown point *and* introduces an
  existential intermediate stack `t_2*`;
- `Instrs_ok/frame` adds an arbitrary common stack prefix `t*`;
- `unreachable`, `br`, `return` (and `br_table`) have unconstrained output
  stacks (`t_1* -> t_2*`), so in "stack in, stack out" mode their output is
  not computable, and in checking mode the intermediate stacks are not known.

A complete checker needs bidirectional mode inference with stack
polymorphism, i.e. a validation *algorithm*.

`Module_ok` has a second, independent problem: a cyclic dependency. The
context `C = {TYPES ft'*, FUNCS ift* ft*, ...}` contains `ft*`, and `ft*` is
the *output* of the premises `(Func_ok: C |- func : ft)*`, which take `C` as
input. Mode analysis cannot schedule this. Breaking the cycle needs the
insight that `Func_ok`'s output `C.TYPES[x]` depends only on `C.TYPES`, i.e.
partial evaluation or laziness, not a mode. SpecTec does not derive one
either: the AL (`--print-al`, Strategy B) calls `$Module_ok` as an opaque
function, and SpecTec's interpreter backend validates with the hand-written
OCaml reference validator. Options, none taken yet (each is a decision for
the project, not a mechanical next step):
1. Hand-write `Instr_ok`/`Instrs_ok` as a config override, i.e. a validation
   algorithm proved equivalent to the rules later. Large, and against the
   "only builtins are hand-written" rule.
2. A sound-but-incomplete generic checker: a multi-mode compilation (stack in →
   stack out, plus checking mode for the last instruction of a sequence),
   with a cycle guard for `frame`. It would reject valid code that needs stack
   polymorphism in the middle of a sequence (dead code after `br`). Rules
   that cannot be compiled in a mode would be listed as incomplete.
3. Skip validation for execution: run modules via `$allocmodule` + `$invoke`
   without `$instantiate`'s `Module_ok` premise. That is not the spec's
   instantiation, so it would be a test-only path.

### T7: Binary format, and conformance (stretch) 🔶 Partial
- [x] Grammar → parser for `A-binary.spectec` (§2.6): every grammar becomes
      `GRAM/G(bytes, params)` → `(list value rest)` or `nil` (ordered choice,
      greedy iteration that stops on no progress, per-element bindings
      collected as output lists). Grammars with grammar parameters (`Blist`,
      `Bsection_`) are inlined at each use. Needed one more generic feature,
      list-iterated premises with outputs (which also un-stubbed `Elem_ok`
      and `$instantiate`'s own body)
- [ ] `.wasm` bytes → `PARSE-MODULE` → instantiate → invoke, with no JS
      involved. Parsing is done (`GRAM/BMODULE`); instantiate is blocked on
      `Module_ok` (T6)
- [ ] Run a subset of `spectec/test-interpreter/spec-test-1` (the WASM 1.0 `.wast` suite).
      Blocked on instantiate as well

**Exit**: N of M spec-test-1 assertions pass (record N/M).

**Result (parser)**: `tests/sem/t7-binary.lisp`: **13/13** modules of the
shared oracle corpus (`make corpus`: `wat2wasm` of `tests/oracle/*.wat`)
parse completely with the generated `GRAM/BMODULE`, and their exports
(names, kinds) equal V8's `WebAssembly.Module.exports`.
New config entries (now 6): `:sized` and `:il-patch` (below), plus
`inv_utf8` (a hand-written UTF-8 decoder beside the `$utf8` override, used
by `Bname`). Two problems in the SpecTec source / IL, found by translating
faithfully:
- `A-binary.spectec` writes the module header as `0x00 0x61 0x73 0x6D 1:Bu32`.
  The version is the fixed 4 bytes `01 00 00 00`, not a LEB128 u32, so read
  literally no real `.wasm` parses. Fixed by a counted `:il-patch` on `Bmodule`.
- `Bsection_`/`Bcode` say `len = ||BX||` (byte size of the match), but the
  IL has `len = 0`: elaboration loses `||·||`. Handled by `:sized`: the item
  after `len` is parsed from exactly `len` bytes.

### T8: Logic mode, guards, reasoning 🔶 Partial
- [x] Move generated functions from `:program` to logic mode: **all 462**.
      Termination comes from generic translator mechanisms (no config
      measures): (1) `mutual-recursion` holds only the functions that really
      recurse (aux functions that never call back are emitted first);
      (2) parsers carry always-true progress checks `|rest| <= |input|` after
      every sub-parse, with measures 2|S| (grammar) and 2|S|+1 (its loops);
      (3) a second logic attempt proves termination in the `ground-zero`
      theory, so large callees are not opened; (4) inside a recursive
      relation group every recursive premise call is preceded by a generated
      size check (`%SIZE` of the callee inputs < of the own inputs, always
      true for WASM `Step`), and relations get measure ω·(1+size) and their
      split searches ω·size + counter (`%OM`, with two prelude lemmas);
      (5) per-formal measure attempts for single recursive defuns
      (`$allocfuncs` recurses on its 3rd argument)
- [x] Guard verification wherever it is achievable: each event is followed
      by `(%try-guards f)`, a step-bounded `verify-guards` that falls back
      silently. Result: **164** functions guard-verified
      (`:common-lisp-compliant`), 298 logic-only, 0 `:program`, of 462
- [x] Generated or hand-written proofs over the generated defs: the analogs of
      WASM1's `add-correct` and `div-by-zero-traps`. `tests/sem/t8-proofs.lisp`,
      all for all inputs: `$idiv_`/`$irem_` by zero have no result; the
      generated `STEP_PURE` reduces `i32.const a; i32.const b; i32.add` to
      `i32.const (a+b mod 2^32)`, traps `div_u` by zero, and selects
      correctly. Proofs expand the lifted search functions by name, collected
      from `gen/wasm1.lisp`. Also `compare/c2-int-equiv.lisp` (T9)
- [ ] Prove the split strategy in §2.5 complete (now possible: `STEP` is in logic mode)

**Exit**: the share of the generated semantics in logic mode is recorded and
increasing; the first `run`-level theorem is proved. *Status*: **met**. Share
462/462 in logic mode. `tests/sem/t8-run.lisp` proves, for all 32-bit a, b,
that the generated `STEPS` runs `i32.const a; i32.const b; i32.add` to
`i32.const ((a+b) mod 2^32)`, via the lemmas that one `STEP` adds, a single value is
stuck, and the opening lemmas of the generated fuel loop.

### T9: Side-by-side comparison with WASM1 (`translate/compare/`) 🔶 Partial
- [~] **Differential testing**: run the same oracle corpus through both
      semantics and diff the results. *Numeric level done*
      (`compare/c1-numerics-diff.lisp`, `make -C translate compare`): WASM1
      runs the same 8015 V8 vectors as single-instruction programs. The
      module-level corpus waits on T5
- [~] **Equivalence theorems** for numerics, e.g.
      `(equal (W1T::$IADD_ 32 a b) (WASM::...i32.add... a b))`, plus the
      float ops, modulo the encoding map between the two float representations.
      *Integer part done* (`compare/c2-int-equiv.lisp`): 12 theorems, for all
      inputs, that the generated `$binop_` equals the BV expressions WASM1's
      `execute-i32.*`/`i64.*` use (add, sub, mul, and, or, xor). Float
      equivalence is **false** (see below), so it is not attempted
- [x] Metrics table (2026-11-13):

| Metric | WASM1 (agentic) | W1T (translated) |
|---|---|---|
| Hand-written ACL2 lines | ~4,300 (`execution.lisp` 3717 + `validation.lisp` 594) | 390 (`rt/builtins.lisp` 299 + `rt/prelude.lisp` 91) + 16-line config |
| Translator lines | n/a | ~2,550 (`il2acl2/`), WASM-agnostic |
| Generated lines | 0 | 10,396 (`gen/wasm1.lisp`, 310 events) |
| Config overrides | n/a | 7 (`$utf8`, `ctxt-instrs` split, `hint(inverse)` pairs, `:il-patch` version bug, `:sized` section lengths, `:decreasing` typing order) |
| Execution rules covered | 170/170 instructions | all 58 reduction rules (Step_pure/read/Step) |
| Validation | hand-written type checker | generated: all typing relations except `Module_ok`, `Externaddr_ok`; instruction typing via multi-mode (sound, incomplete only for mid-sequence dead code) |
| Spec rules traceable to ACL2 defs | informal | 1:1 by name (`STEP_PURE/BINOP-VAL` ...) |
| Logic-mode share | 100% | **462 / 462** functions (incl. parsers); 164 guard-verified |
| Numeric oracle agreement (8015 V8 vectors) | **6975** (all integer ops agree; floats disagree) | **8015** |
| Effort to absorb a SpecTec update | manual | regenerate + review diff (`make check`) |

**Finding from the differential test**: WASM1's float arithmetic is exact
rational arithmetic with no rounding to f32/f64 precision, e.g.
`f32.add 1.0 4294967296.0` gives `(:F32.CONST 4294967297)` where IEEE (V8, W1T)
gives 4294967296. Every float op that can round disagrees (add/sub/mul/div
agree only on ~12-14/78 vectors; also sqrt, nearest/trunc/floor/ceil,
demote, the int→float conversions, and some float→int truncations and
reinterprets). All integer ops agree on all vectors.

---

## 5. Risks

| Risk | Mitigation |
|---|---|
| Sequence-split matching in `Step/ctxt-instrs` is slow or ambiguous | Config split strategy with a completeness proof (§2.5); Strategy B for `Step` |
| `--ast` output format changes between SpecTec versions | Pinned rev; strict schema check in T1; IL diff reviewed whenever the pin is bumped |
| `--ast` leaves out hints we turn out to need | Clause-less `def` = builtin covers what we know of. Otherwise a small upstream patch to print hints, or Strategy C |
| Termination of generated mutual recursion | Start in `:program` mode; measures go in config, counted |
| Indexed families make guard verification awkward | Untyped universe plus recognizers. Guards are `t` at first, then tightened |
| Spec quirks fixed upstream later (e.g. hand-written special cases in `il2al/manual.ml`) | Check `manual.ml` for anything WASM 1.0 relies on, and record each item in config with a reference |

---

## 6. Reproducing the spike

```bash
git clone --depth 1 --filter=blob:none --sparse https://github.com/WebAssembly/spec.git
cd spec && git sparse-checkout set spectec specification/wasm-1.0 interpreter
cd spectec
rm -rf src/backend-interpreter/reference-interpreter
cp -R ../interpreter src/backend-interpreter/reference-interpreter
rm -r src/backend-interpreter/reference-interpreter/{dune-project,jslib}
cp src/backend-interpreter/dune-ref-interp src/backend-interpreter/reference-interpreter/dune
nix-shell -I nixpkgs=flake:nixpkgs \
  -p 'with ocaml-ng.ocamlPackages_5_4; [ocaml dune_3 menhir menhirLib zarith findlib]' \
  --run 'dune build src/exe-spectec/main.exe'
B=_build/default/src/exe-spectec/main.exe
$B ../specification/wasm-1.0/*.spectec                                   # check
$B --ast --all-passes ../specification/wasm-1.0/*.spectec > wasm-1.0.il.sexp
$B --print-al --test-version 1 ../specification/wasm-1.0/*.spectec      # AL view (Strategy B)
```
