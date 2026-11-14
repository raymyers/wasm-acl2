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
| record (`str`) | alist in field-declaration order: `((:FIELD . v) …)` |
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
- `iter e (dom x xs)…` becomes `(loop$ for x in xs [as y in ys] collect e)`.
  Trivial maps (`x` over `xs`) simplify to `xs`.
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
    read.lisp  schema.lisp  mangle.lisp  types.lisp
    defs.lisp  rels.lisp  gram.lisp  emit.lisp  main.lisp
  il2acl2-config.lsp           # counted overrides (modes, split strategies, measures)
  builtins.lisp                # 45 hand-written builtins
  prelude.lisp                 # tiny runtime helpers (option, list utilities)
  gen/                         # GENERATED — do not edit
    syntax.lisp  numerics.lisp  runtime.lisp  typing.lisp
    reduction.lisp  module.lisp  binary.lisp  top.lisp
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

### T1: IL reader and schema
- [ ] `read.lisp`: read every top-level form of the `.sexp` with the ACL2 reader
- [ ] `schema.lisp`: a recognizer for the IL S-expr grammar, mirroring
      `spectec/src/il/ast.ml` and `backend-ast/print.ml`. It rejects any form
      it does not know, so a SpecTec upgrade that changes the IL fails loudly
- [ ] `mangle.lisp`: injective naming, plus a collision report
- [ ] Dependency order: the IL is already topologically sorted and `rec` groups
      are explicit. Assert this; don't recompute it

**Exit**: all 318 top-level forms parse and pass the schema check.

### T2: Syntax → recognizers (`gen/syntax.lisp`, `gen/runtime.lisp`)
- [ ] 88 `typ` definitions: variants, records, aliases, and indexed families
- [ ] Newtype elision rule (§2.2) applied uniformly
- [ ] Certifies in logic mode, with guards (recognizers are simple)

**Exit**: `(INSTR-P '(:CONST (:I32) 7))` holds, and both books certify.

### T3: Functions and builtins (`gen/numerics.lisp`, `builtins.lisp`)
- [ ] Clause compilation (§2.3): patterns, `if`/`let`/`else` premises, `loop$` for iteration
- [ ] The 45 builtins on Kestrel bv and IEEE libraries
- [ ] Start in `:program` mode for everything that does not get through admission;
      record the count
- [ ] Unit tests: `$iadd_`, `$idiv_` (trap cases via option), `$signed_`, `$fadd_` NaN/Inf/±0

**Exit**: every generated `def` evaluates, and numerics tests pass.

### T4: Reduction relations (`gen/reduction.lisp`)
- [ ] Mode analysis (§2.5) for `Step_pure`, `Step_read`, `Step`
- [ ] `ctxt-label`, `ctxt-frame`, `ctxt-instrs` (the split strategy)
- [ ] `STEPS` with fuel
- [ ] Hand-built configs run factorial and fibonacci to completion

**Exit**: all 58 reduction rules are translated and the M2-style control-flow programs run.
**Go/no-go**: if the `ctxt-instrs` split cannot be handled without an
unreasonable amount of config, switch `Step` to Strategy B (AL).

### T5: Module instantiation and invocation (`gen/module.lisp`)
- [ ] `9-module.spectec`: alloc*, instantiate, invoke (5 rules plus defs)
- [ ] A test harness that builds IL-encoded modules from the existing
      `tests/oracle/*.wat` corpus. The *inputs* are shared; no WASM1 code is used
- [ ] Results checked against Node.js, as the existing oracle does

**Exit**: the oracle `.wat` programs run through instantiate + invoke and agree with Node.

### T6: Typing (`gen/typing.lisp`)
- [ ] All 76 typing rules as checkers or output-mode functions (§2.5)
- [ ] `Module_ok` on the oracle corpus

**Exit**: every oracle module validates, and the deliberately ill-typed
negative tests are rejected.

### T7: Binary format, and conformance (stretch)
- [ ] Grammar → parser for `A-binary.spectec` (§2.6)
- [ ] `.wasm` bytes → `PARSE-MODULE` → instantiate → invoke, with no JS involved
- [ ] Run a subset of `spectec/test-interpreter/spec-test-1` (the WASM 1.0 `.wast` suite)

**Exit**: N of M spec-test-1 assertions pass (record N/M).

### T8: Logic mode, guards, reasoning
- [ ] Move generated functions from `:program` to logic mode. Termination comes
      from `acl2-count` by default; measures go in config when that fails
- [ ] Guard verification wherever it is achievable
- [ ] Generated or hand-written proofs over the generated defs: the analogs of
      WASM1's `add-correct` and `div-by-zero-traps`
- [ ] Prove the split strategy in §2.5 complete

**Exit**: the share of the generated semantics in logic mode is recorded and
increasing; the first `run`-level theorem is proved.

### T9: Side-by-side comparison with WASM1 (`translate/compare/`)
- [ ] **Differential testing**: run the same oracle corpus through both
      semantics and diff the results
- [ ] **Equivalence theorems** for numerics, e.g.
      `(equal (W1T::$IADD_ 32 a b) (WASM::...i32.add... a b))`, plus the
      float ops, modulo the encoding map between the two float representations
- [ ] Metrics table:

| Metric | WASM1 (agentic) | W1T (translated) |
|---|---|---|
| Hand-written ACL2 lines | ~4,300 | builtins + prelude + config |
| Generated lines | 0 | |
| Config overrides | n/a | |
| Instructions covered | 170/170 | |
| Spec rules traceable to ACL2 defs | informal | 1:1 by name |
| Logic-mode share | 100% | |
| Oracle agreement | | |
| Effort to absorb a SpecTec update | manual | regenerate + review diff |

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
