# Audit of the fast engine: is anything gamed?

- Milestone: after V8 (plan2.md), asked by the user 2026-11-18: review the fast engine for anything that muddies the result, in particular a cheat that covers what is in fact a bug of the semantics
- Date: 2026-11-18
- Repo commit: 7bebdc4 plus this note's commit
- Status: final
- Feeds engine plan: V9 (the gate could pin the semantics, §3 item 1; `evidence.md` §6 has the two points of §3), V7b (§4)
- Incorporated in engine plan: yes (plan2.md "Current state")

## Summary

- **Nothing gamed was found in the engine.** No certified book separates
  what is proved from what runs, no proof is skipped, no test class hides
  a difference, the gate only grew, and every change of a machine went
  toward the semantics.
- **The theorem cannot see a bug of the semantics, and two things on the
  semantics' side were not proved**: its `Step` uses a hand-chosen redex
  strategy, and three performance changes were made to it while the
  engine was being built. Both are argued in writing and tested by the
  spec suite. The engine mirrors the first, so no engine theorem or test
  against the semantics can detect a fault there (§3).
- **One thing was worse than documented**: without the TeX driver's
  `data.drop` shortcut the TeX demo does not run with ACL2's default
  stack; the engine's own fallback exhausts it. With a larger stack it
  runs and reaches the same state, so the shortcut hides no difference
  on this module (§4).
- Two sentences in `evidence.md` and `engine/THEOREM.md` said the engine
  has no second definition of an instruction. It has (the fast paths),
  each proved equal. Corrected.

## Findings

### 1. What was looked for, and where

| Question | How it was checked | Result |
|---|---|---|
| Does a book make the logic differ from what executes? | `grep` of all engine books for `mbe`, `defattach`, `non-exec`, `memoize`, trust tags, raw Lisp, `redef`, `skip-proofs`, `defaxiom` | none. `ec-call` only (the identity in logic). `defun-nx` only for five functions that appear in statements and are never run. Program mode only in the generators of lemmas and of code |
| Do the certificates agree? | `engine/inspect.lsp` | 67 books under `run`, none with a skipped proof, an axiom or a trust tag |
| Is a spec function redefined, wrapped or attached anywhere under `engine/`? | `grep` of every `.lisp`, `.lsp`, `.sh` | one place: `sb-int:encapsulate` of `fast-apply-fallback` in `tex/texrun.lisp` (§4). The books and the slides driver: none |
| Does a machine special-case an instruction against its rule? | reading `machine.lisp` (`machine-step`, `op-step`, `redex-arity`, `machine-abs`) and `fast.lisp` (the array, `fast-apply-rule`, `fast-hot-step`, `fast-step`) | second computations exist (§2); each has a theorem with no hypothesis about the instruction |
| Does the abstraction repair a state? | reading `fm->ms`, `machine-abs`, `abs-ctrl` | no: the bytes put back, the control stack unfolded; nothing is filtered. And the driver reads its answer from `engine-config`, so nothing the abstraction did could be hidden from the result |
| Do the test harnesses excuse a difference? | reading `difftest2-one.lsp`, `difftest3-one.lsp`, `difftest2-summary.sh`, `slides/check.mjs` | a machine that is `:stuck` where the spec has a result is counted `:differ`; `:unsupported` and out-of-fuel are their own classes and are reported; the one excusing class, `:host-refused`, has 0 members |
| Was a gate weakened? | history of `engine/Makefile` | the list of books only grew; `no-skips` is as it was written |
| Was the semantics changed to suit the engine? | every commit that touches `translate/` outside `gen/` and `tests/` since the engine began | two commits (§3) |
| Was a machine changed away from the semantics? | the three recorded machine fixes (one memory assumed, E7; the handler's catch clauses, V3; `throw_ref` under null, V4) | each made the machine do what the semantics does; none changed the semantics |

### 2. Where the fast machine does not simply call the rule function

These are the places a cheat would have to be. Each is covered by a
theorem for every state with the invariant, or ends in `:unsupported`.

| Code | What it does | Why it cannot differ from the semantics |
|---|---|---|
| `fast-hot-step`: `local.get`, `local.set`, `local.tee`, `binop`, `relop`, `br_if` | computes the rule's result by hand, with the spec's `$local`, `$with_local`, `$binop_`, `$relop_` | `hot-step-is-op-step` (`refine-op.lisp`): when it handles the step, the result is `fast-op-step`'s; otherwise it declines and the general path runs |
| the 19 `FAST-<rule>` memory functions | the rule's own body with `(len bytes)`, `(take n (nthcdr a bytes))` and `$with_mem` replaced by array operations (`subst-memory`, a program-mode rewriter) | the rewriter is not trusted: `refine-mem.lisp` proves each generated function equal to its rule. A lemma that fails there only prints `REFINE-MEM-FAILED` (0 in the certification output), but the rule then has no (U) lemma, and the census at the end of `refine-step.lisp` stops certification unless the rules without one are exactly the two host rules |
| `redex-arity` | the machine's own table of operand counts | `<R>-ARITY` for 89 rules: it is the rule's count; for the other heads it returns `nil` and the machine stops `:unsupported` |
| `frame-safe-p`: a rule applied to the store without the bytes | 106 rules | pure, or a frame lemma per rule (`frame.lisp`, census at the end of the book) |
| `rule-may-match` | skips the fallback for a rule whose opcode is not in the redex | `<rule>-NEEDS-ITS-OPCODE` per rule; the two host rules have none and never fire (V7) |
| `byte-or-zero` in `list-to-mem` | writes 0 for a memory element that is not a byte | would be a silent repair, but it is never reached with such an element: the loader asks `config-shape-p`, the fallback refuses a result whose memory 0 is not a byte list, the store path refuses bytes that are not bytes. The function is there for the array's guard |
| `fallback-shape-ok`, the store path's bounds test, a host `call_ref`, an opcode without rules | the machine stops `:unsupported` | "stops": `fast-step-when-refused` |

So **the only freedom the theorems leave the fast machine is to stop**.
That is where a cheat could still sit: refusing a state where the
semantics does something inconvenient. In the slides no run is refused
(all 12 end with a result). In TeX the only refusals are the 63,681 host
calls (0 other fallbacks or refusals in `main`).

### 3. What the theorems cannot show: the semantics itself

The engine is proved against `W3T::STEP` as generated. If that function
is wrong, the engine is faithfully wrong, and the tests against the
semantics agree with it.

1. **Changed while the engine was built.** `translate/gen/wasm-3.0` is
   not checked in; it is a deterministic function of the IL, the
   translator and the config (`make -C translate check-gen`). Those
   changed twice since the engine began:
   - `c35e99c` (2026-11-15): measures for three recursions and one
     function per rule (E2, D4 (a)). No definition's value was meant to
     change.
   - `6b90823` (2026-11-16): three config entries and two runtime
     functions, for speed and stack depth: `:search-start` (the split
     search of `br-label-*`, `return-*`, `trap-instrs` starts at the
     first element with the fixed tag), `:constant-iter` (`e^n` by
     `make-list`), `:tests-first` (`$growmem`, `$growtable` test the
     limit before building the contents), `%SIZE` as a loop (`mbe`, the
     equality proved), `%LIST-SIZE-OK` (logically `T`). Each has a
     written reason why the value is the same. **Only the `%SIZE` one is
     proved.** The engine's proofs are about the changed definitions
     (`refine.lisp` reasons about `%TAG-LO1`). The spec suite after the
     change: 64,005 of 64,018.
   Neither commit was made to make an engine proof go through or to
   make the engine agree; the second was made to make the semantics
   finish the spec suite.
2. **`Step/ctxt-instrs` is not the generic translation of the rule.**
   Config `(:split "Step" "ctxt-instrs" :strategy :redex)`, since
   2026-11-14, before the engine: the values are the longest prefix, the
   redex ends after the first non-value. "Completeness vs. the generic
   search: T8 obligation": written, not proved
   (`../../wasm3-translation/evidence.md` §4.5). **The list machine
   chooses its redex the same way**, so the engine's theorem and tests 1
   to 3 are blind to a fault of that strategy. What would see one: the
   spec suite run on the semantics, and V8 (the slides, the DVI).
3. The numeric functions are hand-written (`translate/rt/builtins*.lisp`);
   the engine calls them (plan.md D6) and so agrees with them by
   construction.

### 4. The `data.drop` shortcut of the TeX driver

The one place where code under `engine/` changes what an engine function
does (`sb-int:encapsulate`, raw Lisp, in the driver; disclosed in the
README and in V7b). Checked by running without it
(`TEXNOSHORTCUT=1`, new; `data/v8-engine-run/shortcut.txt`):

| Run of `input.tex` | Instantiation | State after it (`STATE-DIGEST`) | `main` | DVI |
|---|---|---|---|---|
| shortcut on | 0.0 s, 40 shortcuts | memory `5368768714199100771`, store and frame `14344681081273627535` | 55,065,266 steps | `91c83590...` |
| shortcut off, default stack (64 MB) | **control stack exhausted at the first `data.drop`** | | | |
| shortcut off, `--control-stack-size 8000` | 105.9 s, 40 fallbacks | the same two numbers | 55,065,266 steps | `91c83590...` |

- The shortcut changes no state on this module: the digests (FNV-1a of
  the memory array and of the printed store, frame, stacks) are equal.
- **Without the shortcut the demo does not run as it is started.** The
  README said "102 s for the 40 of them"; that needs the larger stack.
  The overflow is most likely `len-t` (`machine.lisp`: plain recursion)
  called by `list-to-mem` on the 72 MB byte list; read from the code, no
  backtrace was taken. So every rule that takes the fallback fails this
  way on a large memory, with a Lisp error and not with `:unsupported`.
  It is an error of execution, not a wrong result, and no theorem is
  affected; but "the fallback is exact" is true in logic and not usable
  at 72 MB with the default stack.

### 5. Smaller points

- The slide renderer is compiled with `-mcpu=mvp -fno-builtin`, so that
  it stays in the integer core. The demo was shaped to the proved
  subset; that is a choice of the demo, stated in E12.
- `engine-run-is-spec-steps` does not say the engine makes progress
  (`engine/THEOREM.md` §6).
- The test numbers of tests 2 and 3 are not gates: nothing fails when
  they change.

## Open questions

- A proof, in ACL2, that the `:search-start`, `:constant-iter` and
  `:tests-first` forms equal the forms before them (generate both,
  prove the functions equal). Cheap next to T8.
- T8, the completeness of the redex strategy.
- `len-t` as a loop (`mbe`), so that the fallback runs at any memory
  size. It is in `machine.lisp`, under every book.

## Data

`data/v8-engine-run/shortcut.txt`; `engine/tex/texrun.lisp`
(`TEXNOSHORTCUT`, `STATE-DIGEST`), `engine/tex/run.sh`,
`engine/tex/README.md`, `plan/wasm-engine/evidence.md` (§2, §6),
`engine/THEOREM.md` (§1).
