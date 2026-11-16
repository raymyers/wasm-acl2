# WASM 3.0 in the browser (JSCL)

> **Goal**: run the generated WASM 3.0 semantics (`translate/gen/wasm-3.0`
> plus `translate/rt/`) in a web page. A user supplies a module (binary, or
> WAT converted to binary in the page), calls an export and gets the result
> computed by the ACL2 semantics, shown next to the browser's own engine.
> Compiled by [JSCL](https://github.com/jscl-project/jscl).
>
> **Non-interference**: the ACL2 books stay the source of truth and are
> never copied or edited for the demo. A build step reads them and writes
> derived files under `demo/build/` (never checked in). Shims supply what
> JSCL lacks. Nothing under `translate/` changes except through the
> translator (`il2acl2/`, `rt/`, config), and only for an approved item
> (today: W7, rule tags). Generated code is never edited by hand. Its
> output may change, for 1.0 too, but everything that certified or passed
> before must still certify and pass, with unchanged mode manifests.
>
> **Stepper**: the page also steps through a run one reduction at a time.
> It shows the configuration (W5), the WAT line (W6) and the name of the
> SpecTec rule that fired (W7, W8).
>
> **Status: W0 done (go); W7 next** (written 2026-11-15, after the wasm3 plan M0..M9).
> Per-session procedure: [step.md](step.md). Survey behind this plan:
> [S0-survey](notes/S0-survey.md).

---

## Current state

- **Last updated**: 2026-11-15
- **Milestones**: W0 done, **go** ([W0-feasibility](notes/W0-feasibility.md#w0-exit-gono-go-per-risk-2026-11-15));
  W7 done ([W7-rule-tags](notes/W7-rule-tags.md)); W1 done, D5 final
  ([W1-numbers-stack](notes/W1-numbers-stack.md)); W2 done ([W2-extractor](notes/W2-extractor.md)); W3 done ([W3-shim](notes/W3-shim.md));
  W4 done ([W4-semantics-node](notes/W4-semantics-node.md))
- **Waiting for the user**: nothing. The plan is meant to run headless
  from W0 to W9 (except W9 item 4). It stops only at a W0 no-go, or if W0
  contradicts the conditional W1 decision (D5).
- **Decided by the user (2026-11-15)**: D5, conditionally: numbers by
  option A (shim tower), stack by option (b) (mechanical rewrite in the
  extractor), with node `--stack-size` and the Worker as a fallback.
  **Final** (W1, 2026-11-15): both D5 conditions hold on W0's numbers.
- **Optional input**: a page design from a Claude Design session, saved to
  `plan/wasm3-demo/design/` (exports and a short README). W5 follows it if
  it exists. Otherwise W5 uses §3 and D6 as they are.
- **Decided by the user (2026-11-15)**: D6, a stepper at all three levels,
  with rule names from translator tags (option 3a). D7, the translator may
  change generated output (1.0 included) for W7, provided all certifications
  and tests still pass.
- **Extractor (W2), for the user** (each with its reason in
  `demo/extract/extract.lisp` and [W2-extractor](notes/W2-extractor.md)):
  event table: drop `in-package`, prover settings and proof events,
  `%TRY-GUARDS-T`, the `%TRY-*` and `%RULE` macros, the `%HOSTCALL-HOOK`
  encapsulate; keep `%TRY-LOGIC-T`'s defun, `defun` (xargs stripped),
  `mutual-recursion` as `progn`, `defconst` as `defparameter`; map
  `defattach` to `%DEFATTACH`, `memoize` to `%MEMOIZE`. Printing: CL
  numeric functions, `equal`, `append`, `reverse` as `ACL2::` (shim).
  Rewrites: literals (`%Q`, `%BIG`), clause-chain flattening, the stack
  rewrite (tail calls, CONS heads, continuations, calls inside clause
  chains; the last two found by W4 on `br_table.0.wasm`).
- **Shim (W3), for the user** (each with its reason next to it in
  `demo/shim/`, table in [W3-shim](notes/W3-shim.md)): `num.js`, the D5
  tower (add sub mul div neg, lt le gt ge eq, min max abs signum, floor
  ceiling truncate round mod rem, expt ash logand logior logxor lognot
  logbitp logcount integerLength, evenp oddp zerop plusp minusp integerp
  rationalp numerator denominator, q, big); `list.js`, JS loops (equal len
  trueListp count take updateNth append2 revappend memberEqual memberEq
  assocEqual; `count` memoized by cons identity, found in W4);
  `acl2.lisp`: the ACL2 numeric macros on the tower, `%Q %BIG`, natp posp
  zp nfix ifix rfix, `WHILE`, equal len true-listp append reverse take
  update-nth member-equal member-eq assoc-equal acl2-count put-assoc-equal
  alistp remove-duplicates-equal subsetp-equal iff hons-copy make-ord, mv
  mv-let, `%DEFATTACH`, `%MEMOIZE` (identity), intern$; `rule.lisp`:
  `%RULE` (identity until W8).
- **Driver (W4), for the user** (`demo/driver/glue.lisp`, reasons next
  to each): `DECODE`, `INSTANTIATE`, `DO-ACTION`, `EMPTY-ENV`,
  `LOAD-MODULE`, `INVOKE` (binds `*spec-fuel*`), `RUN-CMD`, `SPECTEST-ENV`,
  `W3T::READ-BYTES` (asks the JS host), `HOST-CALL` (attached as
  `%HOSTCALL-HOOK`), `REGISTER-HOST`; `driver/host.js` (default host: no
  result).
- **Next action**: W5 (browser page), per the headless order. W5 items
  1–3 exist in the tree, uncommitted (built by a subagent while the W7 spec
  reruns ran, smoke test passing); item 4 (Step mode) is not started.
- **Translator change (W7, for the user)**: `%RULE` (`rt/prelude.lisp`,
  a macro: `(%RULE name x)` = `x`) and two emitter changes in
  `il2acl2/compile.lisp` (`crule`, `cprod`). Reason: D6/D7, the stepper's
  rule names. `gen/wasm-1.0` regenerated (tags only).
- **W0 numbers for W1** (D5): option A costs at most 4.04× plain JSCL on
  the sample (limit 20×); the only deep recursion (65,541 on a 1-page
  module) is `$ALLOCMEM/ITER2` calling itself, tail recursive modulo
  `cons`. Both D5 conditions hold so far; W1 records it.
- **New extractor rewrite, for the user** (W0 item 3, W2 item 7):
  clause-chain flattening. Reason: the decoder's clause chain nests 1,010
  deep and the JS parsers of node (default stack), Chromium and Firefox
  overflow on it before any code runs. The rewrite is mechanical and the
  same for every chain.
- **Toolchain** (W0 item 1): flake input `jscl-src` (54c8849), packages
  `jscl` and `wabt-js`; the dev shell adds `jscl`, `jscl-xc`,
  `playwright-test`, `pngquant` and the variables `JSCL_HOME`, `WABT_JS`,
  `PLAYWRIGHT_NODE_MODULES`, `PLAYWRIGHT_BROWSERS_PATH`.
- **Headless order** (one item per session, as step.md says): W0, W7,
  W1, W2, W3, W4, W5, W6, W8, W9. W7 goes early so that W2's event table
  sees `%RULE` from the start.
- **Start from**: `make -C translate check-3.0` (it regenerates
  `gen/wasm-3.0`, which is not checked in, and must be green), then
  `sh plan/wasm3-demo/notes/data/survey/survey.sh <jscl checkout>`

## 1. Decisions

Defaults chosen by Claude are marked *(default)*. The user can change any of them before the milestone that depends on it.

- **D1 Layout** *(default)*: everything new lives in `demo/` at the repo root:
  `demo/extract/` (build step), `demo/shim/` (Lisp and JS that JSCL lacks),
  `demo/driver/` (demo glue), `demo/web/` (page), `demo/test/` (node tests)
  and `demo/build/` (output, in `.gitignore`). `demo/Makefile` is
  separate from `translate/Makefile`, so no ACL2 target depends on it.
- **D2 Toolchain** *(default)*: JSCL becomes a pinned flake input (first rev:
  54c8849, 2026-11-14), bootstrapped with nixpkgs' SBCL. Node comes from
  the flake, as it does for the oracle scripts. Unmodified JSCL; a fork
  only if W1 decides on option B.
- **D3 Scope** *(default)*: decode, instantiate (with validation:
  `$instantiate` runs `Module_ok` since wasm3 M7), invoke, run. Text format
  is out of scope, as in the wasm3 plan (§Deferred); the page converts WAT
  with wabt's JS build, and only the binary reaches the semantics.
- **D4 Oracle in the page** *(default)*: the page runs the same module on
  the browser's `WebAssembly` engine and shows both results. It does not
  say which is right; the conformance claim comes from `make -C demo check`.
- **D5 Numbers and stack** (user, 2026-11-15, conditional; final after W1): numbers by
  option A, stack by option (b), with the fallback (a) where (b) does not
  reach (see W1). The decision stands unless W0 shows one of these:
  (i) option A makes the numeric vectors more than 20× slower than plain
  JSCL fixnum arithmetic on the same ops (measured on a sample); (ii) the
  recursion that overflows is not self-recursion (mutual recursion, or a
  non-tail, non-`cons` shape), so (b) cannot remove it. In either case W1
  writes the note and stops for the user.
- **D8 Offline build** (default): every external input is pinned and
  fetched through Nix: JSCL (flake input), wabt's JS build and Playwright
  browsers (nixpkgs `playwright-driver.browsers`, or `fetchurl` with a
  hash). The page bundles wabt into `demo/build/`, with no CDN, so that
  `make -C demo check` needs no network after `nix develop`.
- **D6 Stepper** (user, 2026-11-15): three levels.
  (1) Configuration: one `step` call per click. Show the instruction
  sequence with the redex highlighted, the values, the locals, and the
  `LABEL_`/`FRAME_` nesting. Memory is shown as a diff only.
  (2) WAT line: worked out in the glue (heuristic, display only).
  (3) Rule name: the translator tags each rule clause (option 3a below).
  Option 3b, where the extractor matches clauses to IL rules by order, is
  rejected: the translator splits and reorders rules, so a mismatch would
  mislabel steps silently.
- **D7 Translator changes** (user, 2026-11-15): allowed for W7. They go
  through the generator only, never through hand edits of `gen/`. Output
  may change for every version, 1.0 included (the checked-in `gen/wasm-1.0`
  is regenerated). Every book that certified still certifies, every test
  that passed still passes, the mode manifests (`t0-modes`, `t0-modes-3.0`)
  match unchanged, and `check-gen` determinism holds.

## 2. Starting point (survey, 2026-11-15)

From [S0-survey](notes/S0-survey.md) at 354f87c:

- 27 generated books, 486,141 lines, about 33 MB. The largest are
  `5_3-binary_instructions` (18 MB), `4_3-execution_instructions` (9 MB)
  and `2_3-validation_instructions` (4 MB).
- What is generated: `defun`s inside `%TRY-LOGIC-T` (1,298) and
  `%TRY-GUARDS-T` (1,298), plus `mutual-recursion`. The bodies use plain
  list code (`let`/`let*`, `car`/`cdr`, `equal`, `eq`, `and`) and ACL2's
  `len`, `nfix`, `natp`, `take`, `true-listp`. The other events (`defthm`,
  `in-theory`, `table`, `verify-guards`, `value-triple`, `local`,
  `encapsulate`/`defattach`, `memoize`, `include-book`) are few and
  mechanical.
- JSCL: numbers are JS doubles. `rationalp` is `integerp`, there are no
  bignums, and `integer-length` errors above 2^30. The semantics needs
  bignums (i64, v128) and exact rationals (float arithmetic in
  `rt/builtins.lisp`).
- Stack: memory bytes are a list of `65536 × pages` built by recursion
  (`$ALLOCMEM/ITER2`). JSCL's `equal` recurses on `cdr`. `%size`
  (`acl2-count`) runs at runtime in the termination checks.
- The ACL2 conformance driver (`translate/tests/spec/t7-lib-3.0.lisp`) shows
  the entry points: `gram/bmodule` (decode), `$instantiate`, `$invoke`,
  `step`, plus pure helpers (`to-val`, `resolve-imports`, `run-steps`,
  `final-config`, `instantiate`, `do-action`).

## 3. Architecture

```
translate/gen/wasm-3.0/*.lisp ─┐                   (read only)
translate/rt/*.lisp ───────────┼─▶ demo/extract ─▶ demo/build/lisp/*.lisp ─┐
translate/tests/spec/t7-lib-3.0.lisp (named pure defuns) ┘                 │
demo/shim/*.lisp (ACL2 layer for JSCL) ────────────────────────────────────┼─▶ JSCL (AOT, SBCL host)
demo/driver/*.lisp (JS-facing glue) ───────────────────────────────────────┘        │
                                                                demo/build/wasm3.js ─┴─▶ demo/web (Worker + page)
                                                                                      └─▶ demo/test (node)
```

- **Extractor** (`demo/extract`): runs in the flake's ACL2, in raw Lisp, so
  that symbols are read with the real `W3T`/`WRT`/`ACL2` packages and keep
  their identity. It follows the `include-book` order from
  `gen/wasm-3.0/wasm3.lisp`. Each top-level event goes through a **closed
  table**, and an event that is not in the table is an error (as `make gen`
  fails on a raw Lisp error):
  unwrap `%TRY-LOGIC-T`/`%TRY-GUARDS-T` to their `defun`; drop `defthm`,
  `in-theory`, `table`, `verify-guards`, `value-triple`, `local`, `xargs`;
  turn `mutual-recursion` into `progn`; map `defattach %hostcall-hook` and
  `memoize` to shim calls; keep `%RULE` tags (W7), which the shim defines
  as a recorder; rewrite number literals that JSCL cannot read
  (ratios, |n| > 2^53) into shim constructors; print every symbol
  package-qualified. Output is deterministic (checked as `check-gen` is).
- **Shim** (`demo/shim`): packages, the numeric representation (W1), the
  ACL2 functions in use, `equal`/`acl2-count`/`len` that do not recurse on
  `cdr`, memoization, host-call hook, `er` as a JS exception.
  The shim is the only hand-written semantics-adjacent code, so each part
  of it is checked against ACL2 output (W3 exit).
- **Driver**: the pure helpers of `t7-lib-3.0.lisp`, extracted by name, are
  not copied. Thin demo glue converts JS values (`Uint8Array`, `number`,
  `BigInt`, `Float32`/`Float64` bits) to and from the semantics' encodings.
- **Page**: the semantics runs in a Web Worker (it does not freeze the UI,
  and step limits and stack settings stay per run). The page has a WAT/binary
  input, an export picker, args, the result, the step count, and the native
  engine's result. It has two modes: **Run** (to completion, under fuel)
  and **Step** (one `step` per click, or N steps, or run to the next
  line).
- **Stepper data per step**: the configuration after the step, as a
  rendered view (not the whole store). The memory diff against the
  previous step. The line mapping (W6). The rule chain (W8), for example
  `Step/ctxt-instrs → Step/pure → Step_pure/nop`, recorded by the shim's
  `%RULE` while that one `step` call runs.
- **Rule tags** (W7): for each rule clause of a relation, the translator
  wraps the clause's result in `(%RULE "Rel/rule-id" result)`. In ACL2,
  `%RULE` is a macro in `rt/prelude.lisp` that expands to `result`, so the
  terms that ACL2 admits and proves are the same as before. In JSCL, the
  shim's `%RULE` pushes the name when the clause succeeds.

## 4. Milestones

### W0: Feasibility spike (go/no-go)
1. [x] Toolchain in the flake (D2, D8): `nix develop` gives `jscl` (node),
       the SBCL-hosted cross compiler, wabt's JS build, and Playwright
       with headless Chromium and Firefox. `make -C demo jscl-hello`
       compiles and runs a one-line file in node. `make -C demo
       browser-hello` loads it in both headless browsers, and writes the
       first progress screenshot (step.md).
       **Done 2026-11-15** ([W0-feasibility](notes/W0-feasibility.md)):
       `nix/jscl.nix` (SBCL 2.6.6 image `jscl-xc` saved after bootstrap),
       wabt.js 1.0.39, Playwright 1.61.1 with nixpkgs Chromium 1228 and
       Firefox 1532. `make -C demo check`: node PASS, wabt.js PASS,
       Chromium PASS, Firefox PASS. Screenshot `progress/01-W0-browser-hello.png`
2. [x] Hand-run slice: `rt/prelude`, `rt/builtins*`, and the books
       `0_*`/`1_*` through a throwaway version of the extractor table,
       compiled with JSCL and loaded in node. Record what JSCL rejects
       (`declare xargs`? package syntax? reader?).
       **Done 2026-11-15** ([W0-feasibility](notes/W0-feasibility.md#item-2-hand-run-slice-2026-11-15)):
       JSCL rejects nothing (`|PKG|::|NAME|` symbols, `declare xargs` and
       `ignorable` accepted), but reads the ratio `1/2` as a symbol
       without a warning (3 literals in `rt/builtins.lisp`). 17 undefined
       ACL2 functions in the slice, 24 names in all books (incl. `mv`,
       `mv-let`). `1_0-syntax_profiles` is outside the include chain
3. [x] Measure for the slice, then project to all 27 books: JS size,
       compile time, node load time. If the projection is above 50 MB JS or
       60 s load, measure reachability pruning from the §2 entry points
       (count of `defun`s reachable / total).
       **Done 2026-11-15**, measured on all books instead of projected
       ([W0-feasibility](notes/W0-feasibility.md#item-3-size-compile-time-load-time-2026-11-15)):
       3.75 MB JS, JSCL compile 2.3 s, node load 0.10 s (plus 0.16 s for
       `jscl.js`). Pruning not needed. New: the JS parsers of node (default
       stack), Chromium and Firefox overflow on the 1,010-deep clause chain
       of the decoder; mechanical clause-chain flattening (depth 111) makes
       all of them load it (Chromium Worker 0.42 s, Firefox Worker 0.64 s,
       incl. `jscl.js`). Added as W2 item 7
4. [x] Deepest recursion on a decode + instantiate + `step` run of a module
       with 1 page of memory, measured in ACL2 (instrumented run or the
       longest list in the store) and in node (default and `--stack-size`).
       Browser Worker stack in Chrome and Firefox for the same depth
       (a synthetic JS recursion is enough).
       **Done 2026-11-15** ([W0-feasibility](notes/W0-feasibility.md#item-4-deepest-recursion-on-a-1-page-module-2026-11-15)):
       instrumented ACL2 run: decode 33, instantiate **65,541** (65,537 of
       them `$ALLOCMEM/ITER2` calling itself, tail recursive modulo
       `cons`), invoke 38. JSCL frames of that shape that fit: node 9,695
       (default), 55,095 (`--stack-size=3900`), 229,711 (worker, 16 MB);
       Chromium Worker 2,047, Firefox Worker 4,095. Overflows, but it is
       self-recursion: go. JSCL's `equal` and `append` recurse on `cdr`
       (shim replaces them)

5. [x] Option A cost sample (for D5 (i)): `+`, `*`, `floor`, `logand` and
       `ash` on fixnums, plain JSCL against the shim tower, 10^6 ops each.
       **Done 2026-11-15** ([W0-feasibility](notes/W0-feasibility.md#item-5-option-a-cost-sample-2026-11-15)):
       prototype tower (safe-integer numbers, BigInt beyond) / plain JSCL:
       `+` 3.24, `*` 3.28, `floor` 3.93, `logand` 0.14, `ash` 0.89 / 0.75
       (max over two runs 4.04×). Results equal

**Exit**: note `W0-feasibility` with the numbers above, and a go/no-go for
each risk. **No-go** (stops the plan for the user) if, after pruning has
been measured: the JS of the full or pruned set is over 100 MB, or loading
it in node takes over 60 s, or the measured deepest recursion of a 1-page
module overflows a Chromium Worker's stack and is not self-recursion (so
no rewrite can help). Anything below these limits is go, with the numbers
recorded.

**W0 result (2026-11-15): go.** 3.75 MB JS, 0.10 s node load, no pruning;
the deepest recursion overflows a Chromium Worker but is self-recursion;
option A ≤ 4.04×. One new requirement: clause-chain flattening (W2 item 7).
[W0-feasibility](notes/W0-feasibility.md#w0-exit-gono-go-per-risk-2026-11-15).

### W1: Numbers and stack (confirm D5)
The user has decided A + (b), conditionally (D5). This milestone records
the design and checks the D5 conditions against W0. It stops for the user
only if a condition fails.
1. [x] Design note `W1-numbers-stack` (the options below, the choice, and
       the W0 numbers that confirm it):
   - **Numbers.** (A) Shim tower in Lisp: the demo's packages shadow the
     CL numeric functions (`+ - * / < <= > >= = floor mod rem truncate
     ceiling expt ash log* integer-length logcount numerator denominator
     integerp rationalp`) and `equal`. Integers are canonical (JS number
     when a safe integer, else `BigInt`), and ratios are a normalized
     struct. JSCL is unchanged. (B) Patch JSCL's number tower with BigInt
     and ratios (a fork to carry, possibly upstreamable). (C) Change the
     encodings in `rt/`, which is rejected: it is source of truth.
     Measure the cost of (A) on the numeric vectors.
   - **Stack.** Measured from W0 item 4. Options: (a) node `--stack-size`
     and Worker only, with a documented memory limit; (b) the extractor
     mechanically rewrites self-recursive functions (tail calls into
     loops, tail-recursion modulo `cons` into accumulate-and-reverse), the
     same rewrite for every function, checked by W3/W4 tests; (c) shim
     overrides for named hot functions (rejected unless (b) cannot cover
     them, because it duplicates semantics).
       **Done 2026-11-15** ([W1-numbers-stack](notes/W1-numbers-stack.md)):
       A and (b) chosen as decided, (a) kept as the node-only fallback; (c)
       not used
2. [x] D5 conditions checked against W0. If both hold, the note says
       so and D5 is final. If one fails, stop for the user
       **Done 2026-11-15** ([W1-numbers-stack](notes/W1-numbers-stack.md#d5-final)):
       (i) option A at most 4.04× plain JSCL (limit 20×); (ii) the
       overflowing recursion ($ALLOCMEM/ITER2, 65,541 frames) is
       self-recursion, tail recursive modulo `cons`. Both hold: **D5 final**.
       (Later, W4: the overflows of `br_table.0.wasm` are self-recursion too)

**Exit**: D5 final, or a stop for the user with the failed condition
measured.

### W2: Extractor
1. [x] `demo/extract` per §3: closed event table, include order, literal
       rewrite, qualified symbols, `make -C demo extract` writes
       `demo/build/lisp/`
       **Done 2026-11-15** ([W2-extractor](notes/W2-extractor.md#event-table-closed-anything-else-is-an-error)):
       27 books + `driver.lisp`; 1,515 `defun`, 1,298 `%TRY-LOGIC-T`, 12
       `mutual-recursion`, 0 unknown events
2. [x] Report printed by every run: events per kind per book, dropped
       events by kind, and ACL2 functions referenced but not defined by
       the books (the list that the shim must provide)
       **Done 2026-11-15**: `REPORT` lists events per kind, dropped events,
       rewrites, and the undefined names: 59 in ACL2 (the shim), 52 in
       COMMON-LISP (JSCL), 3 elsewhere (`READ-BYTES`, `%HOSTCALL-HOOK`, `%RULE`)
3. [x] Determinism: two runs are byte-identical (`make -C demo check-extract`)
       **Done 2026-11-15**: 34 files identical; `translate/` clean after the runs
4. [x] Named extraction of the pure driver helpers from
       `tests/spec/t7-lib-3.0.lisp`. A name that does not exist is an error
       **Done 2026-11-15**: 34 names (incl. `run-cmd`, `instantiate`,
       `do-action`, `spectest-env`) into `driver.lisp`
5. [x] Pruning (only if W0 item 3 said so): keep the `defun`s reachable
       from the entry points. The kept/total count is in the report
       **Not needed** (W0 item 3: 3.75 MB JS, 0.10 s load)
6. [x] Stack rewrite (only if W1 chose (b))
       **Done 2026-11-15** ([W2-extractor](notes/W2-extractor.md#rewrites-each-the-same-for-every-form)):
       672 self-recursive defuns into loops (tail calls, CONS heads,
       continuations, calls inside clause chains; the last two added for
       W4's br_table.0.wasm), 34 left recursive with the reason in `REPORT`
7. [x] Clause-chain flattening (from W0 item 3): the translator's clause
       chains `(LET ((%R Xi)) (DECLARE ...) (IF %R (CAR %R) rest))` and
       `(... (IF %R %R rest))` become one flat sequence, so that no form
       nests deeper than the JS parsers accept (decoder: 1,010 → 111). Same
       rewrite for every chain; a chain stops at an Xi that mentions `%R`.
       Checked by W3/W4 like the rest of the extraction
       **Done 2026-11-15**: 104 chains, 1,579 links; decoder depth 111

**Exit**: `demo/build/lisp/` regenerates deterministically. The report
lists 0 unknown events. `git status translate/` is clean after the run.

**W2 result (2026-11-15): exit met.** Deterministic, 0 unknown events,
`translate/` clean (`make -C demo check-extract`).

### W3: Shim and numerics in node
1. [x] `demo/shim` per §3 and D5, covering the W2 item 2 list (0 left)
       **Done 2026-11-15** ([W3-shim](notes/W3-shim.md#shim-contents-each-with-its-reason-in-the-source)):
       `num.js` (D5 tower), `list.js` (loops; `acl2-count` memoized),
       `acl2.lisp`, `rule.lisp`; all 59 ACL2 names of the W2 report covered
2. [x] Vector runner in node. The extractor converts the ACL2 test data
       (`tests/sem/numeric-vectors.lsp`, `tests/sem-3.0/simd-vectors-3.0.lsp`,
       numeric data under `tests/sem-3.0`), and the runner applies the same
       builtins and compares the results. The runner re-implements no test
       logic beyond the comparison that the ACL2 test books make
       **Done 2026-11-15** ([W3-shim](notes/W3-shim.md#vector-runner-item-2)):
       the books' own `CHECK-VECTORS` and `CHECK-SIMD`, extracted by name;
       numerics 8,724/8,724 (243 ms), SIMD 1,008/1,008 (356 ms), full
       relaxed profile 480/480
3. [x] Shim unit tests for `equal`, `acl2-count`, ratios and bignum edge
       cases (2^53 ± 1, 2^64, negative `mod`/`floor`, `ash` both ways),
       with expected values printed by ACL2
       **Done 2026-11-15** ([W3-shim](notes/W3-shim.md#unit-tests-item-3)): 119/119

**Exit**: 8,724/8,724 numeric and 1,008/1,008 SIMD vectors (incl. 480
relaxed) pass under JSCL in node, the ACL2 counts (wasm3 M1).

**W3 result (2026-11-15): exit met.** 8,724/8,724 and 1,008/1,008 (480
relaxed) under JSCL in node; units 119/119. `make -C demo check` runs
`vectors` and `units`.

### W4: The whole semantics in node
1. [x] All books (or the pruned set) load. `demo/driver` provides
       `decode(bytes)`, `instantiate(module, imports)` and
       `invoke(inst, name, args, fuel)`, built on the extracted
       `t7-lib-3.0` helpers
       **Done 2026-11-15** ([W4-semantics-node](notes/W4-semantics-node.md#driver-item-1)):
       all books + driver helpers + glue, `wasm3.js` 3.96 MB, node load 0.13 s
       (+ 0.17 s `jscl.js`); `DECODE`, `LOAD-MODULE` (decode + instantiate
       against an environment of registered instances), `INVOKE` (with fuel),
       `RUN-CMD`
2. [x] Host imports: `%hostcall-hook` attached to a JS callback (the
       `spectest` module of `tests/spec/spectest-3.0.wat`, plus a `print`
       for the page)
       **Done 2026-11-15** ([W4-semantics-node](notes/W4-semantics-node.md#host-imports-item-2)):
       `HOST-CALL` asks `globalThis.DEMOHOST`; `REGISTER-HOST` makes a
       module's exports host functions. `make -C demo host`: `f(20) =
       inc(20) * 2 = 42` with `inc` in JS. The spectest module is an ordinary
       module (its prints are no-op wasm functions), run as in t7. The
       semantics calls a host several times per step, so a host answers as a
       function; the page's `print` (W5) records once per step
3. [x] Conformance in node: a script runner over the converted spec-test-3
       data (`translate/tests/spec/data-3.0/<name>.lsp` and `.wasm`), on
       this fixed subset (names as in `results-3.0/NAMES`): `i32`, `i64`,
       `f32`, `f64`, `memory`, `call_indirect`, `br_table`,
       `simd--simd_i32x4_arith`, `simd--simd_lane`, `gc--struct`,
       `gc--i31`, `exceptions--try_table` (7,086 `T7-CMD` lines in the local results present on 2026-11-15).
       Compare each command's kind and pass/fail with the `T7-CMD` lines
       of the ACL2 run in `results-3.0/<name>.out`. Agreement means the
       same verdict, including the commands that fail in ACL2 too.
       **Baseline**: `data-3.0/` and `results-3.0/` are gitignored. Make
       them in the session: `make -C translate spec-data SPEC=3.0`, then
       `make -C translate spec SPEC=3.0` (about 11 min), at the current
       commit. Record that commit in the note
       **Done 2026-11-15** ([W4-semantics-node](notes/W4-semantics-node.md#conformance-item-3)):
       baseline the after-W7 `results-3.0/` (commit 0f36ff1). **7,087/7,087
       commands agree** in 12/12 scripts, compared per command (a CRASH in
       ACL2 prints no `T7-CMD` line; 7,086 lines + 1). `call_indirect` on
       ACL2's prefix (ACL2 killed at 600 s); #72 `fib-i64(20)` fails on both
       sides (ACL2 CRASH, node `:FUEL`). Two bugs found and fixed on the way:
       the stack rewrite missed shapes (`br_table`), and `acl2-count` was 80%
       of the time (memoized)
4. [x] Timing: ms per step in node, against 0.011 ms in ACL2 (wasm3 M3)
       **Done 2026-11-15** ([W4-semantics-node](notes/W4-semantics-node.md#timing-item-4)):
       0.32–3.84 ms per step on 5 invokes; the same invokes in ACL2: node is
       about 32× slower on `fac-iter` (0.87 ms against about 0.027 ms per
       step), 1.8× on `fac-rec`, 4× faster on `call_indirect` `fac-i64(25)`
       (1.44 s against 6.4 s)

**Exit**: the chosen subset agrees with ACL2 command by command (a
disagreement is a shim or extractor bug, never a "known difference"). The
per-step time is recorded.

**W4 result (2026-11-15): exit met.** 7,087/7,087 commands agree; per-step
time recorded. `make -C demo check` adds `host` and `conformance-quick`
(the subset without `call_indirect`).

### W5: Browser page
1. [ ] `demo/web`: Worker that loads `wasm3.js`, page UI per §3 and D4
       (and `plan/wasm3-demo/design/` if it exists), WAT via the bundled
       wabt (D8), examples: factorial (i64), float math,
       memory load/store, a GC struct, an exception, a SIMD lane op
2. [ ] Fuel and cancel: a step limit per run, and a Stop button that ends
       the Worker
3. [ ] Smoke test: Playwright (W0 item 1) runs every example in headless
       Chromium and headless Firefox, and each result must equal native
       `WebAssembly` in the same browser

4. [ ] Stepper, level 1 (D6): a Step mode in the Worker protocol
       (`step`, `stepN`, `runToEnd`) and a configuration view. The view
       shows the instruction sequence with the redex highlighted (the
       first non-value instruction in the innermost `LABEL_`/`FRAME_`),
       the operand values, the locals of the current frame, the nesting,
       and the bytes of memory that changed. The step count for a run in
       Step mode equals the count in Run mode (tested)

**Exit**: the smoke test passes in `make -C demo check` in both
browsers, and it also steps one example to its end. Screenshots of Run
and Step mode are in `progress/` (step.md).

### W6: Stepper, WAT line
1. [ ] The page shows the module as wabt prints the binary, one
       instruction per line, with its own offsets. User formatting is kept
       only for flat WAT (recorded as a limit)
2. [ ] Line mapping in the glue. The function comes from the step where a
       `call` turns into a `FRAME_` (kept per frame on a stack). The
       position is `len(body) − len(remaining)` inside the innermost
       `LABEL_`/`FRAME_`, since reduction consumes from the front. Blocks
       and loops map through the `LABEL_` that they turn into
3. [ ] "Run to next line" and line breakpoints

**Exit**: on every W5 example, a step-through with the mapping checked at
each step against a hand-written list of expected lines (fac: every
line, plus the branch and `call` lines). The page labels the
highlighting as a display aid, not part of the semantics.

### W7: Rule tags in the translator (D7)
1. [x] Design note `W7-rule-tags`: where the translator emits the tag for
       each relation shape (plain clause chain, split `Step`, search and
       iteration helpers, `:rel-override` (the `Instrs_ok` sequencer:
       no IL rule, no tag), enumeration variants, `:given-entry`), and the
       exact spelling of names (`Rel/rule-id`, as in the IL, e.g.
       `Step_pure/nop`)
       **Done 2026-11-15** ([W7-rule-tags](notes/W7-rule-tags.md#design-item-1)):
       the tag wraps a rule's output inside its success list,
       `(list (%RULE "Rel/id" out))`, so the shape `(list x)` that marks an
       unconditional rule is kept; grammar productions are positional,
       `Gram/#k`. Untagged: the `Instrs_ok` override, closure relations
       (`Steps`), dropped rules, `def` clauses
2. [x] `%RULE` in `rt/prelude.lisp` (a macro that expands to its second
       argument), and the emitter change in `il2acl2/`. Every relation is
       tagged, not just `Step*`: typing and the decode grammar get names too
       (decode tags are useful for a future decode view)
       **Done 2026-11-15**: one change in `crule`, one in `cprod`
       (`cprods` passes the position); `%RULE` is imported by W1T, W2T and
       W3T like the other rt names
3. [x] Regenerate 1.0, 2.0 and 3.0 with `make gen`. Commit the new
       `gen/wasm-1.0` in the same commit as the translator change
       **Done 2026-11-15**: tags 1.0 457, 2.0 927, 3.0 1,434 (1,147
       distinct). `gen/wasm-1.0`: 5 files changed, `package.lsp` imports
       `WRT::%RULE`
4. [x] Gates: `make -C translate check`, `check-2.0`, `check-3.0` green.
       `t0-modes` and `t0-modes-3.0` match the manifests unchanged.
       Certification times recorded against the earlier ones (3.0:
       4 min 38 s, wasm3 M9).
       **Spec runs, per command**: before the change, run `make spec`
       (1.0) and `make spec SPEC=3.0` at the parent commit (after
       `make spec-data` for each), and keep the `results*/` directories
       as the baseline (outside the repo tree, path in the note). Run both
       again after the change. For every script, the sequence of `T7-CMD`
       lines must be identical. The only exceptions are scripts that timed
       out or crashed in either run (listed in the note, rerun once with
       a doubled TIMEOUT). Totals are not compared: they depend on
       timeouts (63,326/63,883 in wasm3 M8 against 63,324/63,880 in a
       later local run, 1 timeout and 1 crash)
       **Done 2026-11-15** ([W7-rule-tags](notes/W7-rule-tags.md#gates-item-4)):
       `check` exit 0 (71 s, 1.0 recertified), `check-2.0` exit 0 (140 s,
       was 141 s), `check-3.0` exit 0 (279 s, was 284 s; M9 4 min 38 s);
       manifests unchanged, `check-gen` passes. Spec runs (baseline at
       d716fa8 in `/Users/Apple/dev/wasm-acl2-w7-baseline/`, after in
       `/Users/Apple/dev/wasm-acl2-w7-after/`): identical `T7-CMD`
       sequences for 258/258 (3.0, 65,009 lines) and 67/67 (1.0, 11,964
       lines). The 9 scripts that timed out or crashed (3.0: 5, 1.0: 4)
       were rerun once with a doubled TIMEOUT on both sides: identical, or
       identical on the common prefix where the timeout cut them; 3.0
       `call_ref` now completes on both sides (35/35)
5. [x] Coverage check: every rule id of `Step`, `Step_pure` and
       `Step_read` in the IL appears as a tag in `gen/wasm-3.0`, or is
       listed as dropped by the probe. 218 reduction rules (wasm3 M3)
       **Done 2026-11-15** ([W7-rule-tags](notes/W7-rule-tags.md#coverage-item-5)):
       Step 36/36, Step_pure 79/79, Step_read 103/103: 218/218, none missing

**W7 result (2026-11-15): exit met.** Gates green, manifests unchanged,
identical per-command spec results, coverage 218/218.

**Exit**: item 4 green, with unchanged mode manifests and identical
per-command spec results; item 5 at 218 of 218 (or every missing one has
a reason).

### W8: Stepper, rule names
1. [ ] Shim `%RULE` recorder. `step` returns the rule chain of that one
       reduction (the outermost rule first). Run mode turns the recorder off
       (cost measured: the per-step time with and without it)
2. [ ] Page: the chain is shown at each step. Each name links to a
       search for the rule id in the SpecTec source at the pinned rev
       (`WebAssembly/spec@943c5df`, `specification/wasm-3.0/`). A direct
       file-and-line link is optional, only if the IL keeps source
       positions
3. [ ] Test: for a fixed set of small programs, the expected chain at
       every step is written by hand from the spec (`nop`, `i32.add`,
       `block`/`br`, `call`/`return`, a trap, a `throw`/`catch`), and the
       node stepper must give exactly those chains

**Exit**: item 3 passes in `make -C demo check`. Every step of every W5
example has a non-empty chain.

### W9: Build integration and non-interference
1. [ ] `make -C demo` (all), `make -C demo check` (W2 determinism, W3, W4
       subset, W5 smoke, W6 line checks, W8 chains), and the flake output
       `packages.wasm3-demo` (a static directory)
2. [ ] Non-interference check: after `make -C demo check`, `git status
       --porcelain translate/` is empty (the demo build writes nothing
       there; only W7 changed it, through the translator), and
       `make -C translate check`, `check-2.0` and `check-3.0` are green
3. [ ] `demo/README.md`: how to build, what is derived from which file,
       where the shims are and why
4. [ ] Publishing the static site (GitHub Pages or other): the user
       decides. **Not part of a headless run**: leave it open, and list it
       in "Current state"

**Exit**: items 1 to 3. One command builds the demo from a clean
checkout, and the ACL2 gates are unchanged.

### Order and dependencies

```
W0 ── W1 ──┬─ W3 ── W4 ── W5 ──┬─ W6 ──┬─ W9
     W2 ───┘                   └─ W8 ──┘
W7 (translate/ only) ──────────────┘
```

- W7 changes only `translate/`, and needs no demo milestone. It can run at
  any time (early is better: W2's event table then sees `%RULE` from the
  start). It must be done before W8.
- W6 and W8 both need W5, and are independent of each other.

- W0 first: it decides whether the plan goes ahead and supplies W1's numbers.
- W2 items 1 to 4 can start after W0, in parallel with W1. Items 5 and 6
  depend on W0 and W1.
- W3 needs W1's decision and W2. W4 needs W3 (numerics must be right
  before conformance can mean anything).

### Deferred
- Step back. A configuration holds the store (65,536 list elements per
  page), so snapshots are costly. Replay from the start up to N − 1 steps
  is the cheap alternative.
- A decode view (grammar rule tags from W7 on the binary).
- 1.0 and 2.0 targets (the extractor's table should already fit them).
- Text format by the semantics (deferred upstream, wasm3 plan).

## 5. Risks and go/no-go points

| Risk | Evidence | Go/no-go |
|---|---|---|
| JS too large or too slow to load | 33 MB source, one 18 MB book ([S0](notes/S0-survey.md)) | W0 item 3; pruning in W2 item 5; if still too large, lazy load per book or a node-only demo (user decides) |
| No bignums or ratios in JSCL | `rationalp` = `integerp`, doubles only ([S0](notes/S0-survey.md)) | D5: option A, unless W0 item 5 shows more than 20× (W1 stops); W3 exit is all the vectors |
| JS stack overflow on 1-page memories | 65,536-element byte list built by recursion; recursive `equal` ([S0](notes/S0-survey.md)) | W0 item 4 measures it, W1 decides; fallback: demos without memory, recorded as a limit |
| Too slow per step | 0.011 ms per step in ACL2 (wasm3 M3); JSCL plus shim arithmetic will be slower | W4 item 4; the demo uses small examples and fuel, which is acceptable if a fib/fac example runs in under 5 s |
| Shim bug presented as a semantics result | the shim is hand-written | the W3 and W4 exits compare every part with ACL2 output, and the page states that the result comes from the extracted semantics plus the shim |
| Rule tags change what ACL2 proves or how long it takes | `%RULE` is a macro that expands to its result, so the admitted terms are the same; certification is time-limited per attempt (wasm3 M9) | W7 item 4: unchanged mode manifests and spec totals; a slower certification is recorded, and a mode change stops W7 for the user |
| Line mapping wrong on unusual control flow | heuristic in the glue (D6) | W6 exit checks every step on the examples; the page labels it a display aid |
| Stepper too slow per click | config rendering for every step | render only the instructions and the frame; memory as a diff (W5 item 4) |
| Drift: books change and the demo breaks silently | gen/ is regenerated by the gates | the closed event table fails loudly; `make -C demo check` belongs in the routine after a translator change (the user decides whether to add it to the gates) |
