# W0 feasibility spike
- Milestone: W0 (feasibility spike, go/no-go)
- Date: 2026-11-15
- Repo commit: fbe1979 (+ the W0 commits)
- JSCL: jscl-project/jscl@54c88494e9f8f22e4c24c666e84aab7053f18cee
- Status: draft (items 1 to 3 done; items 4 and 5 pending)
- Feeds demo plan: W0 exit, W1 (D5 conditions), §5 risks
- Incorporated in demo plan: yes (W0 items as they complete)

## Summary
Item 1: the toolchain is in the flake. `nix develop` gives `jscl` (node
REPL), `jscl-xc` (SBCL 2.6.6 image with the JSCL cross compiler, saved after
bootstrap), wabt.js 1.0.39 (`$WABT_JS`), Playwright 1.61.1 with nixpkgs'
Chromium and Firefox, and pngquant. `make -C demo check` runs the hello
program in node and in both headless browsers.

## Findings

### Item 1: toolchain (2026-11-15)
- **JSCL** (`nix/jscl.nix`, flake input `jscl-src`): built in the store with
  nixpkgs' SBCL. `jscl.lisp` captures `*base-directory*` at load time, so
  the source is copied to `$out/share/jscl` and built there. It also runs
  `git rev-parse HEAD` for `*git-commit-hash*`; the build puts a fake `git`
  that prints the pinned rev on `PATH`. `SOURCE_DATE_EPOCH` is the input's
  `lastModified`. Outputs: `dist/jscl.js`, `dist/jscl-node.js`, and
  `lib/jscl/jscl-xc.core` (SBCL image saved after `bootstrap` and
  `build-node-repl`, so `compile-application` has the target environment
  without rebuilding JSCL). `bin/jscl-xc` = `sbcl --core jscl-xc.core`.
  JSCL is unmodified (D2).
- **Compiling an application**: `jscl-xc::compile-application FILES OUT`
  with `*package*` = `JSCL-XC`. The output starts with a prologue that
  `require`s `./jscl` (node) or uses `window.jscl` / `self.jscl` (browser,
  worker), so `jscl.js` is copied next to it in `demo/build/`.
- **Package names at compile time**: in the cross compiler, JSCL's internal
  package is `JSCL-XC`, not `JSCL` (`jscl::jsstring` fails to read with
  "does not designate any package"; `jscl-xc::jsstring` works, as in
  JSCL's own `node/node.lisp`). JS strings need `jsstring`: a Lisp string
  reaches `console.log` as an object of characters.
- `jscl.js` prints `loading boot.lisp!` ... `loading toplevel.lisp!` on
  stdout when it loads. Harmless; the hello check reads the last line.
- **wabt.js**: npm `wabt@1.0.39` (published 2025-11-05), fetched by
  `fetchurl` with a hash (package `wabt-js`). One `index.js` with the wasm
  inlined, so the page can bundle it without a CDN (D8).
- **Playwright**: nixpkgs `playwright-test` 1.61.1 (node modules at
  `$PLAYWRIGHT_NODE_MODULES`) and `playwright-driver.browsers`
  (`chromium-1228`, `chromium_headless_shell-1228`, `firefox-1532`) at
  `$PLAYWRIGHT_BROWSERS_PATH`; nothing is downloaded at test time. Runs on
  aarch64-darwin with `PLAYWRIGHT_SKIP_VALIDATE_HOST_REQUIREMENTS=true`.
- **Results** (`make -C demo check`):
  - `jscl-hello`: `hello from JSCL: 3` in node 24.18.1.
  - `wabt-hello`: WAT `add` → 41-byte binary, `add(2,3) = 5` in node.
  - `browser-hello`: Chromium PASS, Firefox PASS (no page errors).
  - Screenshot `progress/01-W0-browser-hello.png` (5 KB), retaken with
    `make -C demo browser-hello SHOT=<path>`.

### Gates (item 1 commit)
`make -C translate check` exit 0 (5 s), `check-2.0` exit 0 (141 s),
`check-3.0` exit 0 (284 s). Only `flake.nix` (dev shell, new packages) changed;
no ACL2 input.

### Item 2: hand-run slice (2026-11-15)
Throwaway extractor `data/w0-slice/extract-slice.lisp`, run in ACL2's raw
Lisp after `gen/wasm-3.0/portcullis.acl2`, so forms are read with the real
packages. It follows `include-book` depth first from a root book and prints
every symbol as `|PKG|::|NAME|` (keywords `:|NAME|`). Event table of the
spike: drop `in-package`, `include-book`, `set-verify-guards-eagerness`,
`set-bogus-mutual-recursion-ok`, `defthm`, `in-theory`, `program`,
`%TRY-GUARDS-T`, `defmacro` (the four rt macros are event wrappers),
`memoize`, `encapsulate`; unwrap `%TRY-LOGIC-T`; `mutual-recursion` →
`progn`; `(defattach f g)` → `(defun f (&rest args) (apply 'g args))`.
The JSCL side has only `(defpackage "ACL2" (:use))`, same for `WRT` and
`W3T` (`data/w0-slice/pkgs.lisp`).

Slice = `rt/prelude`, `rt/builtins`, `rt/builtins-3.0`, `0_1`..`0_3`,
`1_1`..`1_4` (`1_0-syntax_profiles` is **not** in the include chain from
`wasm3.lisp`; it is a dead book that redefines `$ND` as a stub, so the
extractor must follow the chain, not the directory listing).

- Events in the slice: 567 `defun` (incl. the ones inside wrappers), 396
  `%TRY-LOGIC-T`, 396 `%TRY-GUARDS-T`, 5 `mutual-recursion`, 4 `defthm`,
  4 `defmacro`, 2 `in-theory`, 1 `encapsulate`, 1 `defattach`, plus
  `in-package`/`include-book`/`set-*`. No unknown event.
- **What JSCL accepts**: the `|PKG|::|NAME|` printing (names such as `$MIN`,
  `N^U-P`, `:|%;%|`); `defpackage` with `(:use)`; `(declare (ignorable ...))`;
  `(declare (xargs ...))` (45 in the slice) is ignored without a warning.
  Nothing in the slice is rejected.
- **What JSCL gets silently wrong**: a ratio literal. `1/2` (3 occurrences,
  `rt/builtins.lisp` lines 140 and 246, in `%round-even` and the float
  rounding) is read as the **symbol** `1/2` and compiled as a variable
  reference, with no warning. The extractor must rewrite ratio literals
  (planned in §3; now confirmed necessary). No integer literal above 2^53
  in all 27 books (the large constants are computed with `expt`).
- **ACL2 functions referenced but undefined** (JSCL's end-of-unit
  warnings), slice (17): `ACL2-COUNT ALISTP ASSOC-EQUAL IFF IFIX LEN
  MAKE-ORD MEMBER-EQ MEMBER-EQUAL NATP NFIX POSP PUT-ASSOC-EQUAL RFIX TAKE
  TRUE-LISTP ZP`. All books (24 names): the same plus `HONS-COPY
  REMOVE-DUPLICATES-EQUAL SUBSETP-EQUAL UPDATE-NTH`, and the macros `MV`
  and `MV-LET` (compiled as function calls, which is also why `OK`, the
  first variable of the one `mv-let` in the `Instrs_ok` sequencer, is
  reported as a function). These are the shim's ACL2 layer (W2 item 2
  computes the list properly).
- Measured (slice): 703,297 bytes of Lisp → 677,960 bytes of JS, compile
  0.32 s, node load 20 ms (plus 159 ms for `jscl.js` itself). Chromium
  page 19 ms, Firefox page 30 ms; Worker loads fine in both.
- Calls in node: `W3T::$MIN 3 5` → 3. `W3T::$SUM (1 2 3)` stops at
  "Undefined function ACL2::TRUE-LISTP", as expected without the shim.

### Item 3: size, compile time, load time (2026-11-15)
Measured on **all** books (not projected: the full extraction takes 2 s).
`measure.sh` runs the slice, the full set, and the full set with
clause-chain flattening; raw output `data/w0-slice/measure.out`.

| | slice | all 27 books | all, flattened |
|---|---|---|---|
| defuns / top forms | 567 / 573 | 1,463 / 1,475 | 1,463 / 1,475 |
| Lisp (bytes) | 703,297 | 5,023,067 | 4,932,884 |
| JS (bytes) | 677,960 | 3,766,008 | 3,751,475 |
| JSCL compile (s) | 0.32 | 2.41 | 2.33 |
| max nesting depth | 217 | **1,010** | 111 |
| node load, default stack | 20 ms | **RangeError** | 102 ms |
| node load, `--stack-size=2000` | 20 ms | 142 ms | 104 ms |
| Chromium page / Worker | 19 ms / ok | **RangeError** / **RangeError** | 85 ms / 418 ms (incl. jscl.js) |
| Firefox page / Worker | 30 ms / ok | **too much recursion** (both) | 135 ms / 644 ms (incl. jscl.js) |

(`jscl.js` itself: 156-168 ms in node, 278-283 ms Chromium page, 357-376
ms Firefox page.) The 33 MB of source is mostly indentation: printed
compactly it is 5 MB.

- **Size and load are far below the limits** (50 MB JS, 60 s load):
  3.75 MB and about 0.1 s. Pruning (W2 item 5) is **not needed**; it was
  conditional on the projection exceeding the limits.
- **New finding: the JS parsers overflow on nesting.** The overflow is in
  parsing (node: `compileFunctionForCJSLoader`), before any code runs.
  Depth histogram of the full set: 14 forms deeper than 50, 9 than 100, 5
  than 200, 1 than 800. The deepest (1,010) is the `GRAM/BINSTR` clique
  (labelled by its first member `GRAM/BINSTR/REP32`): the instruction
  decoder, one alternative per opcode, each nested in the else branch of
  the previous one. Next: `STEP_READ` 269, `STEP_READ/SPLIT` 245,
  `INSTR_OK` 241, `$FREE_INSTR` 217 (217 still loads in both browsers).
- **Fix measured: clause-chain flattening**, a mechanical rewrite of the
  translator's clause chains
  `(LET ((%R Xi)) (DECLARE (IGNORABLE %R)) (IF %R (CAR %R) rest))` and the
  grammar form `(... (IF %R %R rest))` (one shape per chain, at least 3
  links) into one flat sequence
  `(LET ((%CHAIN X1)) (IF (NOT %CHAIN) (SETQ %CHAIN X2)) ... (IF %CHAIN (CAR %CHAIN) rest))`.
  Equivalent because each Xi is NIL or a non-NIL result and is evaluated in
  the same order; in the nested form Xi+1 is inside the previous `%R`
  binding (then NIL), so the chain stops at the first Xi that mentions
  `%R`. 104 chains flattened; max depth 1,010 → 111; all three loaders
  then work with default settings. `block`/`return-from` was rejected for
  this: JSCL compiles it to a JS `try`/`throw`
  (`src/compiler/compiler.lisp`, `define-compilation block`), a cost on
  every decode. W2 adopts this rewrite (new extractor entry, reason as
  above; listed in the plan's "Current state").

## Open questions
- Items 4 and 5 (recursion depth, option A cost).

## Data
- Items 2 and 3: `sh plan/wasm3-demo/notes/data/w0-slice/measure.sh` from
  the repo root inside `nix develop`, after `make -C translate gen
  SPEC=3.0` (writes `demo/build/w0/`; output saved as
  `data/w0-slice/measure.out`, run at 050fa11). The scripts:
  `extract-slice.lisp` + `run-extract.sh` (throwaway extractor),
  `pkgs.lisp`, `compile.lisp` + `run-compile.sh` (JSCL), `depth.js`
  (nesting histogram), `load.js` (node load and calls),
  `browser-load.mjs` (page and Worker, both browsers).
- `make -C demo check` inside `nix develop` (needs nothing else).
- `nix build .#jscl` rebuilds the JSCL package (about 1 min on an M-series
  Mac).
