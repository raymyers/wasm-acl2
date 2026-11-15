# W0 feasibility spike
- Milestone: W0 (feasibility spike, go/no-go)
- Date: 2026-11-15
- Repo commit: fbe1979 (+ the W0 commits)
- JSCL: jscl-project/jscl@54c88494e9f8f22e4c24c666e84aab7053f18cee
- Status: draft (item 1 done; items 2 to 5 pending)
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

## Open questions
- Items 2 to 5 (slice, size and load projection, recursion depth, option A
  cost).

## Data
- `make -C demo check` inside `nix develop` (needs nothing else).
- `nix build .#jscl` rebuilds the JSCL package (about 1 min on an M-series
  Mac).
