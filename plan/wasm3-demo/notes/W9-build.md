# Build integration and non-interference
- Milestone: W9 (build integration and non-interference)
- Date: 2026-11-15
- Repo commit: see the W9 commit (on top of a51de43)
- JSCL: 54c8849
- Status: final
- Feeds demo plan: W9
- Incorporated in demo plan: yes (W9)

## Summary
`make -C demo` builds the demo (`demo/build/wasm3.js` and the page in
`demo/build/web/`), `make -C demo check` runs every demo test, and the
flake output `packages.wasm3-demo` builds the page as a static directory
without the dev shell. After `make -C demo check`, `translate/` is
untouched, and the three ACL2 gates are green. `demo/README.md` explains
the build, what is derived from which file, and the shims. Publishing
(W9 item 4) is left to the user.

## Findings

### Build (item 1)
- `make -C demo` (target `all`): the toolchain check file, `js`
  (extraction from `translate/gen/wasm-3.0` and JSCL compilation) and
  `web`. It needs `translate/gen/wasm-3.0` (`make -C translate gen
  SPEC=3.0`, or `check-3.0`), which is not checked in.
- `make -C demo check`: `jscl-hello wabt-hello browser-hello check-extract vectors units host
  conformance-quick smoke lines chains`. `make -C demo all check`: exit 0
  in 65 s (`data/w9/demo-check.log`): numerics 8,724/8,724, SIMD
  1,008/1,008, units 119/119, host, 7,010/7,010 conformance commands,
  smoke in Chromium and Firefox, lines 234/234, chains 33/33. The full
  conformance subset (`make -C demo conformance`, 7,087/7,087, about 25
  min) stays out of `check` (W4).
- `packages.wasm3-demo` (`flake.nix`): a derivation over the repository
  (without `.git`, `plan/` and `build/` directories) that runs `make -C
  translate gen SPEC=3.0` (certifying only the translator) and `make -C
  demo web` in the Nix sandbox, and installs `demo/build/web` as `$out`
  (the site root). `nix build .#wasm3-demo`: exit 0, a 7.3 MB directory
  (`index.html`, the Worker, `jscl.js`, `wasm3.js`, `wabt.js`, the page
  scripts); the smoke test run against that directory (`node
  demo/test/smoke.mjs <result>`) passes in both browsers
  (`data/w9/nix-build.log`, `nix-smoke.log`).

### Non-interference (item 2)
After `make -C demo all check`, `git status --porcelain translate/` is
empty (0 lines; `check-extract` checks it on every run as well). The ACL2
gates on the same tree (`data/w9/gates.out`):

| gate | exit | time | earlier |
|---|---|---|---|
| `make -C translate check` | 0 | 7 s | 7 s (W4) |
| `check-2.0` | 0 | 144 s | 140 s (W7) |
| `check-3.0` | 0 | 293 s | 279 s (W7), 4 min 38 s (wasm3 M9) |

`translate/` changed only in W7, through the translator (D7).

### README (item 3)
`demo/README.md`: build and check commands; a table of every output in
`demo/build/` with its sources and the step that makes it; the
extractor; the shims (file, what, why); the driver; the page.

### Publishing (item 4)
Not done: the user decides where (GitHub Pages or other). The static
directory is `nix build .#wasm3-demo` (or `demo/build/web/` after
`make -C demo`); it needs no server beyond static files (the Worker loads
`jscl.js` and `wasm3.js` from the same directory).

## Data
`data/w9/`: the logs of the runs above.
