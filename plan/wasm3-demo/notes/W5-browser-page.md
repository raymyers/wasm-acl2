# The browser page: Run and Step mode (demo/web)
- Milestone: W5 (items 1–4)
- Date: 2026-11-15
- Repo commit: see the W5 commit (on top of b3da599)
- JSCL: 54c8849; wabt.js 1.0.39; Playwright 1.61.1 (flake)
- Status: final
- Feeds demo plan: W5, W6, W8
- Incorporated in demo plan: yes (W5)

## Summary
`make -C demo web` assembles the page in `demo/build/web/` (the files of
`demo/web/`, `driver/lisp.js`, the built `jscl.js` and `wasm3.js`, and
wabt's JS build as `wabt.js`: D8, no CDN). The semantics runs in a Web
Worker (`worker.js`); the page converts WAT with wabt, runs the module on
the browser's own `WebAssembly` next to it, and shows both results (D4).
`make -C demo smoke` runs every example through the UI in headless
Chromium and Firefox and requires the semantics' result to equal the
native one in the same browser: **all 8 runs agree in both browsers**,
plus the fuel and Stop checks (raw output: [data/w5/smoke.log](data/w5/smoke.log),
[data/w5/smoke.json](data/w5/smoke.json); script: `demo/test/smoke.mjs`).
Screenshot: `progress/02-W5-run-mode.png` (41 KB).

Step mode (item 4, D6 level 1) has Step, Step ×N, Run to end and Restart,
and a configuration view: the instructions with the redex highlighted,
the operand values, the locals of the innermost frame, the LABEL_/FRAME_
nesting, and the memory bytes changed by the last request. In both
browsers the smoke test:
- runs fac(20) to its end in Step mode in **240 steps, as in Run mode
  (240)**, with the same result as Run mode and native;
- steps the GC example to its end with **17 Step clicks (Run mode: 17
  steps)**;
- sees the memory example's first store as a one-byte diff (address 4,
  00 → 01, after step 28).

Raw output: [data/w5/smoke-step.log](data/w5/smoke-step.log),
[data/w5/smoke-step.json](data/w5/smoke-step.json). Screenshot:
`progress/03-W5-step-mode.png` (44 KB).

## Files
| file | role |
|---|---|
| `demo/web/index.html`, `style.css` | page; light/dark by CSS variables (system setting, or the ◐ button) |
| `demo/web/app.js` | UI: examples, WAT/hex → bytes, export picker, typed arg inputs, fuel, Run/Step tabs, Run, Step, Step ×N, Run to end, Restart, Stop, the two result cards, the configuration view |
| `demo/web/worker.js` | `importScripts('wasm3.js')` (its prologue imports `jscl.js`), then `lisp.js`, `semantics.js`. Protocol: `run` → `result` {status, values, steps, loadMs, runMs}; `start` (load, `$invoke`), `step`, `stepN` {n}, `runToEnd` → `state` {status, done, steps, advanced, ms, view, values} |
| `demo/web/semantics.js` | JS ↔ semantics values (item 2); calls `DEMO::EMPTY-ENV`, `LOAD-MODULE`, `INVOKE`, and for Step mode `START-INVOKE`, `STEP-CONFIG`, `FINISH-CONFIG`; step counter; the configuration view model and memory diff |
| `demo/web/native.js` | the same export on `WebAssembly`, results in the same `{type, bits, text}` form |
| `demo/web/modinfo.js` | WAT (wabt) or hex → bytes; exported functions with param/result types from the type/import/function/export sections (GC type encodings included) |
| `demo/web/examples.js` | the six examples |
| `demo/test/smoke.mjs` | items 3 and 4 |
| `demo/Makefile` | targets `web`, `smoke` (in `.PHONY`, not in `check`) |

## Findings

### Value conversion (item 2)
- Arguments are t7's `TO-VAL` encodings: `(:I32 n)`/`(:I64 n)` with n
  unsigned mod 2^N, `(:F32 bits)`/`(:F64 bits)` with the IEEE pattern.
  The UI takes integers signed or unsigned (decimal or `0x`), floats as JS
  literals, `inf`, `nan`, or `0x…` raw bits. Numbers handed to Lisp are
  canonical for the shim: a JS number up to 2^53 − 1, a BigInt above.
- Results: `(:CONST (:Ixx) n)` shown signed; `(:CONST (:Fxx) f)` goes
  through the extracted `WRT::%FBITS` to the bit pattern, shown as the
  value and its hex bits; `(:VCONST (:V128) n)` as i32x4 lanes;
  references symbolically (`ref.struct 0`, `ref.null`, …). The page
  compares on `type:bits` strings, so float results are compared bit for
  bit, not as JS numbers.
- v128 values cannot cross the JS API (a `TypeError` on the native side),
  so the SIMD example takes and returns i32. v128 arguments are not
  offered in the UI.

### Step count
Measured without a new Lisp entry point: compiled code calls `W3T::STEP`
through the symbol's function cell, so `semantics.js` wraps that cell.
A step is an outermost call (STEP also calls itself on inner
configurations) that returns a configuration; the final call that
returns NIL at the normal form is not counted. Check in node:
fac(20) takes 240 steps; fuel 240 gives `:FUEL`, fuel 241 completes
(t7's RUN-STEPS needs steps + 1 fuel, the last unit for seeing the
normal form); fuel 50 → `:FUEL` after 50 counted steps. Instantiation
steps (start function) are counted separately (`loadSteps`; 0 for all
examples).

### Examples (all agree with native in both browsers)
| example | export(args) | result | steps | Chromium | Firefox |
|---|---|---|---|---|---|
| factorial (i64) | fac(20) | 2432902008176640000 | 240 | 183 ms | 456 ms |
| float math | hypot(1.5, 2) | 2.5 (0x4004000000000000) | 11 | 7 ms | 22 ms |
| float math | third(10) (f32) | 3 (0x40400000) | 6 | 9 ms | 3 ms |
| memory load/store | squares(10) | 285 | 321 | 212 ms | 477 ms |
| GC struct (hex) | f(3, 4) | 15 | 17 | 8 ms | 15 ms |
| exception | safe(-7) (caught) | 993 | 22 | 24 ms | 23 ms |
| exception | unsafe(-7) (escapes) | uncaught exception | 16 | 7 ms | 11 ms |
| SIMD lane op | dot(5, 6, 7, 8) | 70 | 24 | 16 ms | 35 ms |

Times are the semantics' invoke only (`runMs`, in the Worker), from the
run recorded in `data/w5/smoke.log`; decode + validate + instantiate is
separate (`loadMs`, 6 ms for factorial in the screenshot). The machine
was running timing-sensitive ACL2 jobs on all 10 cores at the time, so
the absolute numbers are pessimistic and vary run to run (fac(20) in
Chromium: 161, 180 and 183 ms over three smoke runs; Firefox 362–456 ms).
About 0.7–0.8 ms per step in Chromium and 1.5–1.9 ms in Firefox for
factorial; node (same machine) 300–460 ms for the same run.
The native engine's times are at or below the browsers' timer resolution
(0.1 ms Chromium, 1 ms Firefox), so the page shows `< 0.1 ms` and the
note gives no ratio.

### Load times (Worker start until ready)
| | Chromium | Firefox |
|---|---|---|
| `importScripts` jscl.js + wasm3.js + makeSemantics, inside the Worker | 596–719 ms | 731–1,025 ms |
| `new Worker` → ready message, seen by the page | 612–742 ms | 808–1,203 ms |
| `page.goto` → engine ready and first example compiled by wabt | 921–996 ms | 1,292–1,874 ms |
| Stop → fresh Worker ready | 839–864 ms | 900–985 ms |

Ranges over the three smoke runs of this session (same loaded machine).

### Fuel and Stop (item 2)
- Fuel is the page's input (default 200,000, t7's `*spec-fuel*`), passed
  to `DEMO::INVOKE`; out of fuel shows "out of fuel" with the step count.
  Smoke: fac(20) with fuel 50 → `fuel` after 50 steps, both browsers.
- Stop terminates the Worker (`worker.terminate()`), shows "stopped" with
  the elapsed time and starts a fresh Worker. Smoke: fac(10^8) with fuel
  10^9, Stop after 1.5 s, state before `running`, after `stopped`; the
  fresh Worker is ready in 839/956 ms (Chromium/Firefox), and fac(20)
  then agrees with native again.

### What did not work, and limits
- **wabt 1.0.39 cannot parse GC instructions** (`struct.new`: "unexpected
  token … expected an instr"), with every feature flag on; exceptions
  (`try_table`, `throw`) and SIMD parse. The GC example is therefore given
  as hex bytes (hand-assembled, the WAT in comments); the page accepts hex
  for any module. A newer wabt (or another WAT converter) would be a flake
  change (D8).
- The page does not call wabt's `validate`: validation is the
  semantics' job (`Module_ok`, D3), so an ill-typed WAT module reaches
  both engines and each reports it (checked by hand in Chromium with the
  same ill-typed module given as hex: the semantics says `invalid module`,
  V8 gives its compile error).
- Native timing is too coarse to compare per example (above).
- Only exported functions are listed; modules with imports are
  `unlinkable` on both sides (the page provides no imports and no
  spectest module).
- The step counter relies on JSCL calling through the function cell
  (true for every call site of STEP in `wasm3-core.js`); if a future JSCL
  inlines self-calls, the count would need a glue entry point instead.

### Step mode (item 4)
- **Session.** `start` loads the module and calls `DEMO::START-INVOKE`
  (DO-ACTION's export lookup and `$invoke`); the view shows step 0. Each
  request advances with `DEMO::STEP-CONFIG`, then computes the next
  configuration ahead and keeps it for the next request. That is how the
  page knows when the shown configuration is a normal form; it is the same
  extra STEP call that RUN-STEPS makes to see the end. At the normal form,
  `FINISH-CONFIG` classifies the result as INVOKE does. The fuel bounds
  the STEP calls of the session as `*spec-fuel*` bounds RUN-STEPS (n
  steps need n + 1 calls), so both modes run out of fuel at the same point
  (node: fac(20) with fuel 240 → `fuel` after 240 steps; fuel 241 → ok
  after 240 steps; the same in both modes).
- **View model**, built in the Worker from the configuration
  `(:%;% (:%;% store frame) instrs)`. The walk descends through the
  first non-value instruction while it is a `LABEL_%{%}%` or
  `FRAME_%{%}%` context. At the innermost level, the values before the
  redex are the operands; then comes the redex, then at most 14 more
  instructions ("… k more"). Instructions are printed WAT-like for
  display only (`i32.ge_u`, `i32.store`, `struct.get 0 1`,
  `block … end (n instrs)`), with a generic lower-case form for anything
  else. Locals come from `(:LOCALS …)` of the innermost frame (`unset`
  for a non-defaultable local not yet set), and a local that changed is
  tinted. The nesting is a breadcrumb
  (`frame{1} › label{1} › label{0} › label{0}`); the tooltip gives the
  arity, the values below, the instructions after and the label's
  continuation.
- **Memory diff.** The page diffs the `:BYTES` list of every memory in
  the store's `:MEMS` against the previously shown configuration's store,
  so after Step ×N it covers all N steps. A memory record that is the
  same object is skipped. Otherwise the two byte lists are walked
  together and the walk stops where they share structure. Runs of changed
  bytes are grouped: at most 8 ranges of 16 bytes are shown, then
  "… k more".
- **Step counts, Step mode vs Run mode.** In the smoke test (both
  browsers): fac(20) takes 240 steps in both modes (Step ×100 gives 100,
  then Run to end 140 more); gc f(3, 4) takes 17 clicks = 17 steps =
  Run mode's 17. In node, with `S.advance(1)` to the end, every count and
  final value equals Run mode's: fac 240, gc 17, exception safe 22,
  exception unsafe 16 (`exception`), simd 24.
- **Time per step in Step mode** (`data/w5/smoke-step.log`; the machine
  was loaded, as above):

  | | Chromium | Firefox |
  |---|---|---|
  | Run to end: Worker time / steps (fac(20), 240 steps) | 0.57 ms | 1.02 ms |
  | Run mode, same page earlier: runMs / steps (fac(20)) | 0.70 ms (167 ms) | 1.31 ms (315 ms) |
  | one Step click, UI round trip (gc f(3, 4), mean of 17) | 33 ms | 34 ms |

  The Worker time covers only the STEP-CONFIG loop (the view is built
  after it). Step mode ran after Run mode in the same page, with a warm
  JIT, and the reverse order was not measured. So the lower Step-mode
  figure is not shown to come from Step mode itself. The click round trip
  includes Playwright's click and its polling for the idle state.
  An earlier smoke run in this session gave 0.56 / 1.03 ms per step and
  33 / 32 ms per click, with the same counts.

### Print host (W4 item 2's "print for the page")
- Every module on the page is instantiated against a base environment.
  In it, a host module **`env`** is registered with `DEMO::REGISTER-HOST`:
  `print`, `print_i32`, `print_i64`, `print_f32`, `print_f64`,
  `print_i32_f32`, `print_f64_f64` (the signature module is 165
  bytes of hex in `semantics.js`, with its WAT next to it). The name
  is `env`, not `spectest`: t7's `REGISTERED`, which the import
  resolution uses, looks `spectest` up under a string key of its own,
  so a host registered as `spectest` (char codes) is not found
  (`:UNLINKABLE`, tried).
- `globalThis.DEMOHOST.call(hf, vals, none)` answers as a pure
  function of (function, values). It returns `none` when the values
  do not fit the signature (the semantics also asks with the other
  argument splits of both `call_ref-hostfunc` rules), and the empty
  result list for a print. It records a print once per step and argument
  list: the key is the step counter (Run mode) or the session's STEP call
  (Step mode). In Step mode a print belongs to the step computed ahead,
  so it is shown when that step is taken.
- The native side gets the same `env` functions as JS imports.
  `native.js` prints the same text (`print_i32(9)`,
  `print_f64(1 (0x3ff0000000000000))`: the value and, for floats, the
  bits). Both result cards list the printed lines.
- Example "Print (host import)": `squares(4)` prints `i*i` for
  `i < 4`, then `4 / 4` as f64. Checks:
  - node (`make -C demo lines`): Run mode and Step mode both print
    exactly the five hand-written lines (Step mode at steps 12, 26, 40,
    54 and 70 of 72);
  - smoke, Chromium and Firefox: in Run mode the two sides print the same
    five lines; in Step mode (15 requests of Step ×5) the semantics
    prints the same five lines as native, each once
    (`notes/data/w8/page-smoke.log`).

## Open
- `make -C demo check` runs `smoke` (both browsers, Run and Step mode)
  since the W5 commit.
- The page supplies no imports. Host imports work in the driver
  (W4 `REGISTER-HOST`); wiring a `print` into the page is not done.
- The memory diff is against the previously shown configuration. After
  Run to end it shows everything the run changed, which can be many
  ranges (only 8 are shown).
