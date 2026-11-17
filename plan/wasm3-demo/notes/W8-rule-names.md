# Stepper, rule names (the %RULE recorder)
- Milestone: W8 (stepper, rule names)
- Date: 2026-11-15
- Repo commit: see the W8 commit
- JSCL: 54c8849
- Status: final
- Feeds demo plan: W8, W9
- Incorporated in demo plan: yes (W8)

## Summary
`shim/rule.lisp` makes W7's `(%RULE "Rel/rule-id" result)` a recorder:
it evaluates RESULT and, when the recorder is on, pushes the name. The
glue's `STEP-RULES` turns it on for one `STEP` call and reads that step's
chain, outermost rule first, from the end of the trace. On six small
programs (nop, `i32.add`, block/br, call/return, a trap, throw/catch) the
chain of every step equals the one written by hand from the spec: **33 of
33 steps** (`make -C demo chains`). The recorder costs nothing measurable
when off (Run mode). The page shows the chain of every step taken in
Step mode, each rule linked to a search in the SpecTec source; every step
of every W5 example has a non-empty chain (224/224 in node, 17/17 clicked
in both browsers).

## Findings

### Recorder (item 1)
- `shim/rule.lisp`: `(%RULE name result)` → `(let ((r result)) (when
  *rule-on* (push name *rule-trace*)) r)`. The tag fires when its rule's
  conclusion is built, after its premises (W7 note).
- Reading the chain (`driver/glue.lisp` `RULE-CHAIN`): a premise can
  succeed inside a rule that then fails on a later premise, so the trace
  also holds names of failed attempts. Read from the end: the last name of
  the Step family (`Step`, `Step_pure`, `Step_read`) is the outermost rule;
  while that rule has a Step-family premise, the family name recorded last
  before it is the rule of that premise (in such a rule the premise is the
  last family call before the conclusion). The rules with such a premise
  are read from the IL (`data/w8/step-premises.mjs`): `Step/pure`,
  `Step/read`, `Step/ctxt-instrs`, `Step/ctxt-label`, `Step/ctxt-handler`,
  `Step/ctxt-frame`, and none of `Step_pure` or `Step_read`; the glue
  descends only through these (`+STEP-DESCENDS+`), so a stale name from a
  failed attempt cannot be appended to a rule without a Step premise.
  Names of other relations (typing, `Expand`, ...) are skipped.
- Entry points (W5 item 4's split of `DO-ACTION`, plus W8):
  `START-INVOKE`, `STEP-CONFIG`, `FINISH-CONFIG`, `STEP-RULES c` →
  `(next-config chain)`.

### Cost (item 1)
`data/w8/recorder-cost.js` on the build without the recorder (W5's) and
with it (`data/w8/recorder-cost.out`), median of 3:

| run | no recorder | recorder, off (Run mode) | recorder on (Step, every step) |
|---|---|---|---|
| `fac.0` `fac-iter(25)` | 318.3 ms | 316.0 ms | 274.9 ms, 366 steps, 0.75 ms/step |
| `call_indirect.0` `fac-i64(10)` | 266.4 ms | 275.9 ms | 286.1 ms, 158 steps, 1.81 ms/step |

Off, one special-variable test per successful rule: within the noise on
`fac-iter`, +3.6% on `fac-i64(10)`. Run mode does not bind the recorder.

### Test (item 3)
`test/chains.js`: six programs in WAT (wabt), the expected chain of every
step written in the file from the spec's rules (how they follow is in
its header: `call_ref-func` makes the frame and label; a redex inside is
reached by `ctxt-frame`/`ctxt-label`, `ctxt-instrs` only when values
precede it or instructions follow it, `ctxt-handler` for a handler; then
`pure`/`read` and the rule, or a Step rule directly; `label-vals`,
`frame-vals` at the end).

| program | steps | result | chains |
|---|---|---|---|
| nop | 4 | (none) | 4/4 |
| `i32.add` | 4 | 3 | 4/4 |
| block/br | 5 | 7 | 5/5 |
| call/return | 7 | 5 | 7/7 |
| trap | 4 | trap | 4/4 |
| throw/catch | 9 | 3 | 9/9 |

The throw/catch chain, for example: `call_ref-func`; `Step_read/block`;
`Step_read/try_table`; `Step/throw` (under `ctxt-handler`, `ctxt-label`);
`Step_read/throw_ref-label`; `Step_read/throw_ref-handler-catch`;
`Step_pure/br-label-zero`; `label-vals`; `frame-vals`.

### Page (item 2)
- **Stepping**: Step mode (`demo/web/semantics.js`) takes every step with
  `DEMO::STEP-RULES` instead of `STEP-CONFIG`, so each step taken
  carries its chain. The chain belongs to the step just taken: the
  Step-mode session computes the next step ahead (W5 item 4), so the chain
  is kept with that next configuration until the step is taken. Run mode
  still calls `INVOKE` with the recorder off.
- **Display**: "Rules of the last step, outermost first", above the
  configuration view, e.g. `Step/ctxt-frame › Step/ctxt-label ›
  Step/ctxt-instrs › Step/ctxt-label › Step/ctxt-label › Step/ctxt-instrs
  › Step/call_ref-hostfunc-res` (the print example, step 26; screenshot
  `progress/05-W8-rule-names.png`, 50 KB). Each name links to a GitHub
  code search, `repo:WebAssembly/spec path:specification/wasm-3.0
  "<rule id>"`. **GitHub code search only covers the default branch**,
  not the pinned rev, so the rev is shown next to the chain as a link to
  `WebAssembly/spec/tree/943c5df…/specification/wasm-3.0`.
- **No direct file-and-line link**: `translate/il/wasm-3.0.il.sexp` has
  no source positions (no `.spectec` file names, no line numbers: 0
  matches), so the page cannot link a rule to its line.
- **Every step has a chain** (the exit). In node (`make -C demo lines`,
  `data/w8/page-lines.log`), every W5 example is stepped to its end
  with the page's code: 224/224 steps have a non-empty chain. The mean
  chain length ranges from 3.3 rules (`third`) to 8.5
  (`safe(-7)`). The print example also has a chain on 72/72 steps. In
  the browsers (`make -C demo smoke`, `data/w8/page-smoke.log`), the
  GC example clicked to its end shows a non-empty chain on 17/17 steps in
  Chromium and in Firefox; the last chain is
  `Step/pure › Step_pure/frame-vals`.
- **Cost in Step mode** (fac(20) to its end, Worker time per step, the
  same smoke check as W5):

  | | Chromium | Firefox |
  |---|---|---|
  | STEP-CONFIG (W6 run, `notes/data/w6/smoke.log`) | 0.59 ms | 0.96 ms |
  | STEP-RULES (this run, `data/w8/page-smoke.log`) | 0.86 ms | 1.32 ms |

  An earlier smoke run in this session gave 0.88 and 1.46 ms. The
  recorder conses a name per successful rule tag and reads the chain
  back after each step. One Step click (UI round trip) stays at 33 ms in
  both browsers.

## Data
`data/w8/`: `step-premises.mjs` / `.out`, `recorder-cost.js` / `.out`;
`make -C demo chains` (test); page: `page-lines.log` (`make -C demo lines`), `page-smoke.log` / `page-smoke.json` (`make -C demo smoke`).
