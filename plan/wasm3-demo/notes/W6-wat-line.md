# The stepper's WAT line (demo/web/lines.js, semantics.js)
- Milestone: W6 (items 1–3 and the exit)
- Date: 2026-11-15
- Repo commit: see the W6 commit (on top of 8b00a38)
- JSCL: 54c8849; wabt.js 1.0.39; Playwright 1.61.1 (flake)
- Status: final
- Feeds demo plan: W6, W9
- Incorporated in demo plan: yes (W6)

## Summary
In Step mode, the left panel shows the module as wabt prints it from the
bytes (flat, one instruction per line, with line numbers). The line of the
current configuration is highlighted. The highlight is labelled on the
page as "a display aid, not part of the semantics". The line is worked out
in the JS glue from the configuration's `LABEL_`/`FRAME_`/`HANDLER_`
nesting, as the plan describes. New controls: **Next line**, and
**breakpoints** (click a line number). Run to end, Step ×N and Next line
stop after a step that reaches a breakpoint.

The exit test steps every W5 example to its end in node (10 runs: the six
examples, plus `fac_rec`, `third`, `safe(5)` and `unsafe(-7)`). It checks
the line of every configuration against lists **written by hand** from the
printed text and the reduction rules (`demo/test/lines-expected.js`), and
does not record them from the mapper. All 10 runs agree, 234 of 234
configurations. The step count and the result equal Run mode's in every
run. Next line and the breakpoints pass too.

In headless Chromium and Firefox, the smoke test clicks fac(3) through
the UI one step at a time: 37 of 37 highlighted lines are as written by
hand. A breakpoint on `br 0` (line 21) stops Run to end after step 14;
Next line then goes to step 15, line 8.

Raw output: [data/w6/lines.log](data/w6/lines.log) (`node demo/test/lines.js
demo/build`, target `make -C demo lines`), [data/w6/smoke.log](data/w6/smoke.log),
[data/w6/smoke.json](data/w6/smoke.json). Screenshot:
`progress/04-W6-wat-line.png` (42 KB).

## Files
| file | role |
|---|---|
| `demo/web/lines.js` | `Lines.print(wabt, bytes)`: wabt's `readWasm` + `toText({foldExprs: false})`, or a fallback printer (below); `Lines.parse(text)`: per function, the instructions with their lines, and the bodies of block/loop/if/try_table with the line of their `else`/`end` |
| `demo/web/semantics.js` | the mapper (`mapStep`), run after every step of a Step-mode session; `advance(n, {breakpoints, nextLine})`; the view now also descends into `HANDLER_` |
| `demo/web/worker.js` | `start` takes the printed text; `nextLine`; breakpoints on `stepN`, `runToEnd`, `nextLine`; replies carry `line`, `fn`, `stopped` |
| `demo/web/app.js`, `index.html`, `style.css` | printed module panel (Step mode), highlight, breakpoints, Next line |
| `demo/web/examples.js` | factorial gains `fac_rec` (recursive: an `if`/`else` and a `call` per level), for the exit's "branch and call lines" |
| `demo/test/lines-expected.js` | the hand-written lines, with the conventions in its header |
| `demo/test/lines.js` | node test (`make -C demo lines`) |
| `demo/test/smoke.mjs` | the browser part (`lineChecks`); `SHOT_LINE=<png>` |

## Findings

### The mapping (display only)
- **Function**: when contexts appear, the redex of the step before made
  them. The function comes from `CALL x` (module function index `x`),
  or from `CALL_REF`/`RETURN_CALL_REF` with `(REF.FUNC_ADDR a)` below
  it. In that case `a` is looked up in its instance's `FUNCS` (the
  store's function instance → `MODULE` → `FUNCS`). In the 3.0 semantics,
  `call x` first becomes `(REF.FUNC_ADDR a) (CALL_REF t)`, and only the
  `CALL_REF` step makes `FRAME_(LABEL_(body))`. A JS stack of levels runs
  alongside the configuration's contexts, so each frame keeps its function.
- **Position**: in the innermost level, the redex is body instruction
  `len(body) − len(rest) − 1`, where `rest` is what follows the redex.
  The redex itself may already be rewritten (`CALL` → `CALL_REF`,
  `BR_IF` → `BR`, `IFELSE` → `BLOCK`), but what follows it is the
  original tail.
- **Blocks and loops** map through the `LABEL_` they become, with the
  body of their printed node. In the semantics, `if` is the instruction
  `IFELSE`. It first becomes a `BLOCK` of the branch taken; the mapper
  records the condition while `IFELSE` is the redex and picks that branch.
  `try_table` becomes `HANDLER_(LABEL_(body))`, seen in the
  configurations. The innermost new context gets the body; outer new
  contexts only know their owner (the function, the try_table).
- **Exits**: a level with only values left, or an exception on its way out
  (`THROW_REF`), shows the level's end line: the block's or if's `end`,
  or the function's last line. For exceptions this rule is needed:
  `THROW_REF` first drops the rest of the level in its own step (seen in
  `safe(-7)`, configurations 13 and 14), so the tail rule no longer holds
  there.
- Every non-constant instruction line of `fac` is visited
  (6 7 8 9 11 12 13 14 15 16 17 19 20 21 24), and so is every line of
  `fac_rec`'s branch and call path (26 28 29 32 33 35 36 37 38).
  Constants are values in the configuration and never a redex, so their
  lines (`i64.const`, `v128.const`) are never highlighted.

### Step counts and time (node, `data/w6/lines.log`; the machine was loaded)
| run | configurations | steps (= Run mode) | ms/step with mapping and view |
|---|---|---|---|
| fac(3) | 37 | 36 | 1.50 |
| fac_rec(2) | 22 | 21 | 1.29 |
| hypot(1.5, 2) | 12 | 11 | 1.27 |
| third(10) | 7 | 6 | 1.00 |
| squares(1) | 52 | 51 | 1.69 |
| gc f(3, 4) (fallback printer) | 18 | 17 | 1.06 |
| safe(-7) | 23 | 22 | 1.27 |
| safe(5) | 21 | 20 | 1.15 |
| unsafe(-7) | 17 | 16 | 0.88 |
| dot(5, 6, 7, 8) | 25 | 24 | 1.29 |

These node times include building the view model after every single
step.

Browsers (`data/w6/smoke.log`):
- Run to end of fac(20) in Step mode, with the mapping running on every
  step: 0.59 ms/step (Chromium), 0.96 ms/step (Firefox). W5 measured
  0.57 and 1.02 without the mapping.
- One Step click of fac(3) with the highlight: 31 ms (Chromium) and
  34 ms (Firefox) per click, UI round trip including Playwright.

### Limits
- **Formatting**: the page always shows wabt's flat print of the bytes.
  The user's own formatting survives only as far as flat WAT prints back
  the same. Folded expressions, names (`$n`), comments and blank lines
  are lost, because the binary does not carry them.
- **wabt 1.0.39 cannot read the GC example** ("expected valid local
  type", at the `(ref 0)` local). A fallback printer in `lines.js` prints
  the code section in the same flat format, and the page says which
  printer was used. It covers the MVP numeric, memory and control
  opcodes, calls, locals and globals, and the GC struct, array and i31
  opcodes. At any other opcode it stops printing that function, and that
  function has no lines.
- Lines are those of instructions. Configurations outside the module's
  code (the invocation before the first step, the final values) have no
  line. Constants are never highlighted (above).
- The mapping assumes one body instruction per printed line, which holds
  for every example. A step that replaces a frame in place
  (`return_call*`) keeps the old function's level; this is not exercised
  by the examples.
- A `br` to an outer label shows, on its intermediate step, the line of
  the block or loop being left (fac(3) configuration 32: line 8). A
  `return` shows the enclosing block's line while it leaves it.

## Open
- `make -C demo check` runs `lines` (node) and `smoke` (with the W6 line
  checks, both browsers) since the W6 commit. (The subagent that built the
  page ran both outside make, without ACL2; the W6 commit's `make check`
  ran them through make.)
- The Stop button wraps to its own row in Step mode at 1280×800
  (cosmetic).
