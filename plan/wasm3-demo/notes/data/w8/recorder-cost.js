// W8 item 1: the cost of the %RULE recorder. fac.0.wasm fac-iter(25) and
// call_indirect.0.wasm fac-i64(10): (a) INVOKE (Run mode: recorder off), and
// (b) START-INVOKE + STEP-RULES to the end (recorder on for every step), on
// the given build; median of 3 after a warm-up. Run on a build without the
// recorder (W5's) and with it (W8's) to compare (a).
// Usage: node recorder-cost.js BUILD DATA_DIR
'use strict';
const path = require('path'), fs = require('fs');
const [build, dataDir] = process.argv.slice(2).map(a => path.resolve(a));
const jscl = require(path.join(build, 'jscl.js'));
require(path.join(build, 'wasm3.js'));
const L = require(path.resolve(__dirname, '../../../../../demo/driver/lisp.js'))(jscl);
const hasRules = (() => { try { L.fn('DEMO', 'STEP-RULES')(L.NIL); return true; } catch (e) { return false; } })();   // an undefined JSCL function still has a callable fvalue (it signals)
const med = f => { f(); const t = []; for (let k = 0; k < 3; k++) { const t0 = process.hrtime.bigint(); f(); t.push(Number(process.hrtime.bigint() - t0) / 1e6); } return t.sort((a, b) => a - b)[1]; };
for (const [file, fn, n] of [['fac.0.wasm', 'fac-iter', 25], ['call_indirect.0.wasm', 'fac-i64', 10]]) {
  const [, env] = L.toArray(L.fn('DEMO', 'LOAD-MODULE')(L.list([...fs.readFileSync(path.join(dataDir, file))]), L.fn('DEMO', 'EMPTY-ENV')()));
  const name = L.list([...Buffer.from(fn)]), args = L.list([L.list([L.kw('I64'), n])]);
  const run = med(() => L.fn('DEMO', 'INVOKE')(env, name, args, L.NIL));
  let steps = 0, stepMs = null;
  if (hasRules) stepMs = med(() => {
    let [, c] = L.toArray(L.fn('DEMO', 'START-INVOKE')(env, name, args)); steps = 0;
    for (;;) { const [c2] = L.toArray(L.fn('DEMO', 'STEP-RULES')(c)); if (c2 === L.NIL) break; c = c2; steps++; }
  });
  console.log(`W8-COST ${path.basename(build)} ${file} ${fn}(${n}): run (recorder off) ${run.toFixed(1)} ms` +
    (hasRules ? `; step with chains ${stepMs.toFixed(1)} ms for ${steps} steps (${(stepMs / steps).toFixed(3)} ms/step)` : '; no recorder in this build'));
}
