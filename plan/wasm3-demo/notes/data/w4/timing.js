// W4 item 4: ms per step of the JSCL build in node, on fixed invokes of the
// converted spec-test-3 modules. A step is one top-level STEP call (what
// t7's RUN-STEPS counts; STEP's own recursion into LABEL_/FRAME_ contexts is
// not counted). Each invoke runs once with the step counter (the warm-up),
// then 3 times without it; the median is reported. The same invokes run in ACL2 by timing-acl2.sh.
// Usage: node timing.js BUILD DATA_DIR
'use strict';
const path = require('path'), fs = require('fs');
const [build, dataDir] = process.argv.slice(2).map(a => path.resolve(a));
const jscl = require(path.join(build, 'jscl.js'));
require(path.join(build, 'wasm3.js'));
const L = require(path.resolve(__dirname, '../../../../../demo/driver/lisp.js'))(jscl);
const kw = L.kw;
const S = L.I.intern('STEP', 'W3T'), step0 = S.fvalue;
let depth = 0, steps = 0;
const counting = function (...a) { if (depth === 0) steps++; depth++; try { return step0.apply(this, a); } finally { depth--; } };

// [module file, export, args]: the invokes of timing-acl2.sh
const RUNS = [
  ['fac.0.wasm', 'fac-iter', [['I64', 25]]],
  ['fac.0.wasm', 'fac-rec', [['I64', 25]]],
  ['call_indirect.0.wasm', 'fac-i64', [['I64', 25]]],
  ['memory_redundancy.0.wasm', 'test_redundant_load', []],
  ['br_table.0.wasm', 'large', [['I32', 100]]],
];
for (const [file, fn, args] of RUNS) {
  const bytes = L.list([...fs.readFileSync(path.join(dataDir, file))]);
  const [st, env] = L.toArray(L.fn('DEMO', 'LOAD-MODULE')(bytes, L.fn('DEMO', 'EMPTY-ENV')()));
  const a = L.list(args.map(([t, v]) => L.list([kw(t), v])));
  const name = L.list([...Buffer.from(fn)]);
  // one run with the step counter (also the warm-up), then 3 timed runs without it
  S.fvalue = counting; steps = 0;
  let [r] = L.toArray(L.fn("DEMO", "INVOKE")(env, name, a, L.NIL));
  const n = steps; S.fvalue = step0;
  const times = [];
  for (let k = 0; k < 3; k++) {
    const t0 = process.hrtime.bigint();
    [r] = L.toArray(L.fn("DEMO", "INVOKE")(env, name, a, L.NIL));
    times.push(Number(process.hrtime.bigint() - t0) / 1e6);
  }
  times.sort((x, y) => x - y);
  const med = times[1];
  console.log(`W4-TIME ${file} ${fn}${JSON.stringify(args.map(x => x[1]))}: load ${L.show(st)}, result ${L.show(r).slice(0, 50)}, ${n} steps, ${med.toFixed(1)} ms, ${(med / n).toFixed(4)} ms/step`);
}
