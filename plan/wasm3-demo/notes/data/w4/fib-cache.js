// W4: call_indirect T7 line #72 (fib-i64(20) = 10946) disagreed with ACL2
// (node: assertion fails). Runs that command alone on call_indirect.0.wasm,
// with the shim's memoized ACL2-COUNT (list.js) and with an uncached exact
// walk swapped in (ACL2L.count is looked up at every call), and prints both
// results, step counts and times.
// Usage: node fib-cache.js BUILD DATA_DIR [fuel]
'use strict';
const path = require('path'), fs = require('fs');
const [build, dataDir, fuelArg] = process.argv.slice(2);
const jscl = require(path.resolve(build, 'jscl.js'));
require(path.resolve(build, 'wasm3.js'));
const L = require(path.resolve(__dirname, '../../../../../demo/driver/lisp.js'))(jscl);
const Cons = L.list([1]).constructor;
const N = globalThis.ACL2N;
function plainCount(x) {                       // exact, no cache, no recursion
  let s = 0n; const st = [x];
  while (st.length) {
    let y = st.pop();
    while (y instanceof Cons) { s += 1n; st.push(y.$$jscl_car); y = y.$$jscl_cdr; }
    if (typeof y === 'number') s += BigInt(Math.abs(y));
    else if (typeof y === 'bigint') s += y < 0n ? -y : y;
    else if (y instanceof N.Q) s += (y.n < 0n ? -y.n : y.n) + y.d;
    else if (y && y.stringp === 1) s += BigInt(y.length);
  }
  return s <= BigInt(Number.MAX_SAFE_INTEGER) ? Number(s) : s;
}
const bytes = L.list([...fs.readFileSync(path.join(dataDir, 'call_indirect.0.wasm'))]);
const fuel = fuelArg ? +fuelArg : L.NIL;
let steps = 0; const S = L.I.intern('STEP', 'W3T'); const f0 = S.fvalue; S.fvalue = function (...a) { steps++; return f0.apply(this, a); };
const cached = globalThis.ACL2L.count;
for (const [label, fn] of [['memoized count', cached], ['plain count', plainCount]]) {
  globalThis.ACL2L.count = fn;
  const [st, env] = L.toArray(L.fn('DEMO', 'LOAD-MODULE')(bytes, L.fn('DEMO', 'EMPTY-ENV')()));
  steps = 0; const t = Date.now();
  const [r] = L.toArray(L.fn('DEMO', 'INVOKE')(env, L.list([...Buffer.from('fib-i64')]), L.list([L.list([L.kw('I64'), 20])]), fuel));
  console.log(`W4-FIB ${label}: load ${L.show(st)}, fib-i64(20) -> ${L.show(r)}, ${steps} STEP calls, ${Date.now() - t} ms`);
}
