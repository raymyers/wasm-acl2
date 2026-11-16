// W4 item 4: where node's time goes on a call-heavy invoke. Runs fac-i64(25)
// of spec-test-3 call_indirect.0.wasm (the slowest commands of the subset)
// and counts STEP calls, ACL2-COUNT calls (the %SIZE checks of
// rt/prelude.lisp) and the conses those calls walk.
// Usage: node size-cost.js BUILD DATA_DIR
'use strict';
const path = require('path'), fs = require('fs');
const [build, dataDir] = process.argv.slice(2).map(a => path.resolve(a));
const jscl = require(path.join(build, 'jscl.js'));
require(path.join(build, 'wasm3.js'));
const L = require(path.resolve(__dirname, '../../../../../demo/driver/lisp.js'))(jscl);
const bytes = L.list([...fs.readFileSync(path.join(dataDir, 'call_indirect.0.wasm'))]);
const [st, env] = L.toArray(L.fn('DEMO', 'LOAD-MODULE')(bytes, L.fn('DEMO', 'EMPTY-ENV')()));
const Cons = L.list([1]).constructor;
const wrap = (name, pkg, f) => { const s = L.I.intern(name, pkg); const g = s.fvalue; s.fvalue = function (...a) { f(...a); return g.apply(this, a); }; };
const name = L.list([...Buffer.from('fac-i64')]), args = L.list([L.list([L.kw('I64'), 25])]);
let t = Date.now();
let [r] = L.toArray(L.fn('DEMO', 'INVOKE')(env, name, args, L.NIL));
const plain = Date.now() - t;
let steps = 0, counts = 0, conses = 0;
wrap('STEP', 'W3T', () => steps++);
wrap('ACL2-COUNT', 'ACL2', x => {
  counts++;
  const stack = [x];
  while (stack.length) { let y = stack.pop(); while (y instanceof Cons) { conses++; if (y.$$jscl_car instanceof Cons) stack.push(y.$$jscl_car); y = y.$$jscl_cdr; } }
});
[r] = L.toArray(L.fn('DEMO', 'INVOKE')(env, name, args, L.NIL));
console.log(`W4-SIZE load ${L.show(st)}; fac-i64(25) = ${L.show(r)} in ${plain} ms (uninstrumented)`);
console.log(`W4-SIZE ${steps} STEP calls, ${counts} ACL2-COUNT calls, ${conses} conses walked (${(conses / counts).toFixed(0)} per call, ${(conses / steps).toFixed(0)} per STEP call)`);
