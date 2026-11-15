// W0 item 5: time 10^6 ops each, plain JSCL against the prototype tower.
// Usage: node bench.js BUILD_DIR   (needs jscl.js and tower.js there)
const path = require('path');
require('./big.js');
const dir = path.resolve(process.argv[2]);
const jscl = require(path.join(dir, 'jscl.js'));
require(path.join(dir, 'tower.js'));
const f = n => jscl.internals.intern(n).fvalue;
const N = 1e6;
function time(name) {
  f(name)(N); f(name)(N);                         // warm up (JIT)
  let best = Infinity, r;
  for (let k = 0; k < 5; k++) { const t0 = process.hrtime.bigint(); r = f(name)(N); best = Math.min(best, Number(process.hrtime.bigint() - t0) / 1e6); }
  return [best, r];
}
for (const op of ['+', '*', 'FLOOR', 'LOGAND', 'ASH', 'ASH-R']) {
  const [p, rp] = time('PLAIN-' + op), [t, rt] = time('TOWER-' + op);
  console.log(`W0-NUM ${op.padEnd(6)} plain ${p.toFixed(2)} ms  tower ${t.toFixed(2)} ms  ratio ${(t / p).toFixed(2)}  results ${rp} ${rt} ${rp === rt ? 'equal' : 'DIFFER'}`);
}
// slow path sanity check (not timed)
console.log('W0-NUM slow path: 2^53+1 via t+ =', String(f('T+')(9007199254740991, 2)), ', t* 2^40*2^40 =', String(f('T*')(2 ** 40, 2 ** 40)));
