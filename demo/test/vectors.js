// W3 item 2: the numeric and SIMD vectors of the ACL2 test books, run on the
// JSCL build with the books' own checking functions (extracted by name):
//   numerics: CHECK-VECTORS of t3-numerics-3.0 on numeric-vectors.lsp +
//             numeric-vectors-2.0.lsp (ACL2 count: 8,724, wasm3 M1)
//   simd:     CHECK-SIMD of t3-simd-3.0 on simd-vectors-3.0.lsp (1,008, of
//             which 480 relaxed; full profile 480/480)
// Usage: node vectors.js BUILD_DIR numerics|simd
'use strict';
const path = require('path'), fs = require('fs');
const build = path.resolve(process.argv[2]), which = process.argv[3];
const jscl = require(path.join(build, 'jscl.js'));
require(path.join(build, `test-${which}.js`));
const L = require('../driver/lisp.js')(jscl);
const I = L.I;
// JSON from demo/extract (lsp->json) -> Lisp values
function toLisp(x) {
  if (Array.isArray(x)) return L.list(x.map(toLisp));
  if (typeof x === 'number' || typeof x === 'bigint') return x;
  if (typeof x === 'string') return I.make_lisp_string(x);
  if (x.big !== undefined) return globalThis.ACL2N.big(x.big);
  if (x.sym !== undefined) return x.sym === 'NIL' ? L.NIL : x.sym === 'T' ? L.T : I.intern(x.sym, x.pkg);
  throw new Error('bad JSON value ' + JSON.stringify(x));
}
const read = f => JSON.parse(fs.readFileSync(path.join(build, 'lisp', 'data', f), 'utf8'));
const t0 = Date.now();
let ok = false;
if (which === 'numerics') {
  const v1 = read('numeric-vectors.json'), v2 = read('numeric-vectors-2.0.json');
  const [nok, bad] = L.toArray(L.fn('DEMO', 'CHECK-VECTORS')(toLisp(v1.concat(v2))));
  const n = v1.length + v2.length;
  console.log(`W3-VECTORS numerics: ${nok} of ${n} vectors agree (${v1.length} from 1.0, ${v2.length} 2.0-only), ${Date.now() - t0} ms`);
  for (const b of L.toArray(bad).slice(0, 8)) console.log('  BAD', L.show(b));
  ok = nok === n;
} else {
  const vs = read('simd-vectors-3.0.json');
  const [nok, bad, nfull, badfull] = L.toArray(L.fn('DEMO', 'CHECK-SIMD')(toLisp(vs)));
  const relaxed = vs.filter(v => v[0].includes('relaxed_')).length;
  console.log(`W3-VECTORS simd: ${nok} of ${vs.length} vectors agree (${relaxed} relaxed, deterministic profile); full profile ${nfull} of ${relaxed}; ${Date.now() - t0} ms`);
  for (const b of L.toArray(bad).slice(0, 6)) console.log('  BAD', L.show(b));
  for (const b of L.toArray(badfull).slice(0, 6)) console.log('  BAD-FULL', L.show(b));
  ok = nok === vs.length && nfull === relaxed;
}
process.exit(ok ? 0 : 1);
