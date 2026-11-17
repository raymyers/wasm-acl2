// W3 item 3: shim unit tests. DEMO::UNIT-RESULTS (the forms of units.lsp,
// compiled with the shim) against the values ACL2 printed for the same
// forms (units-expected.json, written by demo/extract). The comparison is
// on printed values (driver/lisp.js SHOW), not on the shim's own EQUAL.
// Usage: node units.js BUILD_DIR
'use strict';
const path = require('path'), fs = require('fs');
const build = path.resolve(process.argv[2]);
const jscl = require(path.join(build, 'jscl.js'));
require(path.join(build, 'test-units.js'));
const L = require('../driver/lisp.js')(jscl);
const I = L.I;
function toLisp(x) {
  if (Array.isArray(x)) return L.list(x.map(toLisp));
  if (typeof x === 'number') return x;
  if (typeof x === 'string') return I.make_lisp_string(x);
  if (x.big !== undefined) return globalThis.ACL2N.big(x.big);
  if (x.dot !== undefined) { const xs = x.dot.map(toLisp); let l = xs.pop(); while (xs.length) l = new I.Cons(xs.pop(), l); return l; }
  if (x.q !== undefined) return globalThis.ACL2N.q(BigInt(x.q[0]), BigInt(x.q[1]));
  if (x.sym !== undefined) return x.sym === 'NIL' ? L.NIL : x.sym === 'T' ? L.T : I.intern(x.sym, x.pkg);
  throw new Error('bad JSON value ' + JSON.stringify(x));
}
const forms = fs.readFileSync(path.join(__dirname, 'units.lsp'), 'utf8');
const want = JSON.parse(fs.readFileSync(path.join(build, 'lisp', 'tests', 'units-expected.json'), 'utf8')).map(toLisp);
const got = L.toArray(L.fn('DEMO', 'UNIT-RESULTS')());
let ok = 0;
want.forEach((w, i) => {
  const a = L.show(got[i]), b = L.show(w);
  if (a === b) ok++; else console.log(`  BAD #${i}: got ${a.slice(0, 120)} want ${b.slice(0, 120)}`);
});
console.log(`W3-UNITS ${ok} of ${want.length} shim unit tests agree with ACL2`);
process.exit(ok === want.length && got.length === want.length ? 0 : 1);
