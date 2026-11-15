// W0 items 2-3: load jscl.js and a compiled slice in node, print the load
// times, then call a few extracted functions by name.
// Usage: node load.js DIR_WITH_JSCL_JS SLICE.js [PKG::NAME ARGS-JSON]...
const path = require('path');
const dir = path.resolve(process.argv[2]);
const t0 = process.hrtime.bigint();
const jscl = require(path.join(dir, 'jscl.js'));
const t1 = process.hrtime.bigint();
require(path.resolve(process.argv[3]));
const t2 = process.hrtime.bigint();
console.log(`W0-LOAD jscl.js ${Number(t1 - t0) / 1e6} ms, ${path.basename(process.argv[3])} ${Number(t2 - t1) / 1e6} ms`);
const I = jscl.internals;
for (let i = 4; i + 1 < process.argv.length; i += 2) {
  const [pkg, name] = process.argv[i].split('::');
  const args = JSON.parse(process.argv[i + 1]);
  const toLisp = x => Array.isArray(x) ? x.reduceRight((acc, e) => new I.Cons(toLisp(e), acc), I.intern('NIL', 'COMMON-LISP')) : x;
  let r;
  try { r = I.intern(name, pkg).fvalue(...args.map(toLisp)); } catch (e) { r = 'ERROR ' + (e.message || e); }
  console.log(`W0-CALL ${process.argv[i]} ${process.argv[i + 1]} => ${typeof r === 'object' && r && r.name ? r.name : String(r)}`);
}
