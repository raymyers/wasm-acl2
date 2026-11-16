// W4: run a script up to command K and print command K's full result
// (to inspect a disagreement). Usage: node one-cmd.js BUILD DATA_DIR NAME T7LINE
// T7LINE: index among the commands that print a T7-CMD line (as conformance.js #k).
'use strict';
const path = require('path'), fs = require('fs');
const [build, dataDir, name, want] = process.argv.slice(2);
const jscl = require(path.resolve(build, 'jscl.js'));
require(path.resolve(build, 'wasm3.js'));
const demo = path.resolve(__dirname, '../../../../../demo');
const L = require(path.join(demo, 'driver/lisp.js'))(jscl);
const readSexp = require(path.join(demo, 'driver/sexp.js'));
globalThis.DEMOIO = { readBytes(p) { const f = path.join(dataDir, String(p).replace(/^data-3\.0\//, '')); return fs.existsSync(f) ? L.list([...fs.readFileSync(f)]) : L.NIL; } };
const runCmd = L.fn('DEMO', 'RUN-CMD');
let e = L.fn('DEMO', 'SPECTEST-ENV')(), k = 0;
for (const c of L.toArray(readSexp(fs.readFileSync(path.join(dataDir, name + '.lsp'), 'utf8'), L))) {
  const isT7 = !['REGISTER'].includes(L.show(L.toArray(c)[0]).replace(':', ''));
  if (isT7 && k === +want) {
    const t = Date.now(); const r = L.toArray(runCmd(c, e));
    console.log(`W4-ONE #${k} ${L.show(c).slice(0, 200)}\n  -> kind ${L.show(r[0])} ok ${L.show(r[1])} detail ${L.show(r[2]).slice(0, 400)} (${Date.now() - t} ms)`);
    break;
  }
  const r = L.toArray(runCmd(c, e)); e = r[3]; if (isT7) k++;
}
