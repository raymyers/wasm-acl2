// W4: time one spec-test-3 script command by command on the JSCL build
// (to find slow commands). Usage: node percmd.js BUILD DATA_DIR NAME [FROM]
'use strict';
const path = require('path'), fs = require('fs');
const [build, dataDir, name, from] = process.argv.slice(2);
const jscl = require(path.resolve(build, 'jscl.js'));
require(path.resolve(build, 'wasm3.js'));
const demo = path.resolve(__dirname, '../../../../../demo');
const L = require(path.join(demo, 'driver/lisp.js'))(jscl);
const readSexp = require(path.join(demo, 'driver/sexp.js'));
globalThis.DEMOIO = { readBytes(p) { const f = path.join(dataDir, String(p).replace(/^data-3\.0\//, '')); return fs.existsSync(f) ? L.list([...fs.readFileSync(f)]) : L.NIL; } };
const runCmd = L.fn('DEMO', 'RUN-CMD');
let e = L.fn('DEMO', 'SPECTEST-ENV')();
const cmds = L.toArray(readSexp(fs.readFileSync(path.join(dataDir, name + '.lsp'), 'utf8'), L));
cmds.forEach((c, k) => {
  const t = Date.now();
  const r = L.toArray(runCmd(c, e)); e = r[3];
  console.log(`#${k} ${Date.now() - t} ms ${L.show(r[0])} ${L.show(r[1])} ${L.show(c).slice(0, 100)}`);
});
