// W4 item 3: spec-test-3 scripts on the JSCL build, command by command,
// against the ACL2 run of the same scripts. The commands run through the
// conformance driver's own RUN-CMD (tests/spec/t7-lib-3.0.lisp, extracted
// by name: driver/glue.lisp); this file only reads the data, feeds the
// commands in order and compares each command's kind and pass/fail with
// ACL2's (T7-TRY / T7-CMD lines of results-3.0/<name>.out). A command that
// throws leaves the environment as it was, like ACL2's ld with
// :ld-error-action :continue; both sides then count it as a CRASH.
// Usage: node conformance.js BUILD_DIR DATA_DIR RESULTS_DIR NAME...
//   DATA_DIR    translate/tests/spec/data-3.0 (make -C translate spec-data SPEC=3.0)
//   RESULTS_DIR translate/tests/spec/results-3.0 (make -C translate spec SPEC=3.0)
'use strict';
const path = require('path'), fs = require('fs');
const [build, dataDir, resultsDir, ...names] = process.argv.slice(2).map((a, k) => k < 3 ? path.resolve(a) : a);
const jscl = require(path.join(build, 'jscl.js'));
require(path.join(build, 'wasm3.js'));
const L = require('../driver/lisp.js')(jscl);
const readSexp = require('../driver/sexp.js');

// READ-BYTES of the driver asks for "data-3.0/<file>"
globalThis.DEMOIO = {
  readBytes(p) {
    const f = path.join(dataDir, String(p).replace(/^data-3\.0\//, ''));
    return fs.existsSync(f) ? L.list([...fs.readFileSync(f)]) : L.NIL;
  },
};
const runCmd = L.fn('DEMO', 'RUN-CMD');
const e0 = L.fn('DEMO', 'SPECTEST-ENV')();
if (e0 === L.NIL) { console.log('W4 spectest module failed to instantiate'); process.exit(1); }

let allAgree = true, totalCmds = 0, totalSame = 0;
const summary = [];
for (const name of names) {
  const cmds = L.toArray(readSexp(fs.readFileSync(path.join(dataDir, name + '.lsp'), 'utf8'), L));
  const out = fs.readFileSync(path.join(resultsDir, name + '.out'), 'utf8');
  // ACL2's verdict per command, as summarize-3.0.sh reads it: every command
  // but :REGISTER prints "T7-TRY <kind>" (after the ACL2 prompt, so not at
  // the start of a line), then "T7-CMD <kind> <ok>"; a TRY with no CMD before
  // the next TRY (or T7-DONE) aborted on a Lisp resource: verdict CRASH,
  // a failure. Aligning by command, not by T7-CMD line, keeps a CRASH from
  // shifting the later lines.
  const want = []; let open = null;
  for (const line of out.split('\n')) {
    const t = line.match(/T7-TRY (\S+)/), c = line.match(/^T7-CMD (\S+) (\S+)/);
    if (t) { if (open) open.v = 'CRASH'; open = null; if (t[1] !== ':REGISTER') { open = { kind: t[1], v: null }; want.push(open); } }
    else if (c && open) { open.kind = c[1]; open.v = c[2]; open = null; }
    else if (/T7-DONE/.test(line) && open) { open.v = 'CRASH'; open = null; }
  }
  // An ACL2 run that did not end with T7-EXIT 0 (timeout: 124, or 137 when
  // KILL followed) holds only a prefix of the script: its last, unfinished
  // command is dropped, and node stops after as many commands ("ACL2 prefix").
  const exit = (out.match(/T7-EXIT (\d+)/g) || []).pop();
  const prefix = exit !== 'T7-EXIT 0';
  if (open && open.v === null) want.pop();
  const got = [];
  let e = e0, pass = 0;
  const t0 = Date.now();
  for (const c of cmds) {
    if (prefix && got.length >= want.length) break;
    const head = L.show(L.toArray(c)[0]);
    let r;
    try { r = L.toArray(runCmd(c, e)); } catch (err) { got.push({ kind: head, v: 'CRASH', err: String(err).slice(0, 80) }); continue; }
    const [kind, ok, detail, e2] = r;
    e = e2;
    if (kind !== L.NIL) { got.push({ kind: L.show(kind), v: ok === L.NIL ? 'NIL' : 'T', detail: L.show(detail).slice(0, 60) }); if (ok !== L.NIL) pass++; }
  }
  const ms = Date.now() - t0;
  // Same verdict: same kind and same pass/fail. A failure on both sides in a
  // different way (ACL2 CRASH, node a failed check, or the other way round)
  // is the same verdict; such commands are listed by number, never hidden.
  let same = 0; const diffs = [], bothFail = [];
  for (let k = 0; k < Math.max(got.length, want.length); k++) {
    const g = got[k], w = want[k];
    const ok = g && w && g.kind === w.kind && (g.v === w.v || (g.v !== 'T' && w.v !== 'T'));
    if (ok) { same++; if (g.v !== w.v) bothFail.push(`#${k} ${w.kind}: acl2 ${w.v}, node ${g.v}${g.detail ? ' (' + g.detail + ')' : ''}${g.err ? ' (' + g.err + ')' : ''}`); }
    else if (diffs.length < 5) diffs.push(`#${k}: node ${g ? g.kind + ' ' + g.v : '(none)'} / acl2 ${w ? w.kind + ' ' + w.v : '(none)'}`);
  }
  const agree = same === want.length && got.length === want.length;
  allAgree = allAgree && agree;
  totalCmds += want.length; totalSame += agree ? same : 0;
  const crashes = got.filter(g => g.v === 'CRASH').length;
  console.log(`W4-CONF ${name}: ${agree ? 'AGREE' : 'DIFFER'} ${same}/${want.length} commands${prefix ? ` (ACL2 prefix: its run ended with ${exit || 'no T7-EXIT'})` : ''} (node: ${got.length} commands, ${pass} pass, ${crashes} crash), ${ms} ms`);
  for (const b of bothFail) console.log('  fail on both sides, differently: ' + b);
  for (const d of diffs) console.log('  ' + d);
  summary.push({ name, agree, prefix, commands: want.length, nodeCommands: got.length, pass, crashes, bothFail, ms });
}
console.log(`W4-CONF total: ${allAgree ? 'all agree' : 'DISAGREEMENT'}; ${totalSame}/${totalCmds} commands in agreeing scripts`);
if (process.env.W4_JSON) fs.writeFileSync(process.env.W4_JSON, JSON.stringify(summary, null, 1));
process.exit(allAgree ? 0 : 1);
