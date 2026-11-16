// W6 exit (node part): every W5 example is stepped to its end in Step mode
// with the printed module, and the line of each configuration is checked
// against the hand-written lists of lines-expected.js. Also checks that the
// step count equals Run mode's, the result equals Run mode's, the coverage
// lists (fac: every non-constant line; branch and call lines), and "Run to
// next line" and breakpoints on factorial.
// W8 exit (page part): every step of every W5 example has a non-empty rule
// chain (Step mode steps with DEMO::STEP-RULES). Print host: the print
// example prints the same lines in Run and in Step mode, once each.
// Usage: node lines.js BUILD_DIR (needs WABT_JS, from `nix develop`).
'use strict';
const path = require('path');
const build = path.resolve(process.argv[2] || path.join(__dirname, '../build'));
const jscl = require(path.join(build, 'jscl.js'));
require(path.join(build, 'wasm3.js'));
const web = path.join(__dirname, '../web');
const { makeSemantics } = require(path.join(web, 'semantics.js'));
const S = makeSemantics(jscl, require('../driver/lisp.js'));
const EXAMPLES = require(path.join(web, 'examples.js'));
const ModInfo = require(path.join(web, 'modinfo.js'));
const Lines = require(path.join(web, 'lines.js'));
const CASES = require('./lines-expected.js');

(async () => {
  const wabt = await require(process.env.WABT_JS)();
  let fail = 0, totalSteps = 0, totalChainless = 0;
  const say = (ok, what) => { console.log(`W6-LINES ${ok ? 'PASS' : 'FAIL'} ${what}`); if (!ok) fail++; };
  const setup = c => {
    const bytes = ModInfo.toBytes(wabt, EXAMPLES.find(e => e.id === c.example).source);
    const fn = ModInfo.exportsOf(bytes).find(f => f.name === c.export);
    return { bytes, args: fn.params.map((type, k) => ({ type, value: c.args[k] })), printed: Lines.print(wabt, bytes) };
  };
  for (const c of CASES) {
    const { bytes, args, printed } = setup(c);
    const run = S.run(bytes, c.export, args, 0);
    const t0 = Date.now();
    let r = S.start(bytes, c.export, args, 0, printed.text);
    const got = [r.line];
    let chainless = 0, links = 0;
    while (!r.done) { r = S.advance(1); got.push(r.line); if (!r.chain || !r.chain.length) chainless++; else links += r.chain.length; }
    totalSteps += r.steps; totalChainless += chainless;
    const ms = Date.now() - t0;
    const diffs = [];
    for (let k = 0; k < Math.max(got.length, c.lines.length); k++)
      if (got[k] !== c.lines[k]) diffs.push(`#${k}: got ${got[k]} want ${c.lines[k]}`);
    const sameRun = r.steps === run.steps && JSON.stringify(r.values) === JSON.stringify(run.values) && r.status === run.status;
    say(diffs.length === 0 && sameRun, `${c.example}/${c.export}(${c.args.join(', ')}) [${printed.printer}]: ${got.length - diffs.length}/${c.lines.length} lines as expected, ${r.steps} steps (Run mode ${run.steps}), ${r.status}${r.values ? ' ' + r.values.map(v => v.text).join(' ') : ''}, ${(ms / r.steps).toFixed(2)} ms/step with mapping`);
    for (const d of diffs.slice(0, 8)) console.log('  ' + d);
    say(chainless === 0, `${c.example}/${c.export}: rule chains on ${r.steps - chainless}/${r.steps} steps (${(links / Math.max(1, r.steps - chainless)).toFixed(1)} rules per chain)`);
    if (c.covers) {
      const missing = c.covers.filter(l => !got.includes(l));
      say(missing.length === 0, `${c.example}/${c.export}: covers lines ${c.covers.join(' ')}${missing.length ? '; missing ' + missing.join(' ') : ''}`);
    }
  }

  say(totalChainless === 0, `every step of every example has a non-empty chain: ${totalSteps - totalChainless}/${totalSteps} steps`);

  // print host: the print example, Run mode and Step mode; the lines are
  // written by hand from the program (i*i for i < 4, then 4 / 4)
  {
    const want = ['print_i32(0)', 'print_i32(1)', 'print_i32(4)', 'print_i32(9)', 'print_f64(1 (0x3ff0000000000000))'];
    const { bytes, args } = setup({ example: 'print', export: 'squares', args: ['4'] });
    const run = S.run(bytes, 'squares', args, 0);
    let r = S.start(bytes, 'squares', args, 0);
    const stepped = [...r.prints], at = [];
    let pc = 0;
    while (!r.done) { r = S.advance(1); if (r.prints.length) at.push(r.steps); stepped.push(...r.prints); if (!r.chain || !r.chain.length) pc++; }
    say(run.status === 'ok' && JSON.stringify(run.prints) === JSON.stringify(want), `print Run mode: ${JSON.stringify(run.prints)} (${run.steps} steps)`);
    say(r.status === 'ok' && r.steps === run.steps && JSON.stringify(stepped) === JSON.stringify(want), `print Step mode: ${JSON.stringify(stepped)}, printed at steps ${at.join(' ')} of ${r.steps}`);
    say(pc === 0, `print: rule chains on ${r.steps - pc}/${r.steps} steps`);
  }

  // Run to next line and breakpoints, fac(3)
  const fac = CASES[0], { bytes, args, printed } = setup(fac);
  S.start(bytes, 'fac', args, 0, printed.text);
  const seq = [];
  for (let k = 0; k < 6; k++) { const r = S.advance(Infinity, { nextLine: true }); seq.push(`${r.steps}:${r.line}`); }
  // from the start: line 6 after 1 step, 7, 8, 9, 11 (after the const), 12
  const wantSeq = ['1:6', '2:7', '3:8', '4:9', '5:11', '6:12'];
  say(seq.join(' ') === wantSeq.join(' '), `next line x6 from the start of fac(3): ${seq.join(' ')} (want ${wantSeq.join(' ')})`);
  // a run of the same line: fac(3) configurations 30, 31 are both line 12
  S.start(bytes, 'fac', args, 0, printed.text);
  S.advance(29);
  const nl = S.advance(Infinity, { nextLine: true });
  say(nl.steps === 30 && nl.line === 12, `next line from step 29 (line 11): stops at step ${nl.steps}, line ${nl.line} (want 30, 12)`);
  const nl2 = S.advance(Infinity, { nextLine: true });
  say(nl2.steps === 32 && nl2.line === 8, `next line from step 30 (line 12; 31 is 12 again): stops at step ${nl2.steps}, line ${nl2.line} (want 32, 8)`);
  // breakpoint on `br 0` (line 21): reached after steps 14 and 26, then not again
  S.start(bytes, 'fac', args, 0, printed.text);
  const hits = [];
  for (let k = 0; k < 4; k++) { const r = S.advance(Infinity, { breakpoints: [21] }); hits.push(r.done ? `end@${r.steps}` : `${r.steps}:${r.line}`); if (r.done) break; }
  say(hits.join(' ') === '14:21 26:21 end@36', `breakpoint at line 21, run to end x3: ${hits.join(' ')} (want 14:21 26:21 end@36)`);

  console.log(`W6-LINES ${fail ? fail + ' FAILED' : 'all passed'}`);
  process.exit(fail ? 1 : 0);
})();
