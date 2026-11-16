// W5 item 3: the page (build/web, `make web`) in headless Chromium and
// Firefox. Every example (and two more exports) runs through the UI (Run
// to end from a fresh session; the page has one view, the stepper); the
// semantics' result must equal the native WebAssembly result in the same
// browser. Also checks fuel (W5 item 2: factorial with fuel 50 is out of
// fuel after 50 steps) and Stop (a long run is stopped, a fresh Worker
// loads, and the next run works). W5 item 4: factorial stepped 100 steps
// and then run to its end takes as many steps as running it to its end
// straight away, with the same result; the GC example is stepped to its end one Step click at a time;
// the memory example shows the first changed bytes (address 4 := 01).
// One line per check per browser; exits non-zero on a mismatch, a failed
// check or a page error.
// Usage: node smoke.mjs BUILD_WEB_DIR. SHOT=<png>: screenshot after Run to end,
// SHOT_STEP=<png>: screenshot mid-run, SHOT_LINE=<png>: stepping
// with the line highlight (W6), SHOT_RULES=<png>: stepping with the rule
// chain (W8) (all Chromium).
// W8 item 2: the GC example's Step clicks each show a non-empty rule chain;
// print host: the print example prints the same lines on both sides, in
// one Run to end and in Step x5 requests, each line once.
// SMOKE_JSON=<file>: the measurements as JSON.
import path from 'node:path';
import fs from 'node:fs';
import { serve } from './serve.mjs';
import { BROWSERS, withPage, screenshot } from './browser.mjs';

const dir = path.resolve(process.argv[2] || path.join(path.dirname(new URL(import.meta.url).pathname), '../build/web'));
const require = (await import('node:module')).createRequire(import.meta.url);
const EXAMPLES = require(path.join(dir, 'examples.js'));
const RUNS = [
  ...EXAMPLES.map(e => ({ id: e.id, export: e.export, args: e.args })),
  { id: 'exception', export: 'unsafe', args: ['-7'] },
  { id: 'float', export: 'third', args: ['10'] },
];
const SHOT_RUN = { id: 'factorial', export: 'fac', args: ['20'] };
const TIMEOUT = 120000;

const srv = await serve([dir]);
let fail = 0;
const report = {};
const line = (b, ok, what) => { console.log(`W5-SMOKE ${b} ${ok ? 'PASS' : 'FAIL'} ${what}`); if (!ok) fail++; };

async function ready(page) {
  await page.waitForSelector('#engine[data-state="ready"]', { timeout: TIMEOUT });
  await page.waitForFunction(() => window.demoWabt && document.querySelector('#export').options.length > 0, null, { timeout: TIMEOUT });
}
async function runOne(page, r, fuel = 200000) {
  await page.selectOption('#example', r.id);
  await page.selectOption('#export', r.export);
  const inputs = await page.$$('#args input');
  for (let k = 0; k < inputs.length; k++) await inputs[k].fill(r.args[k] ?? '');
  await page.fill('#fuel', String(fuel));
  await page.click('#toend');
  await page.waitForSelector('#sem[data-state="done"]', { timeout: TIMEOUT });
  return page.evaluate(() => {
    const s = document.querySelector('#sem'), n = document.querySelector('#nat');
    return { sem: s.dataset.key, nat: n.dataset.key, steps: s.dataset.steps, ms: Number(s.dataset.ms),
      natMs: Number(n.dataset.ms), semText: document.querySelector('#sem-value').textContent,
      semPrints: document.querySelector('#sem-prints').dataset.prints, natPrints: document.querySelector('#nat-prints').dataset.prints };
  });
}

// --- stepping ----------------------------------------------------------------
const idle = page => page.waitForFunction(() => !document.querySelector('#restart').disabled, null, { timeout: TIMEOUT });
const sv = page => page.evaluate(() => {
  const v = document.querySelector('#stepview'), s = document.querySelector('#sem'), n = document.querySelector('#nat');
  return { steps: Number(v.dataset.steps), done: v.dataset.done === 'yes', status: v.dataset.status, sem: s.dataset.key, nat: n.dataset.key,
    redex: (document.querySelector('#sv-instrs .redex') || {}).textContent || null,
    mem: [...document.querySelectorAll('#sv-mem .row')].map(r => ({ addr: Number(r.dataset.addr), new: r.dataset.new })) };
});
// a fresh session at step 0 for run R
async function session(page, r) {
  await page.selectOption('#example', r.id);
  await page.selectOption('#export', r.export);
  const inputs = await page.$$('#args input');
  for (let k = 0; k < inputs.length; k++) await inputs[k].fill(r.args[k] ?? '');
  await page.fill('#fuel', '200000');
  await idle(page);
  await page.click('#restart');
  await page.waitForFunction(() => document.querySelector('#stepview').dataset.steps === '0', null, { timeout: TIMEOUT });
  await idle(page);
}
async function stepChecks(b, page, rep) {
  const runs = Object.fromEntries(rep.runs.map(r => [r.id + '/' + r.export, r]));
  rep.step = {};

  // factorial: Step x100 once, then Run to end; count and result as Run to end alone
  const fac = runs['factorial/fac'];
  await session(page, SHOT_RUN);
  await page.fill('#n', '100');
  await page.click('#stepn'); await idle(page);
  const after100 = (await sv(page)).steps;
  const t0 = Date.now();
  await page.click('#toend'); await idle(page);
  const toEndMs = Date.now() - t0;
  const end = await sv(page);
  const workerMs = await page.$eval('#sem', e => Number(e.dataset.ms));
  const facOk = after100 === 100 && end.done && end.steps === Number(fac.steps) && end.sem === fac.sem && end.sem === end.nat;
  rep.step.factorial = { after100, steps: end.steps, runSteps: Number(fac.steps), sem: end.sem, nat: end.nat, workerMs, toEndMs };
  line(b, facOk, `step mode fac(20): Step x100 -> ${after100} steps; Run to end -> ${end.steps} steps (straight Run to end ${fac.steps}), ${end.sem} (straight ${fac.sem}, native ${end.nat}); worker ${(workerMs / end.steps).toFixed(2)} ms/step`);

  // GC example stepped to its end, one click per step
  const gc = runs['gc/f'];
  await session(page, { id: 'gc', export: 'f', args: ['3', '4'] });
  const redexes = [], chains = [];
  let st = await sv(page), clicks = 0;
  const tc = Date.now();
  while (!st.done && clicks < 100) {
    redexes.push(st.redex);
    await page.click('#step'); clicks++;
    await idle(page);
    st = await sv(page);
    chains.push(JSON.parse((await page.$eval('#sv-chain', e => e.dataset.chain)) || '[]'));
  }
  const perClick = (Date.now() - tc) / clicks;
  const gcOk = st.done && st.steps === Number(gc.steps) && clicks === st.steps && st.sem === gc.sem && st.sem === st.nat;
  rep.step.gc = { clicks, steps: st.steps, runSteps: Number(gc.steps), sem: st.sem, nat: st.nat, msPerClick: perClick, redexes };
  const chained = chains.filter(c => c.length).length;
  rep.step.gcChains = chains;
  line(b, chained === clicks && clicks > 0, `W8 rule chains: ${chained}/${clicks} steps of gc f(3, 4) show a non-empty chain (last: ${(chains[chains.length - 1] || []).join(' › ')})`);
  line(b, gcOk, `step mode gc f(3, 4): ${clicks} Step clicks to the normal form, ${st.steps} steps (Run to end ${gc.steps}), ${st.sem} (native ${st.nat}); ${perClick.toFixed(0)} ms per click (UI round trip)`);

  // memory example: step until the first memory diff
  await session(page, { id: 'memory', export: 'squares', args: ['3'] });
  st = await sv(page);
  while (!st.done && st.mem.length === 0 && st.steps < 200) { await page.click('#step'); await idle(page); st = await sv(page); }
  const memOk = st.mem.length === 1 && st.mem[0].addr === 4 && st.mem[0].new === '1';
  rep.step.memory = { steps: st.steps, mem: st.mem };
  line(b, memOk, `step mode memory squares(3): first changed bytes after step ${st.steps}: ${JSON.stringify(st.mem)}`);
  if (b === 'chromium' && process.env.SHOT_STEP) {
    const kb = await screenshot(page, process.env.SHOT_STEP);
    console.log(`W5-SMOKE screenshot ${process.env.SHOT_STEP}: ${kb.toFixed(0)} KB`);
  }
}

// --- W6: printed module and line highlight ---------------------------------
// fac(3) stepped through the UI, one click per step: the highlighted line
// of every configuration must be the hand-written one (test/lines-expected.js).
// Then a breakpoint on `br 0` (line 21): Run to end stops after step 14,
// Next line goes on to step 15 (line 8, the loop).
const LINE_CASES = require('./lines-expected.js');
const curLine = page => page.$eval('#printed', e => {
  const cur = e.querySelector('li.cur');
  return { line: e.dataset.line === '' ? null : Number(e.dataset.line), cur: cur ? Number(cur.dataset.line) : null };
});
async function lineChecks(b, page, rep) {
  const c = LINE_CASES[0];
  await session(page, { id: c.example, export: c.export, args: c.args });
  const printer = await page.$eval('#pv-printer', e => e.textContent);
  const aid = await page.$eval('.pv-aid', e => e.offsetParent !== null && e.textContent);
  const got = [];
  let st = await sv(page), h = await curLine(page), consistent = true;
  got.push(h.line); consistent = consistent && h.line === h.cur;
  const t0 = Date.now();
  while (!st.done && got.length < 200) {
    await page.click('#step'); await idle(page);
    st = await sv(page); h = await curLine(page);
    got.push(h.line); consistent = consistent && h.line === h.cur;
  }
  const perClick = (Date.now() - t0) / (got.length - 1);
  const diffs = got.map((l, k) => l === c.lines[k] ? null : `#${k}: ${l} want ${c.lines[k]}`).filter(Boolean);
  const ok = diffs.length === 0 && got.length === c.lines.length && consistent && !!aid && /wabt/.test(printer);
  rep.lines = { got, perClick, printer, aid };
  line(b, ok, `W6 lines fac(3): ${got.length - diffs.length}/${c.lines.length} highlighted lines as written by hand (${printer}; label "${aid}"); ${perClick.toFixed(0)} ms per click${diffs.length ? '; ' + diffs.slice(0, 5).join(', ') : ''}`);

  await session(page, { id: c.example, export: c.export, args: c.args });
  await page.click('#printed li[data-line="21"] .ln');
  await page.click('#toend'); await idle(page);
  const atBp = { steps: (await sv(page)).steps, line: (await curLine(page)).line };
  await page.click('#nextline'); await idle(page);
  const next = { steps: (await sv(page)).steps, line: (await curLine(page)).line };
  const bpOk = atBp.steps === 14 && atBp.line === 21 && next.steps === 15 && next.line === 8;
  rep.breakpoint = { atBp, next };
  line(b, bpOk, `W6 breakpoint on line 21: Run to end stops after step ${atBp.steps} on line ${atBp.line} (want 14, 21); Next line -> step ${next.steps}, line ${next.line} (want 15, 8)`);
  if (b === 'chromium' && process.env.SHOT_LINE) {
    const kb = await screenshot(page, process.env.SHOT_LINE);
    console.log(`W5-SMOKE screenshot ${process.env.SHOT_LINE}: ${kb.toFixed(0)} KB`);
  }
  await page.click('#printed li[data-line="21"] .ln');       // breakpoint off again
}

// --- print host and W8 screenshot -------------------------------------------
async function printChecks(b, page, rep) {
  const prints = page => page.evaluate(() => ({ sem: document.querySelector('#sem-prints').dataset.prints,
    nat: document.querySelector('#nat-prints').dataset.prints }));
  const want = JSON.stringify(['print_i32(0)', 'print_i32(1)', 'print_i32(4)', 'print_i32(9)', 'print_f64(1 (0x3ff0000000000000))']);
  await session(page, { id: 'print', export: 'squares', args: ['4'] });
  await page.fill('#n', '5');
  let st = await sv(page), reqs = 0;
  while (!st.done && reqs < 100) { await page.click('#stepn'); await idle(page); st = await sv(page); reqs++; }
  const p = await prints(page);
  const ok = st.done && p.sem === want && p.nat === want;
  rep.prints = { step: p, requests: reqs, steps: st.steps };
  line(b, ok, `print host, stepping (${reqs} Step x5 requests, ${st.steps} steps): semantics ${p.sem}, native ${p.nat}`);
  if (b === 'chromium' && process.env.SHOT_RULES) {
    await session(page, { id: 'print', export: 'squares', args: ['4'] });
    await page.fill('#n', '26');
    await page.click('#stepn'); await idle(page);           // step 26: the second print_i32
    const kb = await screenshot(page, process.env.SHOT_RULES);
    console.log(`W5-SMOKE screenshot ${process.env.SHOT_RULES}: ${kb.toFixed(0)} KB`);
  }
}

try {
  for (const b of BROWSERS) {
    await withPage(b, async (page, errors) => {
      page.on('console', m => { if (m.type() === 'error') errors.push('console: ' + m.text()); });
      const rep = report[b] = { runs: [] };
      const t0 = Date.now();
      await page.goto(srv.url + 'index.html');
      await ready(page);
      rep.loadMs = Date.now() - t0;
      rep.worker = await page.evaluate(() => window.demoLoad[0]);
      line(b, errors.length === 0, `page ready in ${rep.loadMs} ms (Worker: wasm3.js + jscl.js ${rep.worker.workerMs} ms, ready message after ${rep.worker.totalMs} ms)`);

      for (const r of RUNS) {
        const g = await runOne(page, r);
        const ok = g.sem === g.nat && g.sem !== '' && g.semPrints === g.natPrints && errors.length === 0;
        rep.runs.push({ ...r, ...g, ok });
        line(b, ok, `${r.id}/${r.export}(${r.args.join(', ')}): semantics ${g.sem} [${g.steps} steps, ${g.ms.toFixed(0)} ms] native ${g.nat} [${g.natMs.toFixed(2)} ms]${g.semPrints !== '[]' ? `; prints ${g.semPrints} / native ${g.natPrints}` : ''}`);
      }

      // fuel: factorial(20) needs 240 steps
      const f = await runOne(page, SHOT_RUN, 50);
      line(b, f.sem === 'fuel' && f.steps === '50', `fuel: fac(20) with fuel 50 -> ${f.sem} after ${f.steps} steps`);
      rep.fuel = f;

      // stop: a run that takes far longer than the wait, stopped from the UI
      await page.selectOption('#example', 'factorial');
      await (await page.$('#args input')).fill('100000000');
      await page.fill('#fuel', '1000000000');
      await page.click('#toend');
      await page.waitForTimeout(1500);
      const before = await page.$eval('#sem', e => e.dataset.state);
      const ts = Date.now();
      await page.click('#stop');
      const stopped = await page.$eval('#sem', e => e.dataset.status);
      await ready(page);
      const reloadMs = Date.now() - ts;
      const again = await runOne(page, SHOT_RUN);
      const stopOk = before === 'running' && stopped === 'stopped' && again.sem === again.nat;
      line(b, stopOk, `stop: state before ${before}, after ${stopped}; fresh Worker ready in ${reloadMs} ms; then fac(20) ${again.sem}`);
      rep.stop = { before, stopped, reloadMs, again: again.sem };

      if (b === 'chromium' && process.env.SHOT) {
        await page.selectOption('#example', 'factorial');
        await runOne(page, SHOT_RUN);
        const kb = await screenshot(page, process.env.SHOT);
        console.log(`W5-SMOKE screenshot ${process.env.SHOT}: ${kb.toFixed(0)} KB`);
      }
      await stepChecks(b, page, rep);
      await lineChecks(b, page, rep);
      await printChecks(b, page, rep);
      line(b, errors.length === 0, `page errors: ${errors.length ? errors.join('; ') : 'none'}`);
    });
  }
} finally { srv.close(); }
if (process.env.SMOKE_JSON) fs.writeFileSync(process.env.SMOKE_JSON, JSON.stringify(report, null, 1));
console.log(`W5-SMOKE ${fail ? `${fail} FAILED` : 'all passed'}`);
process.exit(fail ? 1 : 0);
