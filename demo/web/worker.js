// demo/web/worker.js: the ACL2-extracted WASM 3.0 semantics (JSCL build) in
// a Web Worker (plan/wasm3-demo §3): the page stays responsive, and Stop
// ends the Worker (W5 item 2). Protocol (every request carries an id that
// the reply repeats):
//   Run mode    {type: 'run', id, bytes, name, args, fuel}
//               -> {type: 'result', id, status, values, steps, loadMs, runMs}
//   Step mode   {type: 'start', id, bytes, name, args, fuel}  (load, $invoke)
//               {type: 'step', id}  {type: 'stepN', id, n}  {type: 'runToEnd', id}
//               {type: 'nextLine', id} (W6); stepN, runToEnd and nextLine take
//               breakpoints: [printed line] and stop after reaching one
//               -> {type: 'state', id, status, done, steps, advanced, ms, view,
//                   line, fn, stopped?, values?}
//   start also takes printed: the module text of lines.js (for the lines)
//   once at start: {type: 'ready', loadMs} or {type: 'failed', message}
'use strict';
const t0 = performance.now();
try {
  importScripts('wasm3.js');            // its prologue imports jscl.js
  importScripts('lisp.js', 'lines.js', 'semantics.js');
  const S = makeSemantics(self.jscl, makeLisp);
  postMessage({ type: 'ready', loadMs: performance.now() - t0 });
  const handlers = {
    run: m => ({ type: 'result', ...S.run(m.bytes, m.name, m.args, m.fuel) }),
    start: m => ({ type: 'state', ...S.start(m.bytes, m.name, m.args, m.fuel, m.printed) }),
    step: () => ({ type: 'state', ...S.advance(1) }),
    stepN: m => ({ type: 'state', ...S.advance(Math.max(1, m.n | 0), { breakpoints: m.breakpoints }) }),
    runToEnd: m => ({ type: 'state', ...S.advance(Infinity, { breakpoints: m.breakpoints }) }),
    nextLine: m => ({ type: 'state', ...S.advance(Infinity, { nextLine: true, breakpoints: m.breakpoints }) }),
  };
  onmessage = e => {
    const m = e.data, h = handlers[m.type || 'run'];
    let r;
    try { r = h ? h(m) : { type: 'state', status: 'error', done: true, message: `unknown request ${m.type}` }; }
    catch (err) {
      const msg = String(err && err.message || err);
      r = { type: m.type === 'run' || !m.type ? 'result' : 'state', done: true,
        status: /recursion|call stack|stack size/i.test(msg) ? 'exhausted' : 'error', message: msg };
    }
    postMessage({ ...r, id: m.id });
  };
} catch (err) {
  postMessage({ type: 'failed', message: String(err && err.message || err) });
}
