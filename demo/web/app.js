// demo/web/app.js: the page (plan/wasm3-demo W5). One view, the stepper
// (W5 item 4, D6 level 1): Step takes one `step` of the reduction relation
// and shows the configuration; Run to end goes on to the result under the
// fuel (or to a breakpoint), which is what the earlier Run mode did.
// WAT is turned into bytes here by the bundled wabt (D3: only the binary
// reaches the semantics); the semantics runs in worker.js, the native
// engine here.
'use strict';
(() => {
  const $ = id => document.getElementById(id);
  const ui = { example: $('example'), src: $('src'), msg: $('src-msg'), format: $('format'), exp: $('export'),
    args: $('args'), fuel: $('fuel'), stop: $('stop'), engine: $('engine'),
    step: $('step'), stepn: $('stepn'), n: $('n'), toend: $('toend'), restart: $('restart'), nextline: $('nextline'),
    printed: $('printed') };
  const breakpoints = new Set();       // printed line numbers (W6)
  let wabt = null, worker = null, ready = false, reqId = 0, running = null, info = null;
  let sess = null;                    // the session {startId, loadMs, totalMs, done}
  let autoStart = false;              // an example was loaded: start its session once the Worker is ready

  // --- left pane: the printed module or the editable source ------------------
  function setView(v) {
    $('source').dataset.view = v;
    $('tab-module').setAttribute('aria-selected', String(v === 'module'));
    $('tab-source').setAttribute('aria-selected', String(v === 'source'));
  }
  $('tab-module').onclick = () => setView('module');
  $('tab-source').onclick = () => setView('source');

  // --- worker --------------------------------------------------------------
  // window.demoLoad: load time of each Worker start (read by the smoke test)
  window.demoLoad = [];
  function startWorker() {
    ready = false; setButtons();
    ui.engine.dataset.state = 'loading'; ui.engine.textContent = 'semantics: loading…';
    const t0 = performance.now();
    worker = new Worker('worker.js');
    worker.onmessage = e => {
      const m = e.data;
      if (m.type === 'ready') {
        ready = true;
        const ms = performance.now() - t0;
        window.demoLoad.push({ workerMs: Math.round(m.loadMs), totalMs: Math.round(ms) });
        ui.engine.dataset.state = 'ready'; ui.engine.textContent = `semantics: ready (${(ms / 1000).toFixed(1)} s)`;
        setButtons();
        if (autoStart && !sess) beginSession();
      } else if (m.type === 'failed') {
        ui.engine.dataset.state = 'failed'; ui.engine.textContent = 'semantics: failed to load';
        ui.msg.textContent = 'Worker: ' + m.message;
      } else if (m.type === 'result' && running && m.id === running.id) {
        running = null; setButtons();
        showSem(m);
      } else if (m.type === 'state') {
        onState(m);
      }
    };
    worker.onerror = e => {
      e.preventDefault();
      ui.engine.dataset.state = 'failed'; ui.engine.textContent = 'semantics: worker error';
      if (running) { showSem({ status: 'error', message: e.message || 'worker error' }); running = null; }
      ui.msg.textContent = 'Worker: ' + (e.message || 'error');
      setButtons();
    };
  }
  function post(type, extra) {
    const id = ++reqId;
    running = { id, t0: performance.now() };
    worker.postMessage({ type, id, ...extra });
    setButtons();
    return id;
  }
  function setButtons() {
    const idle = ready && !running && !!info;
    ui.step.disabled = ui.stepn.disabled = ui.toend.disabled = ui.nextline.disabled = !idle || !!(sess && sess.done);
    ui.restart.disabled = !idle;
    ui.stop.disabled = !running;
  }

  // --- source -> bytes, exports -----------------------------------------
  function compile() {
    ui.msg.textContent = '';
    info = null;
    try {
      const src = ui.src.value;
      if (ModInfo.isWat(src) && !wabt) throw new Error('wabt is still loading');
      const bytes = ModInfo.toBytes(wabt, src);
      let fns = [];
      try { fns = ModInfo.exportsOf(bytes); } catch (e) { ui.msg.textContent = 'reading exports: ' + e.message; }
      info = { bytes, fns };
      ui.format.textContent = `${ModInfo.isWat(src) ? 'WAT → ' : 'hex → '}${bytes.length} bytes`;
      renderPrinted(Lines.print(wabt, bytes));       // the Module tab follows the source
    } catch (e) {
      ui.format.textContent = '';
      ui.msg.textContent = String(e.message || e).replace(/^parseWat failed:\s*/, '');
    }
    const keep = ui.exp.value;
    ui.exp.innerHTML = '';
    for (const f of info ? info.fns : []) ui.exp.add(new Option(`${f.name} (${f.params.join(' ')}) → ${f.results.join(' ') || '()'}`, f.name));
    if (info && info.fns.some(f => f.name === keep)) ui.exp.value = keep;
    renderArgs();
    endSession();
    setButtons();
  }
  function currentFn() { return info && info.fns.find(f => f.name === ui.exp.value); }
  function renderArgs(values) {
    const fn = currentFn();
    const old = [...ui.args.querySelectorAll('input')].map(i => i.value);
    ui.args.innerHTML = '';
    (fn ? fn.params : []).forEach((t, k) => {
      const l = document.createElement('label');
      l.textContent = `arg ${k} : ${t}`;
      const i = document.createElement('input');
      i.value = values ? (values[k] ?? '') : (old[k] ?? '');
      i.dataset.type = t;
      i.addEventListener('keydown', e => { if (e.key === 'Enter') stepAction('runToEnd'); });
      i.addEventListener('input', () => endSession());
      l.appendChild(i); ui.args.appendChild(l);
    });
  }
  function loadExample(id) {
    const ex = EXAMPLES.find(e => e.id === id);
    ui.example.value = id;
    ui.src.value = ex.source;
    compile();
    ui.exp.value = ex.export;
    renderArgs(ex.args);
    clearResults();
    setView('module');
    autoStart = !beginSession();         // examples start at step 0; edited source waits for a click
  }
  // the export, its arguments and the fuel, or null (with a message)
  function request() {
    compile();
    const fn = currentFn();
    if (!fn) { ui.msg.textContent = ui.msg.textContent || 'no exported function'; return null; }
    const args = [...ui.args.querySelectorAll('input')].map(i => ({ type: i.dataset.type, value: i.value }));
    try { args.forEach(a => parseArg(a.type, a.value)); } catch (e) { ui.msg.textContent = e.message; return null; }
    return { fn, args, fuel: Math.floor(Number(ui.fuel.value)) || 0 };
  }

  // --- results -----------------------------------------------------------
  const STATUS = { ok: 'returned', trap: 'trap', exception: 'uncaught exception', fuel: 'out of fuel',
    error: 'error', invalid: 'invalid module', malformed: 'malformed module', unlinkable: 'unlinkable',
    stopped: 'stopped', exhausted: 'resource exhausted', running: 'running…', stepping: 'stepping' };
  // canonical form of a result, for comparing the two sides (smoke test)
  const keyOf = r => r.status === 'ok' ? 'ok ' + r.values.map(v => `${v.type}:${v.bits}`).join(' ') : r.status;
  function valueHtml(r) {
    if (r.status === 'stepping') return '<span class="t">in progress</span>';
    if (r.status !== 'ok') return esc(r.message ? `${STATUS[r.status] || r.status}: ${r.message}` : STATUS[r.status] || r.status);
    if (!r.values.length) return '<span class="t">()</span>';
    return r.values.map(v => `<div><span class="t">${v.type}</span>${esc(v.text)}</div>`).join('');
  }
  const esc = s => String(s).replace(/[&<>]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' })[c]);
  const fmtMs = ms => ms < 0.1 ? '< 0.1 ms' : ms < 1 ? `${ms.toFixed(2)} ms` : ms < 1000 ? `${ms.toFixed(0)} ms` : `${(ms / 1000).toFixed(2)} s`;
  function showCard(side, r, steps, time, load) {
    const card = $(side);
    const busy = r.status === 'running' || r.status === 'stepping';
    card.dataset.state = busy ? 'running' : 'done';
    card.dataset.status = r.status;
    card.dataset.key = busy ? '' : keyOf(r);
    $(side + '-value').innerHTML = valueHtml(r);
    $(side + '-status').textContent = STATUS[r.status] || r.status;
    if (steps !== undefined) $(side + '-steps').textContent = steps;
    $(side + '-time').textContent = time;
    $(side + '-load').textContent = load ?? '—';
    showPrints(side, r.prints || []);
  }
  // lines printed by env.print_* (the print host); data-prints for the smoke test
  function showPrints(side, lines) {
    const ol = $(side + '-prints');
    ol.dataset.prints = JSON.stringify(lines);
    ol.innerHTML = lines.slice(-12).map(t => `<li>${esc(t)}</li>`).join('')
      + (lines.length > 12 ? `<li class="more">… ${lines.length - 12} earlier lines</li>` : '');
  }
  function showSem(r) {
    const steps = r.steps !== undefined ? r.steps.toLocaleString('en-US') : '—';
    let time = r.runMs !== undefined ? fmtMs(r.runMs) : r.elapsed !== undefined ? fmtMs(r.elapsed) : '—';
    if (r.perStep !== undefined) time += ` (${r.perStep.toFixed(2)} ms/step)`;
    const load = r.loadMs !== undefined ? fmtMs(r.loadMs) : undefined;
    $('sem').dataset.steps = r.steps ?? '';
    $('sem').dataset.ms = r.runMs ?? '';
    showCard('sem', r, steps, time, load);
  }
  function showNative(fn, args) {
    const n = runNative(info.bytes, fn, args, parseArg, showBits, { PRINT_TYPES, printLine });
    showCard('nat', n, undefined, n.runMs !== undefined ? fmtMs(n.runMs) : '—', fmtMs(n.loadMs));
    $('nat').dataset.ms = n.runMs ?? '';
  }
  function clearResults() {
    for (const s of ['sem', 'nat']) {
      const c = $(s); c.dataset.state = 'idle'; c.dataset.status = ''; c.dataset.key = '';
      $(s + '-value').textContent = '—'; $(s + '-status').textContent = '—'; $(s + '-time').textContent = '—'; $(s + '-load').textContent = '—';
      showPrints(s, []);
    }
    $('sem-steps').textContent = '—';
  }

  function stop() {
    if (!running) return;
    const elapsed = performance.now() - running.t0;
    worker.terminate();
    running = null;
    if (sess) { sess = null; clearStepView('The Worker was stopped; Restart begins again.'); }
    showSem({ status: 'stopped', message: `Worker ended after ${fmtMs(elapsed)}; a fresh one is loading`, elapsed });
    startWorker();
  }

  // --- the session ------------------------------------------------------------
  // loads the module and $invoke's the export: the view shows step 0
  function beginSession() {
    if (!ready || running || !info) return false;
    const q = request();
    if (!q) return false;
    autoStart = false;
    setView('module');
    const printed = Lines.print(wabt, info.bytes);
    renderPrinted(printed);
    const startId = post('start', { bytes: info.bytes, name: q.fn.name, args: q.args, fuel: q.fuel, printed: printed.text });
    sess = { startId, totalMs: 0, done: false, lastId: startId, prints: [] };
    showSem({ status: 'stepping', steps: 0 });
    showNative(q.fn, q.args);
    return true;
  }
  function endSession() { if (sess) { sess = null; clearStepView(); highlight(null); renderChain(null); setButtons(); } }
  function stepAction(type) {
    if (type !== 'restart' && ui.step.disabled) return;
    if (type === 'restart' || !sess) { if (!beginSession()) return; if (type === 'restart') return; }
    setView('module');
    const id = ++reqId;                  // queued behind a start, if one was just posted
    running = { id, t0: running ? running.t0 : performance.now() };
    worker.postMessage({ type, id, n: Math.max(1, Math.floor(Number(ui.n.value)) || 1), breakpoints: [...breakpoints] });
    if (type === 'runToEnd' || type === 'nextLine') { $('sem').dataset.state = 'running'; $('sem').dataset.status = 'running'; $('sem-status').textContent = STATUS.running; }
    setButtons();
  }
  function onState(m) {
    if (running && m.id === running.id) running = null;
    if (!sess || m.id < sess.startId) { setButtons(); return; }
    if (m.loadMs !== undefined) sess.loadMs = m.loadMs;
    sess.totalMs += m.ms || 0;
    sess.done = !!m.done;
    sess.prints.push(...(m.prints || []));
    renderView(m);
    highlight(m.line);
    renderChain(m.chain);
    if (m.done) {
      const perStep = m.steps ? sess.totalMs / m.steps : undefined;
      showSem({ ...m, runMs: sess.totalMs, loadMs: sess.loadMs, perStep, prints: sess.prints });
    } else {
      showSem({ status: 'stepping', steps: m.steps, runMs: sess.totalMs, loadMs: sess.loadMs, prints: sess.prints });
    }
    setButtons();
  }

  // W8: the rule chain of the step just taken, outermost first; each name
  // searches the SpecTec source (GitHub code search: the default branch,
  // so the pinned rev is shown next to it)
  const ruleUrl = name => 'https://github.com/search?type=code&q='
    + encodeURIComponent(`repo:WebAssembly/spec path:specification/wasm-3.0 "${name}"`);
  function renderChain(chain) {
    const el = $('sv-chain');
    el.dataset.chain = chain ? JSON.stringify(chain) : '';
    el.innerHTML = chain && chain.length
      ? chain.map(n => `<a href="${ruleUrl(n)}" target="_blank" rel="noopener" title="search for rule ${esc(n)} in specification/wasm-3.0">${esc(n)}</a>`).join(' <span class="sep">›</span> ')
      : '<span class="muted">— (no step taken yet)</span>';
  }

  // the printed module (W6): line numbers toggle breakpoints
  function renderPrinted(p) {
    $('pv-printer').textContent = p.printer === 'wabt' ? 'printed by wabt from the bytes'
      : `printed by the page's fallback printer (wabt: ${p.wabtError})`;
    ui.printed.innerHTML = p.text.split('\n').map((t, k) =>
      `<li data-line="${k + 1}"${breakpoints.has(k + 1) ? ' class="bp"' : ''}><span class="ln">${k + 1}</span><span class="code">${esc(t)}</span></li>`).join('');
    ui.printed.dataset.line = '';
  }
  ui.printed.addEventListener('click', e => {
    const ln = e.target.closest('.ln');
    if (!ln) return;
    const li = ln.parentElement, k = Number(li.dataset.line);
    if (breakpoints.has(k)) breakpoints.delete(k); else breakpoints.add(k);
    li.classList.toggle('bp', breakpoints.has(k));
  });
  function highlight(line) {
    ui.printed.dataset.line = line ?? '';
    const old = ui.printed.querySelector('li.cur');
    if (old) old.classList.remove('cur');
    if (line == null) return;
    const li = ui.printed.querySelector(`li[data-line="${line}"]`);
    if (!li) return;
    li.classList.add('cur');
    const box = ui.printed, top = li.offsetTop - box.offsetTop;
    if (top < box.scrollTop + 20 || top > box.scrollTop + box.clientHeight - 40) box.scrollTop = Math.max(0, top - box.clientHeight / 3);
  }

  // the configuration view
  function clearStepView(note) {
    const sv = $('stepview');
    sv.dataset.steps = ''; sv.dataset.done = ''; sv.dataset.status = '';
    $('sv-steps').textContent = '0';
    $('sv-nest').textContent = '';
    $('sv-instrs').innerHTML = `<li class="end">${esc(note || 'Step or Run to end starts the export from its first configuration.')}</li>`;
    $('sv-locals').innerHTML = '';
    $('sv-mem').innerHTML = ''; $('sv-mem').dataset.count = '0';
  }
  let prevLocals = [];
  function renderView(m) {
    const sv = $('stepview');
    sv.dataset.steps = m.steps ?? ''; sv.dataset.done = m.done ? 'yes' : ''; sv.dataset.status = m.status;
    $('sv-steps').textContent = (m.steps ?? 0).toLocaleString('en-US');
    const v = m.view;
    if (!v) { clearStepView(`${STATUS[m.status] || m.status}${m.message ? ': ' + m.message : ''}`); sv.dataset.done = 'yes'; sv.dataset.status = m.status; return; }
    $('sv-nest').innerHTML = v.nesting.length
      ? v.nesting.map(n => `<span class="${n.kind}" title="${n.kind === 'label' ? 'LABEL_' : 'FRAME_'} arity ${n.arity}; ${n.below} value(s) below, ${n.after} instr(s) after${n.cont ? '; continuation: ' + esc(n.cont) : ''}">${n.kind}{${n.arity}}</span>`).join('<span class="sep">›</span>')
      : 'top level';
    const li = (cls, t) => `<li class="${cls}" title="${esc(t)}">${esc(t)}</li>`;
    $('sv-instrs').innerHTML = v.stack.map(t => li('v', t)).join('')
      + (v.redex ? li('redex', v.redex) : li('end', m.done ? 'normal form: no step applies' : 'only values'))
      + v.rest.map(t => li('r', t)).join('') + (v.more ? li('more', `… ${v.more} more`) : '');
    $('sv-locals').innerHTML = v.locals.length
      ? v.locals.map((t, k) => `<li class="${m.advanced && prevLocals[k] !== undefined && prevLocals[k] !== t ? 'changed' : ''}"><span class="k">local ${k}</span><span class="val">${esc(t)}</span></li>`).join('')
      : '<li><span class="k">none</span></li>';
    prevLocals = v.locals;
    const mem = $('sv-mem'), hex = b => b === null ? '··' : b.toString(16).padStart(2, '0');
    $('sv-mem-what').textContent = m.advanced ? `changed by the last ${m.advanced === 1 ? 'step' : m.advanced.toLocaleString('en-US') + ' steps'}` : 'changed bytes';
    mem.dataset.count = String(v.mem.ranges.length);
    mem.innerHTML = v.mem.ranges.length
      ? v.mem.ranges.map(r => `<div class="row" data-addr="${r.addr}" data-new="${r.new.join(' ')}"><span class="addr">${v.mem.ranges.some(x => x.mem) ? `mem ${r.mem} ` : ''}0x${r.addr.toString(16).padStart(4, '0')}</span><span class="old">${r.old.map(hex).join(' ')}</span><span>→</span><span class="new">${r.new.map(hex).join(' ')}</span></div>`).join('')
        + (v.mem.more ? `<div class="none">… ${v.mem.more} more ranges</div>` : '')
      : `<div class="none">${m.advanced ? 'no byte changed' : 'initial configuration'}</div>`;
  }

  // --- wiring ---------------------------------------------------------------
  ui.stop.onclick = stop;
  ui.step.onclick = () => stepAction('step');
  ui.stepn.onclick = () => stepAction('stepN');
  ui.toend.onclick = () => stepAction('runToEnd');
  ui.nextline.onclick = () => stepAction('nextLine');
  ui.restart.onclick = () => { clearResults(); endSession(); stepAction('restart'); };
  ui.fuel.addEventListener('input', () => endSession());
  ui.exp.onchange = () => { renderArgs([]); clearResults(); endSession(); };
  ui.example.onchange = () => loadExample(ui.example.value);
  let timer = null;
  ui.src.addEventListener('input', () => { autoStart = false; clearTimeout(timer); timer = setTimeout(compile, 300); });
  ui.src.addEventListener('keydown', e => {
    if (e.key === 'Tab') { e.preventDefault(); document.execCommand('insertText', false, '  '); }
    if (e.key === 'Enter' && (e.ctrlKey || e.metaKey)) { clearTimeout(timer); stepAction('runToEnd'); }
  });

  // --- start ---------------------------------------------------------------
  for (const ex of EXAMPLES) ui.example.add(new Option(ex.title, ex.id));
  $('nat-engine').textContent = /Firefox\//.test(navigator.userAgent) ? 'SpiderMonkey' : /Chrome\//.test(navigator.userAgent) ? 'V8' : /Safari\//.test(navigator.userAgent) ? 'JavaScriptCore' : 'this browser';
  startWorker();
  window.demoWabt = WabtModule().then(w => { wabt = w; loadExample(EXAMPLES[0].id); return true; },
    e => { ui.msg.textContent = 'wabt failed to load: ' + e; return false; });
})();
