// demo/web/semantics.js: runs a module on the ACL2-extracted WASM 3.0
// semantics (build/wasm3.js, through driver/glue.lisp) and converts values
// between JS and the semantics' encodings (plan/wasm3-demo W5 item 2).
// Used by worker.js (browser) and by node; needs makeLisp (driver/lisp.js).
//
// Argument encodings are those of t7's TO-VAL: (:I32 n) / (:I64 n) with n
// unsigned (mod 2^N), (:F32 bits) / (:F64 bits) with the IEEE bit pattern.
// Numbers given to Lisp are canonical for the shim (num.js): a JS number
// when |n| <= 2^53 - 1, else a BigInt.
'use strict';
function makeSemantics(jscl, makeLisp) {
  const L = makeLisp(jscl);
  const emptyEnv = L.fn('DEMO', 'EMPTY-ENV');
  const loadModule = L.fn('DEMO', 'LOAD-MODULE');
  const invoke = L.fn('DEMO', 'INVOKE');
  const fbits = L.fn('WRT', '%FBITS');

  // Step count: the conformance driver's RUN-STEPS calls W3T::STEP once per
  // step; STEP also calls itself on inner configurations (the context
  // rules), so only the outermost calls are counted. Compiled code calls
  // STEP through the symbol's function cell, so wrapping the cell sees
  // every call. A step is an outermost call that returns a configuration
  // (the last call, which returns NIL at the normal form, is not a step).
  // The wrapper does not change arguments or results.
  const stepSym = L.sym('W3T', 'STEP');
  const step0 = stepSym.fvalue;
  let depth = 0, steps = 0;
  stepSym.fvalue = function (...a) {
    depth++;
    let r;
    try { r = step0.apply(this, a); } finally { depth--; }
    if (depth === 0 && r !== L.NIL) steps++;
    return r;
  };

  const MAX = BigInt(Number.MAX_SAFE_INTEGER);
  const canon = b => (b <= MAX && b >= -MAX) ? Number(b) : b;
  const big = x => typeof x === 'bigint' ? x : BigInt(x);
  const kwName = x => (x && x.name !== undefined && x.package) ? x.name : null;
  const utf8 = s => [...new TextEncoder().encode(s)];
  const toLispArg = (type, bits) => L.list([L.kw(type.toUpperCase()), canon(bits)]);

  // a result value of the semantics -> {type, bits (string, for comparing
  // with the native engine), text (for display)}
  function fromVal(v) {
    const head = L.isCons(v) ? kwName(v.$$jscl_car) : null;
    const a = L.toArray(v);
    if (head === 'CONST') {
      const type = kwName(L.toArray(a[1])[0]).toLowerCase();
      const bits = type[0] === 'f' ? big(fbits(Number(WIDTH[type]), a[2])) : big(a[2]);
      return { type, bits: bits.toString(), text: showBits(type, bits) };
    }
    if (head === 'VCONST') {
      const bits = big(a[2]);
      return { type: 'v128', bits: bits.toString(), text: showV128(bits) };
    }
    if (head && head.startsWith('REF.')) {
      const kind = head.slice(4).toLowerCase().replace(/_addr$|_num$/, '');
      const rest = a.slice(1).map(x => L.show(x)).join(' ');
      return { type: 'ref', bits: kind === 'null' ? 'null' : 'ref', text: kind === 'null' ? 'ref.null' : `ref.${kind} ${rest}`.trim() };
    }
    return { type: '?', bits: L.show(v), text: L.show(v) };
  }

  // --- print host (plan W4 item 2, "a print for the page") ----------------
  // Every module is instantiated against an environment where "env" (not
  // "spectest": t7 looks that name up under a string key) is registered as a host module (DEMO::REGISTER-HOST): the signature
  // module below declares the functions, each export becomes a host
  // function, and globalThis.DEMOHOST answers the calls. The semantics asks
  // the host several times per step (length check, binding, the candidate
  // argument splits of both call_ref-hostfunc rules), so the host answers as
  // a pure function of (function, values): NONE for a call whose values do
  // not fit the signature, the empty result list for a print. The print is
  // recorded once per step and argument list (keyed by the step).
  //   (module (func (export "print")) (func (export "print_i32") (param i32))
  //     (func (export "print_i64") (param i64)) (func (export "print_f32") (param f32))
  //     (func (export "print_f64") (param f64)) (func (export "print_i32_f32") (param i32 f32))
  //     (func (export "print_f64_f64") (param f64 f64)))      (wabt 1.0.39, 165 bytes)
  const SPECTEST_SIG = '0061736d01000000011e0760000060017f0060017e0060017d0060017c0060027f7d0060027c7c0003080700010203040506075907057072696e740000097072696e745f6933320001097072696e745f6936340002097072696e745f6633320003097072696e745f66363400040d7072696e745f6933325f66333200050d7072696e745f6636345f66363400060a160702000b02000b02000b02000b02000b02000b02000b';
  const registerHost = L.fn('DEMO', 'REGISTER-HOST');
  let printSink = null;                       // {key() -> string, seen: Set, out: [line]}
  const chars = l => String.fromCharCode(...L.toArray(l));
  globalThis.DEMOHOST = {
    call(hf, vals, none) {
      const [mod, field] = L.toArray(hf).map(chars);
      const want = mod === 'env' ? PRINT_TYPES[field] : undefined;
      if (!want) return none;
      const vs = L.toArray(vals).map(fromVal);
      if (vs.length !== want.length || vs.some((v, k) => v.type !== want[k])) return none;
      if (printSink) {
        const key = `${printSink.key()}|${field}|${vs.map(v => v.bits).join(',')}`;
        if (!printSink.seen.has(key)) { printSink.seen.add(key); printSink.out.push(printLine(field, vs)); }
      }
      return L.NIL;                              // no results
    },
  };
  let env0 = null;
  function baseEnv() {
    if (!env0) {
      const bytes = L.list(SPECTEST_SIG.match(/../g).map(h => parseInt(h, 16)));
      const [st, e] = L.toArray(registerHost(emptyEnv(), L.list(utf8('env')), bytes));
      env0 = kwName(st) === 'OK' ? e : emptyEnv();
    }
    return env0;
  }

  function run(bytes, exportName, args, fuel) {
    const lispArgs = L.list(args.map(({ type, value }) => toLispArg(type, parseArg(type, value))));
    const prints = [];
    printSink = { key: () => String(steps), seen: new Set(), out: prints };
    try { return run1(bytes, exportName, lispArgs, fuel, prints); } finally { printSink = null; }
  }
  function run1(bytes, exportName, lispArgs, fuel, prints) {
    const t0 = now();
    steps = 0;
    const [st, env] = L.toArray(loadModule(L.list([...bytes]), baseEnv()));
    const loadSteps = steps, t1 = now();
    const status = kwName(st).toLowerCase();
    if (status !== 'ok') return { status, loadMs: t1 - t0, loadSteps, prints };
    steps = 0;
    printSink.key = () => 'run' + steps;
    const [r] = L.toArray(invoke(env, L.list(utf8(exportName)), lispArgs, fuel > 0 ? fuel : L.NIL));
    const t2 = now();
    const out = { status: 'ok', loadMs: t1 - t0, loadSteps, runMs: t2 - t1, steps, prints };
    if (L.isCons(r) || r === L.NIL) out.values = L.toArray(r).map(fromVal);
    else out.status = kwName(r).toLowerCase();                 // trap, exception, fuel, error
    return out;
  }
  const now = () => (typeof performance !== 'undefined' ? performance : Date).now();

  // --- Step mode (W5 item 4, D6 level 1) ---------------------------------
  // A session holds the configuration; DEMO::STEP-CONFIG is one top-level
  // STEP (as t7's RUN-STEPS takes it). After each request the next
  // configuration is computed ahead (and kept for the next step), so the
  // page knows when the current one is a normal form; that call is the one
  // RUN-STEPS makes too. FUEL bounds the STEP calls of the session as
  // *spec-fuel* bounds RUN-STEPS: n steps need n + 1 calls.
  const startInvoke = L.fn('DEMO', 'START-INVOKE');
  // W8: Step mode steps with STEP-RULES (STEP-CONFIG with the %RULE
  // recorder on), so every step taken has its rule chain, outermost first
  const stepRules = L.fn('DEMO', 'STEP-RULES');
  const finishConfig = L.fn('DEMO', 'FINISH-CONFIG');
  let sess = null;

  function start(bytes, exportName, args, fuel, printed) {
    sess = null;
    const lispArgs = L.list(args.map(({ type, value }) => toLispArg(type, parseArg(type, value))));
    const t0 = now();
    const loadPrints = [];
    printSink = { key: () => 'load' + steps, seen: new Set(), out: loadPrints };
    let st, env;
    try { [st, env] = L.toArray(loadModule(L.list([...bytes]), baseEnv())); } finally { printSink = null; }
    const status = kwName(st).toLowerCase();
    if (status !== 'ok') return { status, done: true, loadMs: now() - t0, prints: loadPrints };
    const [ok, c] = L.toArray(startInvoke(env, L.list(utf8(exportName)), lispArgs));
    if (kwName(ok) !== 'OK') return { status: 'error', done: true, loadMs: now() - t0 };
    sess = { env, c, shown: c, next: undefined, steps: 0, calls: 0, fuel: fuel > 0 ? fuel : 200000, done: false, status: 'running',
      chain: null, nextChain: null, nextPrints: [], prints: loadPrints };
    sess.map = printed ? { tree: LinesLib().parse(printed), levels: [], prev: null, conds: new Map() } : null;
    sess.where = mapStep(c);
    lookahead();
    const r = reply(0, 0);
    r.loadMs = now() - t0;
    return r;
  }
  function lookahead() {                       // sets sess.next, or ends the session
    if (sess.next !== undefined || sess.done) return;
    if (sess.calls >= sess.fuel) { sess.done = true; sess.status = 'fuel'; return; }
    sess.calls++;
    sess.nextPrints = [];
    printSink = { key: () => 'step' + sess.calls, seen: new Set(), out: sess.nextPrints };
    let n, ch;
    try { [n, ch] = L.toArray(stepRules(sess.c)); } finally { printSink = null; }
    if (n === L.NIL) { sess.done = true; sess.status = 'ok'; sess.nextPrints = []; }
    else { sess.next = n; sess.nextChain = L.toArray(ch).map(x => L.show(x).replace(/^"|"$/g, '')); }
  }
  // n steps (Infinity: to the normal form), then the view. OPTS (W6):
  // breakpoints, a list of printed lines: stop after a step that reaches
  // one; nextLine: stop after the first step that reaches a printed line
  // other than the current one (a step with no line does not stop).
  function advance(n, opts = {}) {
    if (!sess) return { status: 'error', done: true, message: 'no session' };
    const t0 = now();
    const bps = new Set(opts.breakpoints || []), from = sess.where ? sess.where.line : null;
    let k = 0, stopped = null;
    while (k < n && !sess.done) {
      sess.c = sess.next; sess.next = undefined; sess.steps++; k++;
      sess.chain = sess.nextChain; sess.prints.push(...sess.nextPrints);
      sess.where = mapStep(sess.c);
      const ln = sess.where ? sess.where.line : null;
      lookahead();
      if (ln !== null && bps.has(ln)) { stopped = 'breakpoint'; break; }
      if (opts.nextLine && ln !== null && ln !== from) { stopped = 'line'; break; }
    }
    const r = reply(k, now() - t0);
    if (stopped && !sess.done) r.stopped = stopped;
    return r;
  }
  function reply(k, ms) {
    const out = { status: sess.status, done: sess.done, steps: sess.steps, advanced: k, ms, view: view(sess.c, sess.shown),
      line: sess.where ? sess.where.line : null, fn: sess.where ? sess.where.fn : null,
      chain: sess.chain, prints: sess.prints };
    sess.shown = sess.c;
    sess.prints = [];
    if (sess.done && sess.status === 'ok') {
      const [r] = L.toArray(finishConfig(sess.c, sess.env));
      if (L.isCons(r) || r === L.NIL) out.values = L.toArray(r).map(fromVal);
      else out.status = kwName(r).toLowerCase();            // trap, exception
    }
    return out;
  }

  // the view model of a configuration (:|%;%| (:|%;%| store frame) instrs)
  const VALUE_HEADS = new Set(['CONST', 'VCONST', 'REF.I31_NUM', 'REF.NULL_ADDR', 'REF.STRUCT_ADDR', 'REF.ARRAY_ADDR',
    'REF.FUNC_ADDR', 'REF.EXN_ADDR', 'REF.HOST_ADDR', 'REF.EXTERN']);
  const headOf = x => L.isCons(x) ? kwName(x.$$jscl_car) : null;
  const isValue = x => VALUE_HEADS.has(headOf(x));
  const isLabel = h => h && h.startsWith('LABEL_');
  const isFrame = h => h && h.startsWith('FRAME_');
  const isHandler = h => h && h.startsWith('HANDLER_');
  const ctxKind = h => isLabel(h) ? 'label' : isFrame(h) ? 'frame' : isHandler(h) ? 'handler' : null;
  const field = (rec, k) => { for (const f of L.toArray(rec)) if (L.isCons(f) && kwName(f.$$jscl_car) === k) return f.$$jscl_cdr; return L.NIL; };
  const valText = v => { const r = fromVal(v); return r.type === 'ref' ? r.text : `${r.type} ${r.text}`; };
  const MAXI = 14;                                         // instructions shown after the redex

  function view(c, prev) {
    const [, z, instrs] = L.toArray(c);
    const [, store, frame0] = L.toArray(z);
    let level = L.toArray(instrs), frame = frame0;
    const nesting = [];
    let idx;
    for (;;) {
      idx = level.findIndex(x => !isValue(x));
      const h = idx >= 0 ? headOf(level[idx]) : null;
      if (!ctxKind(h)) break;
      const a = L.toArray(level[idx]);
      const e = { kind: ctxKind(h), arity: Number(a[1]), below: idx, after: level.length - idx - 1 };
      if (e.kind === 'frame') frame = a[2];
      else if (e.kind === 'label') e.cont = L.toArray(a[2]).length ? summary(L.toArray(a[2])) : '';
      nesting.push(e);
      level = L.toArray(a[a.length - 1]);
    }
    const stack = level.slice(0, idx < 0 ? level.length : idx).map(valText);
    const rest = idx < 0 ? [] : level.slice(idx + 1);
    const locals = L.toArray(field(frame, 'LOCALS')).map(l => L.isCons(l) ? valText(l.$$jscl_car) : 'unset');
    return {
      nesting, stack, locals,
      redex: idx < 0 ? null : instrText(level[idx]),
      rest: rest.slice(0, MAXI).map(instrText), more: Math.max(0, rest.length - MAXI),
      mem: memDiff(prev ? L.toArray(L.toArray(prev)[1])[1] : store, store),
    };
  }
  const summary = is => is.length === 1 ? instrText(is[0]) : `${instrText(is[0])} … (${is.length} instrs)`;

  // --- WAT line (W6, D6 level 2; display only, not part of the semantics)
  // The printed module (lines.js) gives, per function, the instructions
  // with their lines and the bodies of block/loop/if/try_table. A JS stack
  // of levels runs alongside the configuration's contexts (LABEL_, FRAME_,
  // HANDLER_, outermost first):
  // - When contexts appear, the redex of the step before made them: a call
  //   (CALL x, or CALL_REF / RETURN_CALL_REF with the function's address
  //   below it) makes FRAME_ and the LABEL_ of the body: the function's
  //   lines; BLOCK/LOOP make a LABEL_ over the body of their printed node
  //   (an IF first becomes a BLOCK of the branch taken, from the condition
  //   seen when IF was the redex); TRY_TABLE makes HANDLER_ and LABEL_.
  //   The innermost new context gets the body; the others only know
  //   their owner (function, try_table).
  // - When contexts disappear, the levels are dropped.
  // - Inside the innermost level the redex is the instruction at
  //   len(body) - len(remaining) - 1, remaining being what follows the
  //   redex: reduction consumes the body from the front, and what follows
  //   the redex is still the original tail (the redex itself may already
  //   be rewritten, e.g. CALL into CALL_REF, BR_IF into BR).
  // - Only values left in a level (it is about to be exited), or an
  //   exception on its way out (THROW_REF, which may first drop the rest
  //   of the level, so the tail rule would not hold): the line of the
  //   level's end (the block's `end`, the function's last line).
  const LinesLib = () => (typeof Lines !== 'undefined' ? Lines : require('./lines.js'));
  function contextPath(c) {
    let level = L.toArray(L.toArray(c)[2]), idx;
    const ctx = [];
    for (;;) {
      idx = level.findIndex(x => !isValue(x));
      const h = idx >= 0 ? headOf(level[idx]) : null;
      if (!ctxKind(h)) break;
      const a = L.toArray(level[idx]);
      ctx.push(ctxKind(h));
      level = L.toArray(a[a.length - 1]);
    }
    return { ctx, level, idx };
  }
  // the module function index of function address A (its instance's FUNCS)
  function funcIndex(c, a) {
    const store = L.toArray(L.toArray(c)[1])[1];
    const fi = L.toArray(field(store, 'FUNCS'))[Number(a)];
    if (!fi) return null;
    const k = L.toArray(field(field(fi, 'MODULE'), 'FUNCS')).findIndex(x => Number(x) === Number(a));
    return k < 0 ? null : k;
  }
  function mapStep(c) {
    const m = sess && sess.map;
    if (!m) return null;
    const { ctx, level, idx } = contextPath(c);
    if (ctx.length < m.levels.length) m.levels.length = ctx.length;
    else if (ctx.length > m.levels.length) m.levels.push(...created(m, ctx.slice(m.levels.length)));
    m.levels.forEach((lv, k) => { if (lv.kind !== ctx[k]) m.levels[k] = { kind: ctx[k] }; });
    const lv = m.levels[m.levels.length - 1];
    let line = null, node = null;
    const op = idx >= 0 ? headOf(level[idx]) : null;
    if (lv) {
      if (idx < 0 || op === 'THROW_REF') line = lv.endLine ?? null;
      else if (lv.nodes) { node = lv.nodes[lv.nodes.length - (level.length - idx - 1) - 1] || null; line = node ? node.line : null; }
      else line = lv.ownerLine ?? null;
    }
    const below = idx > 0 ? level[idx - 1] : null;
    let fnTarget = null;
    if (op === 'CALL') fnTarget = Number(L.toArray(level[idx])[1]);
    else if ((op === 'CALL_REF' || op === 'RETURN_CALL_REF') && headOf(below) === 'REF.FUNC_ADDR') fnTarget = funcIndex(c, L.toArray(below)[1]);
    if ((op === 'IF' || op === 'IFELSE') && node && headOf(below) === 'CONST') m.conds.set(node, Number(L.toArray(below)[2]) !== 0);
    m.prev = { op, node, fnTarget };
    let fn = null;
    for (let k = m.levels.length - 1; k >= 0 && fn === null; k--) if (m.levels[k].fn !== undefined) fn = m.levels[k].fn;
    return { line, fn };
  }
  function created(m, kinds) {
    const out = kinds.map(kind => ({ kind }));
    const p = m.prev;
    let owner = null;
    if (p && p.fnTarget !== null && m.tree.funcs[p.fnTarget]) {
      const F = m.tree.funcs[p.fnTarget];
      owner = { nodes: F.body, endLine: F.endLine, ownerLine: F.endLine, fn: p.fnTarget };
    } else if (p && p.node && /^(BLOCK|LOOP|TRY_TABLE)$/.test(p.op)) {
      const N = p.node;
      const body = N.kind === 'if' ? (m.conds.get(N) ? N.body : (N.else || [])) : N.body;
      owner = { nodes: body, endLine: N.endLine, ownerLine: N.line };
    }
    if (owner) out.forEach((o, k) => {
      if (k === out.length - 1) { o.nodes = owner.nodes; o.endLine = owner.endLine; }
      else { o.ownerLine = owner.ownerLine; o.endLine = owner.endLine; }
      if (owner.fn !== undefined) o.fn = owner.fn;
    });
    return out;
  }

  // WAT-like text of an instruction (display only)
  function instrText(x) {
    if (isValue(x)) { const r = fromVal(x); return r.type === 'ref' ? r.text : `${r.type}.const ${r.text}`; }
    if (!L.isCons(x)) return L.show(x).toLowerCase().replace(/^:/, '');
    const a = L.toArray(x), op = kwName(a[0]);
    if (!op) return L.show(x).toLowerCase();
    const o = op.toLowerCase();
    const typeOf = t => L.isCons(t) && kwName(t.$$jscl_car) ? kwName(t.$$jscl_car).toLowerCase() : null;
    if (/^(BINOP|UNOP|RELOP|TESTOP)$/.test(op) && typeOf(a[1])) {
      const p = L.toArray(a[2]);
      const name = kwName(p[0]) ? kwName(p[0]).toLowerCase() : simple(a[2]);
      const sx = p.length > 1 && L.isCons(p[1]) ? kwName(p[1].$$jscl_car) : null;
      return `${typeOf(a[1])}.${name}${sx === 'S' || sx === 'U' ? '_' + sx.toLowerCase() : ''}`;
    }
    if ((op === 'LOAD' || op === 'STORE') && typeOf(a[1])) {
      const off = Number(field(a[4], 'OFFSET'));
      return `${typeOf(a[1])}.${o}${a[2] !== L.NIL ? ' ' + simple(a[2]) : ''}${off ? ' offset=' + off : ''}`;
    }
    if (op === 'BLOCK' || op === 'LOOP') return `${o} … end (${L.toArray(a[2]).length} instrs)`;
    if (op === 'IF' || op === 'IFELSE') return `if … (then ${L.toArray(a[2]).length}, else ${L.toArray(a[3]).length} instrs)`;
    if (isLabel(op) || isFrame(op)) return `${isLabel(op) ? 'label' : 'frame'}{${Number(a[1])}} …`;
    return [o, ...a.slice(1).map(simple)].filter(s => s !== '').join(' ');
  }
  function simple(x) {
    if (typeof x === 'number' || typeof x === 'bigint') return String(x);
    if (x === L.NIL) return '';
    const k = kwName(x);
    if (k) return k.toLowerCase();
    const s = L.show(x).toLowerCase();
    return s.length <= 24 ? s : '…';
  }

  // bytes changed between two stores (all memories); the byte lists are
  // walked together and the walk stops where they share structure
  function memDiff(s0, s1) {
    const m0 = L.toArray(field(s0, 'MEMS')), m1 = L.toArray(field(s1, 'MEMS'));
    const out = [];
    let shown = 0, more = 0;
    m1.forEach((mem, k) => {
      if (mem === m0[k]) return;
      let a = m0[k] ? field(m0[k], 'BYTES') : L.NIL, b = field(mem, 'BYTES'), addr = 0, cur = null;
      while (L.isCons(b) && a !== b) {
        const x = L.isCons(a) ? a.$$jscl_car : undefined, y = b.$$jscl_car;
        if (x !== y) {
          if (cur && cur.addr + cur.new.length === addr && cur.new.length < 16) { cur.old.push(x); cur.new.push(y); }
          else if (shown < 8) { cur = { mem: k, addr, old: [x], new: [y] }; out.push(cur); shown++; }
          else more++;
        }
        a = L.isCons(a) ? a.$$jscl_cdr : a; b = b.$$jscl_cdr; addr++;
      }
    });
    return { more, ranges: out.map(d => ({ mem: d.mem, addr: d.addr, old: d.old.map(x => x === undefined ? null : Number(x)), new: d.new.map(Number) })) };
  }

  return { run, start, advance, parseArg, L };
}

// the env print functions (spectest-style) and the line a print shows (the same for the
// semantics and the native engine, native.js)
const PRINT_TYPES = { print: [], print_i32: ['i32'], print_i64: ['i64'], print_f32: ['f32'], print_f64: ['f64'],
  print_i32_f32: ['i32', 'f32'], print_f64_f64: ['f64', 'f64'] };
const printLine = (field, vs) => `${field}(${vs.map(v => v.text).join(', ')})`;

// display of a bit pattern of a scalar type (signed for integers)
function showBits(type, bits) {
  bits = BigInt(bits);
  if (type === 'i32') return String(BigInt.asIntN(32, bits));
  if (type === 'i64') return String(BigInt.asIntN(64, bits));
  const dv = new DataView(new ArrayBuffer(8));
  if (type === 'f32') { dv.setUint32(0, Number(bits), true); return fmtFloat(dv.getFloat32(0, true), bits, 8); }
  dv.setBigUint64(0, bits, true); return fmtFloat(dv.getFloat64(0, true), bits, 16);
}
function fmtFloat(f, bits, hexDigits) {
  const s = Number.isNaN(f) ? 'nan' : Object.is(f, -0) ? '-0' : String(f);
  return `${s} (0x${bits.toString(16).padStart(hexDigits, '0')})`;
}
function showV128(bits) {
  const lanes = [];
  for (let k = 0; k < 4; k++) lanes.push(String(BigInt.asIntN(32, (BigInt(bits) >> BigInt(32 * k)) & 0xffffffffn)));
  return `i32x4 ${lanes.join(' ')}`;
}

const WIDTH = { i32: 32n, i64: 64n, f32: 32n, f64: 64n };

// text -> BigInt bit pattern of the given type (i32/i64 signed or
// unsigned decimal or 0x hex; f32/f64 as a JS number literal, inf, nan,
// or 0x... for the raw bits)
function parseArg(type, text) {
  const s = String(text).trim();
  const w = WIDTH[type];
  if (!w) throw new Error(`argument type ${type} is not supported in the page`);
  if (s === '') throw new Error(`missing ${type} argument`);
  const m = 1n << w;
  if (type[0] === 'i') {
    if (!/^[-+]?(0x[0-9a-f_]+|[0-9_]+)$/i.test(s)) throw new Error(`not an ${type}: ${s}`);
    const neg = s[0] === '-';
    let v = BigInt(s.replace(/^[-+]/, '').replace(/_/g, ''));
    if (neg) v = -v;
    if (v >= m || v < -(m >> 1n)) throw new Error(`${s} is out of range for ${type}`);
    return ((v % m) + m) % m;
  }
  if (/^0x[0-9a-f]+$/i.test(s) && !/[.p]/i.test(s)) return BigInt(s) % m;    // raw bits
  const f = /^[-+]?inf(inity)?$/i.test(s) ? (s[0] === '-' ? -Infinity : Infinity)
    : /^[-+]?nan$/i.test(s) ? NaN : Number(s);
  if (Number.isNaN(f) && !/nan/i.test(s)) throw new Error(`not an ${type}: ${s}`);
  const dv = new DataView(new ArrayBuffer(8));
  if (type === 'f32') { dv.setFloat32(0, f, true); return BigInt(dv.getUint32(0, true)); }
  dv.setFloat64(0, f, true); return dv.getBigUint64(0, true);
}

if (typeof module !== 'undefined') module.exports = { makeSemantics, showBits, parseArg, PRINT_TYPES, printLine };
