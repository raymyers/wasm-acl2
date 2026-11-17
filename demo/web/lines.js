// demo/web/lines.js: the printed module of Step mode (plan/wasm3-demo W6,
// D6 level 2; display only). The bytes are printed by wabt (wasm2wat
// style: flat, one instruction per line), and the text is parsed back into
// a tree per function: each instruction with its line, block/loop/if/
// try_table with their bodies and the line of their `end`. The mapping
// from configurations to lines (semantics.js) walks this tree, so it uses
// exactly the lines the page shows.
// wabt 1.0.39 cannot read every 3.0 module (GC: "expected valid local
// type"); then a small fallback printer below prints the code section in
// the same format (the page says which printer was used).
'use strict';
const Lines = (() => {
  const FEATURES = { exceptions: true, simd: true, reference_types: true, multi_value: true, bulk_memory: true,
    tail_call: true, extended_const: true, function_references: true, gc: true };

  // bytes -> {text, printer: 'wabt' | 'fallback', error?}
  function print(wabt, bytes) {
    let wabtError;
    try {
      const m = wabt.readWasm(bytes, { readDebugNames: true, ...FEATURES });
      try { return { text: m.toText({ foldExprs: false, inlineExport: false }).replace(/\n+$/, ''), printer: 'wabt' }; }
      finally { m.destroy(); }
    } catch (e) { wabtError = String(e.message || e).replace(/^readWasm failed:\s*/, '').trim(); }
    return { text: fallbackPrint(bytes), printer: 'fallback', wabtError };
  }

  // printed text -> {funcs: {index -> {index, line, endLine, body}}}; a
  // node is {line, op, kind ('instr'|'block'|'loop'|'if'|'try_table'),
  // body, else?, endLine?}. Lines are 1-based.
  function parse(text) {
    const lines = text.split('\n'), funcs = {};
    let fn = null, stack = null;
    lines.forEach((raw, k) => {
      const ln = k + 1;
      let s = raw.replace(/;;.*$/, '').trim();
      if (!fn) {
        const m = /^\(func\b(?:\s+\$\S+)?\s*(?:\(;(\d+);\))?/.exec(s);
        if (!m) return;
        const index = m[1] !== undefined ? Number(m[1]) : Object.keys(funcs).length;
        fn = { index, line: ln, endLine: ln, body: [] };
        funcs[index] = fn;
        stack = [fn.body];
        if (balance(s) <= 0) fn = null;          // no body: (func ... ) on one line
        return;
      }
      let closes = false;
      if (/\)$/.test(s) && balance(s) < 0) { closes = true; s = s.slice(0, -1).trim(); }
      if (s.startsWith('(local') || s.startsWith('(catch') || s === '') {
        // locals, or a try_table's catch clauses (immediates of the line above)
      } else {
        const op = s.split(/\s+/)[0];
        const cur = stack[stack.length - 1];
        if (op === 'block' || op === 'loop' || op === 'if' || op === 'try_table') {
          const node = { line: ln, op, kind: op, body: [] };
          cur.push(node); stack.push(node.body); node.parent = cur;
          (stack.nodes = stack.nodes || []).push(node);
        } else if (op === 'else') {
          const node = stack.nodes[stack.nodes.length - 1];
          node.else = []; node.elseLine = ln;
          stack[stack.length - 1] = node.else;
        } else if (op === 'end') {
          const node = stack.nodes.pop();
          node.endLine = ln; delete node.parent;
          stack.pop();
        } else {
          cur.push({ line: ln, op, kind: 'instr' });
        }
      }
      if (closes) { fn.endLine = ln; fn = null; }
    });
    return { funcs, lineCount: lines.length };
  }
  function balance(s) {                            // ( minus ) outside strings
    let b = 0, q = false;
    for (let i = 0; i < s.length; i++) {
      const c = s[i];
      if (q) { if (c === '\\') i++; else if (c === '"') q = false; }
      else if (c === '"') q = true; else if (c === '(') b++; else if (c === ')') b--;
    }
    return b;
  }

  // --- fallback printer (only what wabt cannot read; subset of opcodes) ----
  const NUM = {};
  'eqz eq ne lt_s lt_u gt_s gt_u le_s le_u ge_s ge_u'.split(' ').forEach((n, k) => { NUM[0x45 + k] = 'i32.' + n; NUM[0x50 + k] = 'i64.' + n; });
  'eq ne lt gt le ge'.split(' ').forEach((n, k) => { NUM[0x5b + k] = 'f32.' + n; NUM[0x61 + k] = 'f64.' + n; });
  'clz ctz popcnt add sub mul div_s div_u rem_s rem_u and or xor shl shr_s shr_u rotl rotr'.split(' ').forEach((n, k) => { NUM[0x67 + k] = 'i32.' + n; NUM[0x79 + k] = 'i64.' + n; });
  'abs neg ceil floor trunc nearest sqrt add sub mul div min max copysign'.split(' ').forEach((n, k) => { NUM[0x8b + k] = 'f32.' + n; NUM[0x99 + k] = 'f64.' + n; });
  ('i32.wrap_i64 i32.trunc_f32_s i32.trunc_f32_u i32.trunc_f64_s i32.trunc_f64_u i64.extend_i32_s i64.extend_i32_u '
    + 'i64.trunc_f32_s i64.trunc_f32_u i64.trunc_f64_s i64.trunc_f64_u f32.convert_i32_s f32.convert_i32_u f32.convert_i64_s '
    + 'f32.convert_i64_u f32.demote_f64 f64.convert_i32_s f64.convert_i32_u f64.convert_i64_s f64.convert_i64_u f64.promote_f32 '
    + 'i32.reinterpret_f32 i64.reinterpret_f64 f32.reinterpret_i32 f64.reinterpret_i64 i32.extend8_s i32.extend16_s '
    + 'i64.extend8_s i64.extend16_s i64.extend32_s').split(' ').forEach((n, k) => { NUM[0xa7 + k] = n; });
  NUM[0x00] = 'unreachable'; NUM[0x01] = 'nop'; NUM[0x0f] = 'return'; NUM[0x1a] = 'drop'; NUM[0x1b] = 'select'; NUM[0xd1] = 'ref.is_null';
  const MEM = { 0x28: 'i32.load', 0x29: 'i64.load', 0x2a: 'f32.load', 0x2b: 'f64.load', 0x2c: 'i32.load8_s', 0x2d: 'i32.load8_u',
    0x2e: 'i32.load16_s', 0x2f: 'i32.load16_u', 0x30: 'i64.load8_s', 0x31: 'i64.load8_u', 0x32: 'i64.load16_s', 0x33: 'i64.load16_u',
    0x34: 'i64.load32_s', 0x35: 'i64.load32_u', 0x36: 'i32.store', 0x37: 'i64.store', 0x38: 'f32.store', 0x39: 'f64.store',
    0x3a: 'i32.store8', 0x3b: 'i32.store16', 0x3c: 'i64.store8', 0x3d: 'i64.store16', 0x3e: 'i64.store32' };
  const IDX1 = { 0x0c: 'br', 0x0d: 'br_if', 0x10: 'call', 0x12: 'return_call', 0x20: 'local.get', 0x21: 'local.set', 0x22: 'local.tee',
    0x23: 'global.get', 0x24: 'global.set', 0x08: 'throw', 0x14: 'call_ref', 0x15: 'return_call_ref', 0xd2: 'ref.func' };
  const GC = { 0: ['struct.new', 1], 1: ['struct.new_default', 1], 2: ['struct.get', 2], 3: ['struct.get_s', 2], 4: ['struct.get_u', 2],
    5: ['struct.set', 2], 6: ['array.new', 1], 7: ['array.new_default', 1], 11: ['array.get', 1], 12: ['array.get_s', 1],
    13: ['array.get_u', 1], 14: ['array.set', 1], 15: ['array.len', 0], 28: ['ref.i31', 0], 29: ['i31.get_s', 0], 30: ['i31.get_u', 0] };
  const VT = { 0x7f: 'i32', 0x7e: 'i64', 0x7d: 'f32', 0x7c: 'f64', 0x7b: 'v128', 0x70: 'funcref', 0x6f: 'externref' };

  function fallbackPrint(bytes) {
    let p = 8;
    const u8 = () => bytes[p++];
    const uleb = () => { let r = 0n, s = 0n, b; do { b = bytes[p++]; r |= BigInt(b & 0x7f) << s; s += 7n; } while (b & 0x80); return r; };
    const sleb = () => { let r = 0n, s = 0n, b; do { b = bytes[p++]; r |= BigInt(b & 0x7f) << s; s += 7n; } while (b & 0x80); if (b & 0x40) r -= 1n << s; return r; };
    const n = () => Number(uleb());
    const valtype = () => { const b = u8(); if (b === 0x64 || b === 0x63) { const h = sleb(); return `(ref ${b === 0x63 ? 'null ' : ''}${h >= 0 ? h : 'abs'})`; } return VT[b] || `0x${b.toString(16)}`; };
    const out = ['(module'];
    const types = MODINFO_TYPES(bytes), funcTypes = [];
    let imported = 0;
    while (p < bytes.length) {
      const id = u8(), size = n(), end = p + size;
      if (id === 2) { const c = n(); for (let k = 0; k < c; k++) { p += n(); p += n(); const kind = u8(); if (kind === 0) { n(); imported++; } else { p = end; break; } } }
      if (id === 3) { const c = n(); for (let k = 0; k < c; k++) funcTypes.push(n()); }
      if (id === 10) {
        const c = n();
        for (let f = 0; f < c; f++) {
          const bodyEnd = (() => { const s = n(); return p + s; })();
          const t = funcTypes[f], ty = types[t] || { params: [], results: [] };
          const sig = (ty.params.length ? ` (param ${ty.params.join(' ')})` : '') + (ty.results.length ? ` (result ${ty.results.join(' ')})` : '');
          out.push(`  (func (;${imported + f};) (type ${t})${sig}`);
          const locals = [];
          const lc = n(); for (let k = 0; k < lc; k++) { const cnt = n(), vt = valtype(); for (let j = 0; j < cnt; j++) locals.push(vt); }
          if (locals.length) out.push(`    (local ${locals.join(' ')})`);
          let depth = 0, ind = '    ';
          const body = [];
          while (p < bodyEnd) {
            const op = u8();
            let txt;
            if (op === 0x0b) { if (depth === 0) break; depth--; ind = ind.slice(2); body.push(ind + 'end'); continue; }
            if (op === 0x02 || op === 0x03 || op === 0x04) {
              const bt = bytes[p] === 0x40 ? (p++, '') : bytes[p] >= 0x6f && bytes[p] <= 0x7f ? ` (result ${valtype()})` : ` (type ${Number(sleb())})`;
              body.push(`${ind}${['block', 'loop', 'if'][op - 2]}${bt}`); depth++; ind += '  '; continue;
            }
            if (op === 0x05) { body.push(ind.slice(2) + 'else'); continue; }
            if (NUM[op]) txt = NUM[op];
            else if (MEM[op]) { const a = n(), o = n(); txt = MEM[op] + (o ? ` offset=${o}` : ''); void a; }
            else if (IDX1[op]) txt = `${IDX1[op]} ${n()}`;
            else if (op === 0x41) txt = `i32.const ${sleb()}`;
            else if (op === 0x42) txt = `i64.const ${sleb()}`;
            else if (op === 0xd0) txt = `ref.null ${valtype()}`;
            else if (op === 0xfb && GC[bytes[p]] !== undefined) { const [name, k] = GC[n()]; const xs = []; for (let j = 0; j < k; j++) xs.push(n()); txt = [name, ...xs].join(' '); }
            else { body.push(`${ind};; (the fallback printer stops at opcode 0x${op.toString(16)})`); p = bodyEnd; break; }
            body.push(ind + txt);
          }
          p = bodyEnd;
          if (body.length) body[body.length - 1] += ')'; else out[out.length - 1] += ')';
          out.push(...body);
        }
      }
      p = end;
    }
    out[out.length - 1] += ')';
    return out.join('\n');
  }
  // parameter/result types per type index (function types only)
  function MODINFO_TYPES(bytes) {
    const r = [];
    try {
      let p = 8;
      const u8 = () => bytes[p++];
      const n = () => { let v = 0, s = 0, b; do { b = bytes[p++]; v += (b & 0x7f) * 2 ** s; s += 7; } while (b & 0x80); return v; };
      const vt = () => { const b = u8(); if (b === 0x64 || b === 0x63) { n(); return 'ref'; } return VT[b] || 'ref'; };
      const vec = f => { const c = n(), a = []; for (let k = 0; k < c; k++) a.push(f()); return a; };
      while (p < bytes.length) {
        const id = u8(), size = n(), end = p + size;
        if (id === 1) {
          const comp = () => { const b = u8(); if (b === 0x60) return { params: vec(vt), results: vec(vt) };
            if (b === 0x5f) { vec(() => { if (bytes[p] === 0x78 || bytes[p] === 0x77) p++; else vt(); u8(); }); return null; }
            if (bytes[p] === 0x78 || bytes[p] === 0x77) p++; else vt(); u8(); return null; };
          const sub = () => { if (bytes[p] === 0x50 || bytes[p] === 0x4f) { p++; vec(n); } r.push(comp()); };
          vec(() => { if (bytes[p] === 0x4e) { p++; vec(sub); } else sub(); });
        }
        p = end;
      }
    } catch (e) { /* display only */ }
    return r;
  }
  return { print, parse };
})();
if (typeof module !== 'undefined') module.exports = Lines;
