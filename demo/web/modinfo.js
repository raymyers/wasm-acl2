// demo/web/modinfo.js: source text -> bytes (WAT through wabt, or hex), and
// the exported functions of a binary with their parameter and result types
// (read from the type, import, function and export sections, GC type
// encodings included). Display and argument conversion only: the semantics
// does its own decoding and validation.
'use strict';
const ModInfo = (() => {
  const isWat = src => /^\s*\(/.test(src.replace(/;;[^\n]*/g, ''));   // otherwise hex

  function hexBytes(src) {
    const hex = src.replace(/;;[^\n]*/g, '').replace(/\s+/g, '');
    if (!/^([0-9a-f]{2})*$/i.test(hex)) throw new Error('hex input: expected pairs of hex digits (comments start with ;;)');
    return Uint8Array.from(hex.match(/../g) || [], h => parseInt(h, 16));
  }

  const FEATURES = { exceptions: true, simd: true, reference_types: true, multi_value: true,
    bulk_memory: true, tail_call: true, extended_const: true, function_references: true, gc: true, memory64: true };
  function watBytes(wabt, src) {
    const m = wabt.parseWat('input.wat', src, FEATURES);
    // not wabt's validate: validation is the semantics' job (Module_ok), and
    // an invalid module is shown as each side reports it
    try { m.resolveNames(); return new Uint8Array(m.toBinary({}).buffer); }
    finally { m.destroy(); }
  }
  const toBytes = (wabt, src) => isWat(src) ? watBytes(wabt, src) : hexBytes(src);

  const VT = { 0x7f: 'i32', 0x7e: 'i64', 0x7d: 'f32', 0x7c: 'f64', 0x7b: 'v128' };
  function exportsOf(bytes) {
    let p = 8;
    const u8 = () => bytes[p++];
    const leb = () => { let r = 0n, s = 0n, b; do { b = bytes[p++]; r |= BigInt(b & 0x7f) << s; s += 7n; } while (b & 0x80); return Number(r); };
    const name = () => { const n = leb(); const s = new TextDecoder().decode(bytes.subarray(p, p + n)); p += n; return s; };
    const valtype = () => { const b = u8(); if (b === 0x64 || b === 0x63) { leb(); return 'ref'; } return VT[b] || 'ref'; };
    const vec = f => { const n = leb(), r = []; for (let k = 0; k < n; k++) r.push(f()); return r; };
    const limits = () => { const f = u8(); leb(); if (f & 1) leb(); };
    const types = [], funcs = [], exps = [];
    function comptype() {
      const b = u8();
      if (b === 0x60) { const params = vec(valtype), results = vec(valtype); return { params, results }; }
      if (b === 0x5f) { vec(() => { storage(); u8(); }); return null; }
      if (b === 0x5e) { storage(); u8(); return null; }
      throw new Error('type section: unknown type form 0x' + b.toString(16));
    }
    const storage = () => { if (bytes[p] === 0x78 || bytes[p] === 0x77) p++; else valtype(); };
    function subtype() {
      if (bytes[p] === 0x50 || bytes[p] === 0x4f) { p++; vec(leb); }
      types.push(comptype());
    }
    while (p < bytes.length) {
      const id = u8(), size = leb(), end = p + size;
      if (id === 1) vec(() => { if (bytes[p] === 0x4e) { p++; vec(subtype); } else subtype(); });
      else if (id === 2) vec(() => {
        name(); name(); const k = u8();
        if (k === 0) funcs.push(leb());
        else if (k === 1) { valtype(); limits(); }
        else if (k === 2) limits();
        else if (k === 3) { valtype(); u8(); }
        else if (k === 4) { u8(); leb(); }
      });
      else if (id === 3) vec(() => funcs.push(leb()));
      else if (id === 7) vec(() => { const n = name(), k = u8(), i = leb(); if (k === 0) exps.push({ name: n, func: i }); });
      p = end;
    }
    return exps.map(e => ({ name: e.name, ...(types[funcs[e.func]] || { params: [], results: [] }) }));
  }
  return { toBytes, exportsOf, isWat };
})();
if (typeof module !== 'undefined') module.exports = ModInfo;
