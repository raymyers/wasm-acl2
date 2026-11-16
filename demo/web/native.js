// demo/web/native.js: runs the same export on the host's own WebAssembly
// engine (D4: the oracle shown next to the semantics; the page does not
// judge). Results are given as the semantics' are: {type, bits, text}.
'use strict';
// PRINTING ({PRINT_TYPES, printLine}, semantics.js): the same env
// print functions as the semantics' host, as JS imports; their lines are
// returned in `prints`.
function runNative(bytes, fn, args, parseArg, showBits, printing) {
  const prints = [];
  const imports = {};
  if (printing) {
    const dv8 = new DataView(new ArrayBuffer(8));
    const val = (type, x) => {
      let bits;
      if (type === 'i32') bits = BigInt.asUintN(32, BigInt(x));
      else if (type === 'i64') bits = BigInt.asUintN(64, x);
      else if (type === 'f32') { dv8.setFloat32(0, x, true); bits = BigInt(dv8.getUint32(0, true)); }
      else { dv8.setFloat64(0, x, true); bits = dv8.getBigUint64(0, true); }
      return { type, bits: bits.toString(), text: showBits(type, bits) };
    };
    imports.env = {};
    for (const [field, types] of Object.entries(printing.PRINT_TYPES))
      imports.env[field] = (...xs) => { prints.push(printing.printLine(field, types.map((t, k) => val(t, xs[k])))); };
  }
  const now = () => (typeof performance !== 'undefined' ? performance : Date).now();
  const t0 = now();
  let t1 = null;                                   // after compile + instantiate
  const done = r => { const t = now(); return t1 === null ? { ...r, prints, loadMs: t - t0 } : { ...r, prints, loadMs: t1 - t0, runMs: t - t1 }; };
  let inst;
  try { inst = new WebAssembly.Instance(new WebAssembly.Module(bytes), imports); }
  catch (e) {
    const status = e instanceof WebAssembly.CompileError ? 'invalid' : e instanceof WebAssembly.LinkError ? 'unlinkable'
      : e instanceof WebAssembly.RuntimeError ? 'trap' : 'error';
    return done({ status, message: e.message });
  }
  t1 = now();
  const f = inst.exports[fn.name];
  if (typeof f !== 'function') return done({ status: 'error', message: `no exported function ${fn.name}` });
  const dv = new DataView(new ArrayBuffer(8));
  const jsArg = (type, bits) => {
    if (type === 'i32') return Number(BigInt.asIntN(32, bits));
    if (type === 'i64') return BigInt.asIntN(64, bits);
    if (type === 'f32') { dv.setUint32(0, Number(bits), true); return dv.getFloat32(0, true); }
    if (type === 'f64') { dv.setBigUint64(0, bits, true); return dv.getFloat64(0, true); }
    throw new Error(`${type} arguments cannot be passed through the JS API`);
  };
  const fromJs = (type, x) => {
    let bits;
    if (type === 'i32') bits = BigInt.asUintN(32, BigInt(x));
    else if (type === 'i64') bits = BigInt.asUintN(64, x);
    else if (type === 'f32') { dv.setFloat32(0, x, true); bits = BigInt(dv.getUint32(0, true)); }
    else if (type === 'f64') { dv.setFloat64(0, x, true); bits = dv.getBigUint64(0, true); }
    else return { type: 'ref', bits: x === null ? 'null' : 'ref', text: x === null ? 'ref.null' : 'ref (opaque to JS)' };
    return { type, bits: bits.toString(), text: showBits(type, bits) };
  };
  let r;
  try { r = f(...args.map(({ type, value }) => jsArg(type, parseArg(type, value)))); }
  catch (e) {
    if (e instanceof WebAssembly.RuntimeError) return done({ status: 'trap', message: e.message });
    if (typeof WebAssembly.Exception !== 'undefined' && e instanceof WebAssembly.Exception) return done({ status: 'exception', message: 'uncaught WebAssembly exception' });
    if (e instanceof RangeError) return done({ status: 'exhausted', message: e.message });
    return done({ status: 'error', message: String(e.message || e) });
  }
  const rs = fn.results.length === 1 ? [r] : fn.results.length === 0 ? [] : [...r];
  return done({ status: 'ok', values: fn.results.map((t, k) => fromJs(t, rs[k])) });
}
if (typeof module !== 'undefined') module.exports = runNative;
