// E1 items 6 and 7: V8 reference renders and an import trace.
// Usage: node ref-render.mjs <dir with mupdf.js> <outdir> <pdf>...
// For each PDF: page 1 at 72 dpi (identity matrix), DeviceRGB, no alpha,
// written as <outdir>/<name>.ppm; prints width, height, byte count and the
// sha256 of the samples (the PPM header excluded). Then prints, per phase
// (load = instantiate and init, open = openDocument + loadPage,
// render = toPixmap), how often each import was called; the two asm_const
// imports are counted per code address, with the JS snippet they run.
// Calls of the module's exports are counted too (export <minified name>).
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { pathToFileURL } from 'node:url';
import { resolve, basename } from 'node:path';

const [dir, outdir, ...pdfs] = process.argv.slice(2);
mkdirSync(outdir, { recursive: true });
const names = {}; // minified import name -> real name, from the name section
const glue = readFileSync(resolve(dir, 'mupdf-wasm.js'), 'utf8');
const asmConsts = {};
{ const m = glue.match(/var m_=\{(.*?)\};/s);
  if (m) for (const e of m[1].matchAll(/(\d+):(.*?)(?=,\d{7}:|$)/gs)) asmConsts[e[1]] = e[2]; }
const wasmBytes = readFileSync(resolve(dir, 'mupdf-wasm.wasm'));
const mod = new WebAssembly.Module(wasmBytes);
const importNames = WebAssembly.Module.imports(mod).map(i => i.module + '.' + i.name);
// real names, from wasm-objdump's order (same order as the Import section)
const real = ['emscripten_asm_const_int','exit','emscripten_date_now','__wasi_fd_write','__wasi_fd_close',
  '__syscall_unlinkat','__syscall_openat','__syscall_fcntl64','emscripten_resize_heap','emscripten_asm_const_ptr',
  '_tzset_js','_timegm_js','_gmtime_js','_abort_js','__wasi_fd_seek','__wasi_fd_read','__wasi_environ_sizes_get',
  '__wasi_environ_get','__wasi_clock_time_get','__syscall_rmdir','__syscall_ioctl','__syscall_ftruncate64'];
importNames.forEach((n, i) => names[n] = real[i]);

let phase = 'load'; const counts = {};
const bump = k => { counts[phase] ??= {}; counts[phase][k] = (counts[phase][k] || 0) + 1; };
const origInst = WebAssembly.instantiate;
WebAssembly.instantiate = async function (src, imports) {
  for (const [m, obj] of Object.entries(imports)) for (const [k, f] of Object.entries(obj)) {
    if (typeof f !== 'function') continue;
    const nm = names[m + '.' + k] || (m + '.' + k);
    obj[k] = function (...args) {
      if (nm.startsWith('emscripten_asm_const')) bump(nm + ' @' + args[0]); else bump(nm);
      return f.apply(this, args);
    };
  }
  const r = await origInst.call(this, src, imports);
  const inst = r.instance || r;
  const ex = {};
  for (const [k, v] of Object.entries(inst.exports))
    ex[k] = typeof v === 'function' ? function (...a) { bump('export ' + k); return v.apply(this, a); } : v;
  const wrapped = { exports: ex };
  return r.instance ? { instance: wrapped, module: r.module } : wrapped;
};
const mupdf = await import(pathToFileURL(resolve(dir, 'mupdf.js')).href);
for (const pdf of pdfs) {
  phase = 'open ' + basename(pdf);
  const doc = mupdf.Document.openDocument(readFileSync(pdf), 'application/pdf');
  const page = doc.loadPage(0);
  phase = 'render ' + basename(pdf);
  const pix = page.toPixmap(mupdf.Matrix.identity, mupdf.ColorSpace.DeviceRGB, false, true);
  const w = pix.getWidth(), h = pix.getHeight(), px = pix.getPixels();
  writeFileSync(resolve(outdir, basename(pdf, '.pdf') + '.ppm'),
    Buffer.concat([Buffer.from(`P6\n${w} ${h}\n255\n`), Buffer.from(px)]));
  console.log('RENDER', basename(pdf), w, h, px.length, createHash('sha256').update(px).digest('hex'));
}
for (const [p, c] of Object.entries(counts)) {
  console.log('IMPORTS', p);
  for (const [k, n] of Object.entries(c).sort()) {
    const at = k.match(/@(\d+)$/);
    console.log('  ', n, k, at ? (asmConsts[at[1]] || '?').slice(0, 90) : '');
  }
}
