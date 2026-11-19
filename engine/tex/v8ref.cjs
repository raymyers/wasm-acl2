// The reference run for the DVI comparison (plan/wasm-engine/plan2.md V8):
// the same tex.wasm and core.dump on V8 (node), with TikZJax's own host
// functions, library.js of npm node-tikzjax 1.0.5 (fetch.sh), unmodified.
// texrun.lisp is a port of that file; this run is what it is compared with.
//   node v8ref.cjs LIBRARY.js DL_DIR FS_DIR INPUT.tex OUT.dvi [DIR ...]
// The host files are those of FS_DIR, then of each DIR (a later one wins),
// as TEXPATH and build/fs are for the driver; INPUT.tex is read as the
// driver reads it (a newline, then the file).
// Two things are set from outside the library, as the driver sets them:
//   - the date: 2026-01-01, 0 minutes (the DVI preamble contains it);
//   - the font metrics: the TFM files are in FS_DIR (mkfs.mjs), so the
//     library's own source for them, the package @prinsss/dvi2html, is not
//     loaded (a stub stands in for the require).
// A file that is not there: the library unwinds the module (asyncify), fails
// to load the file and rewinds; the driver answers "not found" at once. So
// the two runs can execute different instructions; the DVI must be the same.
const fs = require('node:fs'), path = require('node:path'), Module = require('node:module');
const [libFile, dl, fsDir, input, out, ...dirs] = process.argv.slice(2);
const RealDate = Date;
globalThis.Date = class extends RealDate {
  constructor(...a) { if (a.length) super(...a); else super(2026, 0, 1, 0, 0, 0); }
};
const load = Module._load;
Module._load = function (request, ...rest) {
  if (request === '@prinsss/dvi2html') return { tfmData(name) { throw new Error('no TFM file ' + name); } };
  return load.call(this, request, ...rest);
};
const library = require(path.resolve(libFile));
(async () => {
  for (const d of [fsDir, ...dirs])
    for (const n of fs.readdirSync(d))
      if (fs.statSync(path.join(d, n)).isFile()) library.writeFileSync(n, new Uint8Array(fs.readFileSync(path.join(d, n))));
  const job = path.basename(input);
  library.writeFileSync(job, new Uint8Array(Buffer.concat([Buffer.from('\n'), fs.readFileSync(input)])));
  const memory = new WebAssembly.Memory({ initial: library.pages, maximum: library.pages });
  new Uint8Array(memory.buffer).set(fs.readFileSync(path.join(dl, 'core.dump')));
  library.setMemory(memory.buffer);
  library.setInput(` ${job} \n\\end\n`);
  library.setFileLoader(async name => { throw new Error('not found: ' + name); });
  if (process.env.V8REF_CONSOLE) library.setShowConsole();
  const wasm = await WebAssembly.instantiate(fs.readFileSync(path.join(dl, 'tex.wasm')), { library, env: { memory } });
  const t0 = process.hrtime.bigint();
  await library.executeAsync(wasm.instance.exports);
  const dvi = Buffer.from(library.readFileSync(job.replace(/\.tex$/, '.dvi')));
  fs.writeFileSync(out, dvi);
  console.log(`V8REF ${job}: ${dvi.length} bytes of DVI in ${Number(process.hrtime.bigint() - t0) / 1e9} s -> ${out}`);
})().catch(e => { console.error('V8REF ERROR', e); process.exit(1); });
