// E12 (L0): compare the engine's slides with V8 and make the viewer.
// node check.mjs sent.wasm ENGINEDIR VIEWDIR
// For every ENGINEDIR/slide-N.pbm: sha256 of its pixel data, compared with
// V8 rendering the same module (render(N), framebuffer bytes). Writes
// VIEWDIR/slide-N.png  from the ENGINE's pixels, VIEWDIR/index.html
// (full-screen viewer, arrow keys) and prints one line per slide and a total.
import { readFileSync, writeFileSync, mkdirSync, existsSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { deflateSync } from 'node:zlib';
const [wasmFile, engDir, viewDir] = process.argv.slice(2);
mkdirSync(viewDir, { recursive: true });
const { instance } = await WebAssembly.instantiate(readFileSync(wasmFile), {});
const e = instance.exports, W = e.width(), H = e.height(), n = e.slide_count();
const sha = b => createHash('sha256').update(b).digest('hex');
const crcT = new Int32Array(256).map((_, k) => { let c = k; for (let i = 0; i < 8; i++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1; return c; });
const crc = b => { let c = -1; for (const x of b) c = crcT[(c ^ x) & 255] ^ (c >>> 8); return (c ^ -1) >>> 0; };
const chunk = (t, d) => { const l = Buffer.alloc(4); l.writeUInt32BE(d.length); const td = Buffer.concat([Buffer.from(t), d]); const c = Buffer.alloc(4); c.writeUInt32BE(crc(td)); return Buffer.concat([l, td, c]); };
function png(fb, scale) {
  const w = W * scale, h = H * scale, raw = Buffer.alloc((w + 1) * h);
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
    const sx = (x / scale) | 0, sy = (y / scale) | 0;
    raw[y * (w + 1) + 1 + x] = (fb[sy * (W / 8) + (sx >> 3)] >> (7 - (sx & 7))) & 1 ? 0 : 255;
  }
  const ihdr = Buffer.alloc(13); ihdr.writeUInt32BE(w, 0); ihdr.writeUInt32BE(h, 4); ihdr[8] = 8;
  return Buffer.concat([Buffer.from([137, 80, 78, 71, 13, 10, 26, 10]), chunk('IHDR', ihdr), chunk('IDAT', deflateSync(raw)), chunk('IEND', Buffer.alloc(0))]);
}
const ro = `${engDir}/render.out`;
const log = existsSync(ro) ? readFileSync(ro, 'latin1') : '';
const machine = /machine :LIST/.test(log) ? 'list machine' : 'fast machine';
// Plan D8: say whether the runs are inside the proved subset. The list
// machine prints one line ENGINE-T1 per run (render.lsp): the hypotheses of
// T1 (machine-result-is-spec-result) checked on that run.
const t1 = log.match(/ENGINE-T1 .*$/gm) || [], t1ok = t1.filter(l => /abs T result T$/.test(l)).length;
const proved = machine !== 'list machine' ? 'fast machine: not inside a theorem yet (T2 excludes call_ref until V7 of plan2.md)'
  : t1.length > 0 && t1ok === t1.length ? `inside the proved subset: theorem T1 (machine-result-is-spec-result) holds for all ${t1.length} runs, hypotheses checked at run time`
  : `NOT inside the proved subset: T1 hypotheses hold for ${t1ok} of ${t1.length} runs`;
let same = 0;
for (let i = 0; i < n; i++) {
  e.render(i);
  const v8 = Buffer.from(new Uint8Array(e.memory.buffer, e.framebuffer(), (W / 8) * H));
  const f = `${engDir}/slide-${i}.pbm`;
  if (!existsSync(f)) { console.log('SLIDE', i, 'MISSING'); continue; }
  const pbm = readFileSync(f), header = `P4\n${W} ${H}\n`, pix = pbm.subarray(header.length);
  const ok = pbm.subarray(0, header.length).toString() === header && pix.equals(v8);
  if (ok) same++;
  console.log('SLIDE', i, ok ? 'SAME' : 'DIFFERENT', 'engine', sha(pix), 'v8', sha(v8));
  writeFileSync(`${viewDir}/slide-${i}.png`, png(pix, 1));
}
console.log('PROVED', proved);
console.log('TOTAL', same, 'of', n, 'slides identical to V8; module sha256', sha(readFileSync(wasmFile)));
writeFileSync(`${viewDir}/index.html`, `<!doctype html><meta charset="utf-8"><title>Engine slides</title>
<style>html,body{margin:0;height:100%;background:#fff}img{width:100vw;height:100vh;object-fit:contain;image-rendering:pixelated}
#cap{position:fixed;bottom:4px;left:8px;font:12px sans-serif;color:#888}</style>
<img id="s"><div id="cap"></div><script>
const n=${n};let i=0;const s=document.getElementById('s'),cap=document.getElementById('cap');
function show(){s.src='slide-'+i+'.png';cap.textContent='slide '+(i+1)+'/'+n+' rendered by the ${machine} of the WebAssembly engine in ACL2; pixels identical to V8: ${same}/${n}; ${proved}';}
document.onkeydown=e=>{if(e.key==='ArrowRight'||e.key===' ')i=Math.min(n-1,i+1);else if(e.key==='ArrowLeft')i=Math.max(0,i-1);else if(e.key==='f')document.documentElement.requestFullscreen();show();};show();
</script>`);
