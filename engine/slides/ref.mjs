// V8 reference for the slide renderer (E12): node ref.mjs sent.wasm OUTDIR
// Renders every slide, prints "SLIDE n scale sha256(framebuffer)" and writes
// OUTDIR/slide-n.png (black on white) for viewing.
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { deflateSync } from 'node:zlib';
const [wasmFile, out] = process.argv.slice(2);
mkdirSync(out, { recursive: true });
const { instance } = await WebAssembly.instantiate(readFileSync(wasmFile), {});
const e = instance.exports;
const W = e.width(), H = e.height(), n = e.slide_count();
console.log('SLIDES', n, 'SIZE', W, H);
function png(fbBytes, scale) {
  const w = W * scale, h = H * scale, raw = Buffer.alloc((w + 1) * h);
  for (let y = 0; y < h; y++) {
    raw[y * (w + 1)] = 0;
    for (let x = 0; x < w; x++) {
      const sx = (x / scale) | 0, sy = (y / scale) | 0;
      const bit = (fbBytes[sy * (W / 8) + (sx >> 3)] >> (7 - (sx & 7))) & 1;
      raw[y * (w + 1) + 1 + x] = bit ? 0 : 255;
    }
  }
  const crcT = new Int32Array(256).map((_, k) => { let c = k; for (let i = 0; i < 8; i++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1; return c; });
  const crc = b => { let c = -1; for (const x of b) c = crcT[(c ^ x) & 255] ^ (c >>> 8); return (c ^ -1) >>> 0; };
  const chunk = (t, d) => { const l = Buffer.alloc(4); l.writeUInt32BE(d.length); const td = Buffer.concat([Buffer.from(t), d]); const c = Buffer.alloc(4); c.writeUInt32BE(crc(td)); return Buffer.concat([l, td, c]); };
  const ihdr = Buffer.alloc(13); ihdr.writeUInt32BE(w, 0); ihdr.writeUInt32BE(h, 4); ihdr[8] = 8; ihdr[9] = 0;
  return Buffer.concat([Buffer.from([137, 80, 78, 71, 13, 10, 26, 10]), chunk('IHDR', ihdr), chunk('IDAT', deflateSync(raw)), chunk('IEND', Buffer.alloc(0))]);
}
for (let i = 0; i < n; i++) {
  const k = e.render(i);
  const fb = new Uint8Array(e.memory.buffer, e.framebuffer(), (W / 8) * H);
  console.log('SLIDE', i, 'scale', k, createHash('sha256').update(fb).digest('hex'));
  writeFileSync(`${out}/slide-${i}.png`, png(fb, 1));
}
