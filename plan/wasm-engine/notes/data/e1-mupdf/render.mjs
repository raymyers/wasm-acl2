// Usage: node render.mjs <dir with mupdf.js> <pdf> <out.ppm>
// Renders page 1 at 72 dpi to RGB and prints width, height and the sha256 of the samples.
import { readFileSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { pathToFileURL } from 'node:url';
import { resolve } from 'node:path';
const [dir, pdf, out] = process.argv.slice(2);
const mupdf = await import(pathToFileURL(resolve(dir, 'mupdf.js')).href);
const doc = mupdf.Document.openDocument(readFileSync(pdf), 'application/pdf');
const page = doc.loadPage(0);
const pix = page.toPixmap(mupdf.Matrix.identity, mupdf.ColorSpace.DeviceRGB, false, true);
const w = pix.getWidth(), h = pix.getHeight(), px = pix.getPixels();
writeFileSync(out, Buffer.concat([Buffer.from(`P6\n${w} ${h}\n255\n`), Buffer.from(px)]));
console.log(w, h, px.length, createHash('sha256').update(px).digest('hex'));
