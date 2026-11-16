// Usage: node errpath.mjs <dir with mupdf.js>. Exercises MuPDF's fz_try/fz_catch path (wasm exceptions).
import { pathToFileURL } from 'node:url';
import { resolve } from 'node:path';
const mupdf = await import(pathToFileURL(resolve(process.argv[2], 'mupdf.js')).href);
let caught = [];
try { mupdf.Document.openDocument(Buffer.from('this is not a pdf'), 'application/pdf').loadPage(0); } catch (e) { caught.push(String(e.message || e).slice(0, 60)); }
const doc = mupdf.Document.openDocument(Buffer.from('%PDF-1.4\n1 0 obj\n<< /Type /Catalog >>\nendobj\ntrailer\n<< /Root 1 0 R >>\n'), 'application/pdf');
try { doc.loadPage(5); } catch (e) { caught.push(String(e.message || e).slice(0, 60)); }
console.log(JSON.stringify(caught));
