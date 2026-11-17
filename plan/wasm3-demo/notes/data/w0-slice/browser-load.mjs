// W0 item 3: load jscl.js + a compiled file (default full.js) in headless
// Chromium and Firefox, on the page and in a Worker; print load time or error.
// Usage: node browser-load.mjs DIR FILE.js
import path from 'node:path';
import fs from 'node:fs';
import { serve } from '../../../../../demo/test/serve.mjs';
import { BROWSERS, withPage } from '../../../../../demo/test/browser.mjs';

const dir = path.resolve(process.argv[2]);
const file = process.argv[3] || 'full.js';
fs.writeFileSync(path.join(dir, 'w0-load.html'), `<!doctype html><meta charset=utf-8><body><script>
window.result = new Promise(res => {
  const t0 = performance.now();
  const s1 = document.createElement('script'); s1.src = 'jscl.js';
  s1.onload = () => { const t1 = performance.now();
    window.onerror = (m) => res('page ERROR ' + m);
    const s2 = document.createElement('script'); s2.src = '${file}';
    s2.onload = () => res('page jscl ' + (t1 - t0).toFixed(0) + ' ms, ${file} ' + (performance.now() - t1).toFixed(0) + ' ms');
    document.body.appendChild(s2); };
  document.body.appendChild(s1);
});
window.wresult = new Promise(res => {
  const w = new Worker('w0-worker.js');
  w.onmessage = e => res(e.data); w.onerror = e => { res('worker ERROR ' + e.message); e.preventDefault(); };
});
</script>`);
fs.writeFileSync(path.join(dir, 'w0-worker.js'), `
const t1 = performance.now();
try { importScripts('${file}'); postMessage('worker jscl.js + ${file} (the prologue imports jscl.js) ' + (performance.now() - t1).toFixed(0) + ' ms'); }
catch (e) { postMessage('worker ERROR ' + e); }`);
const srv = await serve([dir]);
try {
  for (const b of BROWSERS) {
    await withPage(b, async (page) => {
      await page.goto(srv.url + 'w0-load.html');
      console.log(`W0-BROWSER ${b}: ${await page.evaluate(() => window.result)}`);
      console.log(`W0-BROWSER ${b}: ${await page.evaluate(() => window.wresult)}`);
    });
  }
} finally { srv.close(); }
