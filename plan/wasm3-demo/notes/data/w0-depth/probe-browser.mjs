// W0 item 4: the stack probes of probe-core.js in a Worker (and on the page)
// of headless Chromium and Firefox. Usage: node probe-browser.mjs BUILD_DIR
import path from 'node:path';
import fs from 'node:fs';
import { serve } from '../../../../../demo/test/serve.mjs';
import { BROWSERS, withPage } from '../../../../../demo/test/browser.mjs';

const here = path.dirname(new URL(import.meta.url).pathname);
const dir = path.resolve(process.argv[2]);
fs.copyFileSync(path.join(here, 'probe-core.js'), path.join(dir, 'probe-core.js'));
fs.writeFileSync(path.join(dir, 'w0-probe-worker.js'),
  `importScripts('probe.js'); importScripts('probe-core.js'); postMessage(w0Probe(self.jscl));`);
fs.writeFileSync(path.join(dir, 'w0-probe.html'), `<!doctype html><meta charset=utf-8><script src="jscl.js"></script>
<script src="probe.js"></script><script src="probe-core.js"></script><script>
window.page = w0Probe(window.jscl);
window.worker = new Promise(res => { const w = new Worker('w0-probe-worker.js'); w.onmessage = e => res(e.data); w.onerror = e => res('ERROR ' + e.message); });
</script>`);
const srv = await serve([dir]);
try {
  for (const b of BROWSERS) {
    await withPage(b, async (page) => {
      await page.goto(srv.url + 'w0-probe.html');
      console.log(`W0-PROBE ${b} page: ${JSON.stringify(await page.evaluate(() => window.page))}`);
      console.log(`W0-PROBE ${b} worker: ${JSON.stringify(await page.evaluate(() => window.worker))}`);
    });
  }
} finally { srv.close(); }
