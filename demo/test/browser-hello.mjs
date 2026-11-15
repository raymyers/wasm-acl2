// W0 item 1: load the JSCL hello page in headless Chromium and Firefox and
// check the string computed by the compiled Lisp. With SHOT=<file>, also
// writes the progress screenshot (Chromium).
import path from 'node:path';
import { serve } from './serve.mjs';
import { BROWSERS, withPage, screenshot } from './browser.mjs';

const here = path.dirname(new URL(import.meta.url).pathname);
const srv = await serve([path.join(here, '../web'), path.join(here, '../build')]);
const want = 'hello from JSCL: 3';
let fail = 0;
try {
  for (const b of BROWSERS) {
    await withPage(b, async (page, errors) => {
      await page.goto(srv.url + 'hello.html');
      const got = await page.textContent('#out');
      const ok = got === want && errors.length === 0;
      console.log(`${b}: ${ok ? 'PASS' : 'FAIL'} ${JSON.stringify(got)} ${errors.join('; ')}`);
      if (!ok) fail++;
      if (ok && b === 'chromium' && process.env.SHOT) {
        const kb = await screenshot(page, process.env.SHOT);
        console.log(`screenshot ${process.env.SHOT}: ${kb.toFixed(0)} KB`);
      }
    });
  }
} finally { srv.close(); }
process.exit(fail ? 1 : 0);
