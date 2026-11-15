// Playwright from the flake (PLAYWRIGHT_NODE_MODULES; browsers from
// PLAYWRIGHT_BROWSERS_PATH): headless Chromium and Firefox, 1280x800, light.
import { createRequire } from 'node:module';
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';

const require = createRequire(import.meta.url);
const pw = require(`${process.env.PLAYWRIGHT_NODE_MODULES}/playwright`);

export const BROWSERS = ['chromium', 'firefox'];

export async function withPage(name, fn) {
  const browser = await pw[name].launch({ headless: true });
  try {
    const ctx = await browser.newContext({ viewport: { width: 1280, height: 800 }, colorScheme: 'light' });
    const page = await ctx.newPage();
    const errors = [];
    page.on('pageerror', e => errors.push(String(e)));
    return await fn(page, errors);
  } finally {
    await browser.close();
  }
}

// Screenshot for plan/wasm3-demo/progress/, palette-quantized with pngquant
// (from the flake); fails above 150 KB (step.md).
export async function screenshot(page, file, opts = {}) {
  await page.screenshot({ path: file, ...opts });
  try {
    execFileSync('pngquant', ['--force', '--skip-if-larger', '--quality=60-90', '--output', file, file]);
  } catch (e) {
    if (e.status !== 98 && e.status !== 99) throw e; // 98/99: already small enough
  }
  const kb = fs.statSync(file).size / 1024;
  if (kb > 150) throw new Error(`${file}: ${kb.toFixed(0)} KB > 150 KB`);
  return kb;
}
