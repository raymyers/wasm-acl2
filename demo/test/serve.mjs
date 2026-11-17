// Minimal static server for the headless browser tests (localhost only).
// serve([dir, ...]) -> {url, close()}; the first dir holding a path wins.
import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';

const TYPES = { '.html': 'text/html', '.js': 'text/javascript', '.mjs': 'text/javascript',
  '.wasm': 'application/wasm', '.css': 'text/css', '.json': 'application/json', '.png': 'image/png' };

export function serve(dirs) {
  const roots = (Array.isArray(dirs) ? dirs : [dirs]).map(d => path.resolve(d));
  const server = http.createServer((req, res) => {
    const rel = decodeURIComponent(new URL(req.url, 'http://x').pathname).replace(/^\/+/, '');
    for (const root of roots) {
      const f = path.join(root, rel);
      if (f.startsWith(root) && fs.existsSync(f) && fs.statSync(f).isFile()) {
        res.writeHead(200, { 'content-type': TYPES[path.extname(f)] || 'application/octet-stream' });
        fs.createReadStream(f).pipe(res);
        return;
      }
    }
    res.writeHead(404); res.end('not found');
  });
  return new Promise(r => server.listen(0, '127.0.0.1', () =>
    r({ url: `http://127.0.0.1:${server.address().port}/`, close: () => server.close() })));
}
