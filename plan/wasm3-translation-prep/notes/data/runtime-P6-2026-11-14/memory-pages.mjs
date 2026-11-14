// P6: initial memory size (pages, summed over a module's memories, imports
// not counted) of every .wasm under DIR. node memory-pages.mjs DIR
import { readFileSync, readdirSync, statSync } from "node:fs";
import { join } from "node:path";
function* walk(d) { for (const n of readdirSync(d)) { const p = join(d, n); if (statSync(p).isDirectory()) yield* walk(p); else if (n.endsWith(".wasm")) yield p; } }
function leb(b, i) { let r = 0n, s = 0n; for (;;) { const x = b[i++]; r |= BigInt(x & 0x7f) << s; s += 7n; if (!(x & 0x80)) return [r, i]; } }
const hist = new Map(); let bad = 0, n = 0;
for (const f of walk(process.argv[2])) {
  n++; const b = readFileSync(f); let pages = 0n, i = 8;
  try {
    while (i < b.length) {
      const id = b[i++]; let len; [len, i] = leb(b, i); const end = i + Number(len);
      if (id === 5) { let cnt; [cnt, i] = leb(b, i);
        for (let k = 0; k < Number(cnt); k++) { const flag = b[i++]; let min; [min, i] = leb(b, i); if (flag & 1) [, i] = leb(b, i); pages += min; } }
      i = end;
    }
  } catch (e) { bad++; continue; }
  const k = pages === 0n ? "0" : pages <= 1n ? "1" : pages <= 4n ? "2-4" : pages <= 16n ? "5-16" : pages <= 256n ? "17-256" : ">256";
  hist.set(k, (hist.get(k) || 0) + 1);
}
console.log("modules", n, "unparsed", bad);
for (const k of ["0", "1", "2-4", "5-16", "17-256", ">256"]) console.log("pages", k, hist.get(k) || 0);
