// W7 item 5: every rule id of the given relations in the IL appears as a
// %RULE tag in the generated books, or is reported missing.
// Usage: node coverage.mjs IL.sexp GEN_DIR [Rel ...]   (default: Step Step_pure Step_read)
import fs from 'node:fs';
import path from 'node:path';
const [il, gen, ...rels0] = process.argv.slice(2);
const rels = rels0.length ? rels0 : ['Step', 'Step_pure', 'Step_read'];
// s-expression reader: strings, atoms, lists
const src = fs.readFileSync(il, 'utf8');
let i = 0;
function read() {
  while (/\s/.test(src[i])) i++;
  if (src[i] === '(') { i++; const l = []; for (;;) { while (/\s/.test(src[i])) i++; if (src[i] === ')') { i++; return l; } l.push(read()); } }
  if (src[i] === '"') { let s = ''; i++; while (src[i] !== '"') { if (src[i] === '\\') i++; s += src[i++]; } i++; return { str: s }; }
  let a = ''; while (i < src.length && !/[\s()]/.test(src[i])) a += src[i++]; return a;
}
const top = []; for (;;) { while (i < src.length && /\s/.test(src[i])) i++; if (i >= src.length) break; top.push(read()); }
const ids = {};
(function walk(xs) {
  for (const x of xs) {
    if (!Array.isArray(x)) continue;
    if (x[0] === 'rec') walk(x.slice(1));
    if (x[0] === 'rel' && x[1] && rels.includes(x[1].str))
      ids[x[1].str] = x.filter(y => Array.isArray(y) && y[0] === 'rule').map(y => y[1].str);
  }
})(top);
const text = fs.readdirSync(gen).filter(f => f.endsWith('.lisp')).map(f => fs.readFileSync(path.join(gen, f), 'utf8')).join(' ').replace(/\s+/g, ' ');
const tags = new Set([...text.matchAll(/\(%RULE "([^"]*)"/g)].map(m => m[1]));
let total = 0, found = 0;
for (const r of rels) {
  const missing = (ids[r] || []).filter(id => !tags.has(`${r}/${id}`));
  total += (ids[r] || []).length; found += (ids[r] || []).length - missing.length;
  console.log(`W7-COVERAGE ${r}: ${(ids[r] || []).length - missing.length}/${(ids[r] || []).length} tagged${missing.length ? '; missing: ' + missing.join(' ') : ''}`);
}
console.log(`W7-COVERAGE total: ${found}/${total} (distinct tags in ${gen}: ${tags.size})`);
process.exit(found === total ? 0 : 1);
