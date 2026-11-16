// W8 item 1: which rules of Step, Step_pure and Step_read have a premise of the Step family (Step,
// Step_pure, Step_read), read from the IL. The glue's rule-chain reader
// (driver/glue.lisp +STEP-DESCENDS+) descends only through these.
// Usage: node step-premises.mjs translate/il/wasm-3.0.il.sexp
import fs from 'node:fs';
const src = fs.readFileSync(process.argv[2], 'utf8');
let i = 0;
function read() {
  while (/\s/.test(src[i])) i++;
  if (src[i] === '(') { i++; const l = []; for (;;) { while (/\s/.test(src[i])) i++; if (src[i] === ')') { i++; return l; } l.push(read()); } }
  if (src[i] === '"') { let s = ''; i++; while (src[i] !== '"') { if (src[i] === '\\') i++; s += src[i++]; } i++; return { str: s }; }
  let a = ''; while (i < src.length && !/[\s()]/.test(src[i])) a += src[i++]; return a;
}
const top = []; for (;;) { while (i < src.length && /\s/.test(src[i])) i++; if (i >= src.length) break; top.push(read()); }
const FAMILY = ['Step', 'Step_pure', 'Step_read'];
// every relation name mentioned in a rule's premises: (rule id ... (rule-prem? ...)) -> strings that are relation names
function mentions(x, acc) {
  if (Array.isArray(x)) { for (const y of x) mentions(y, acc); }
  else if (x && x.str && FAMILY.includes(x.str)) acc.add(x.str);
  return acc;
}
const out = [];
(function walk(xs) {
  for (const x of xs) {
    if (!Array.isArray(x)) continue;
    if (x[0] === 'rec') walk(x.slice(1));
    if (x[0] === 'rel' && x[1] && FAMILY.includes(x[1].str))
      for (const r of x.filter(y => Array.isArray(y) && y[0] === 'rule')) {
        // the rule's own id and its conclusion are r[1], r[2..]; premises are the
        // sub-lists after the conclusion. Count the relation names inside the
        // whole rule body except its id string.
        const m = mentions(r.slice(2), new Set());
        if (m.size) out.push(`${x[1].str}/${r[1].str} -> ${[...m].join(',')}`);
      }
  }
})(top);
for (const l of out) console.log('W8-PREMISE ' + l);
console.log(`W8-PREMISE ${out.length} rules of Step, Step_pure, Step_read with a Step-family premise`);
