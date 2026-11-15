// W0 item 3: maximum parenthesis depth of each top-level form of an extracted
// file (strings and |...| names skipped). Prints the deepest N.
const fs = require('fs');
const s = fs.readFileSync(process.argv[2], 'utf8');
const N = +(process.argv[3] || 10);
let d = 0, max = 0, start = 0, forms = [], i = 0, name = null;
while (i < s.length) {
  const c = s[i];
  if (c === '"') { i++; while (s[i] !== '"') { if (s[i] === '\\') i++; i++; } }
  else if (c === '|') { i++; while (s[i] !== '|') { if (s[i] === '\\') i++; i++; } }
  else if (c === ';') { while (s[i] !== '\n' && i < s.length) i++; }
  else if (c === '(') { if (d === 0) { start = i; max = 0; } d++; if (d > max) max = d; }
  else if (c === ')') { d--; if (d === 0) { const m = s.slice(start, start + 400).match(/\|DEFUN\| (\S+)/); forms.push([max, m ? m[1] : "?"]); } }
  i++;
}
forms.sort((a, b) => b[0] - a[0]);
console.log(`forms ${forms.length}; depth histogram:`, [50, 100, 200, 400, 800].map(t => `>${t}: ${forms.filter(f => f[0] > t).length}`).join(', '));
for (const [m, n] of forms.slice(0, N)) console.log(m, n);
