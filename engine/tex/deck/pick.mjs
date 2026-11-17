// Print deck.tex with the slides not in the list replaced by \skipslide, so
// TeX does not read them. A slide is \begin{slide} ... \end{slide} or a
// \fullbleed line; everything else is kept.
// Usage: node pick.mjs deck.tex 13,14 > picked.tex
import {readFileSync} from 'node:fs';
const [file, list] = process.argv.slice(2);
const want = new Set(list.split(',').map(Number));
let n = 0, skipping = false;
for (const line of readFileSync(file, 'utf8').replace(/\n$/, '').split('\n')) {
  if (skipping) {
    const m = line.match(/^\\end\{slide\}(.*)$/);
    if (m) { skipping = false; console.log('\\skipslide' + m[1]); }
  } else if (/^\\begin\{slide\}/.test(line) && !want.has(++n)) skipping = true;
  else if (/^\\fullbleed\{/.test(line) && !want.has(++n)) console.log('\\skipslide');
  else console.log(line);
}
