// Print \figdim{figs/NAME.png}{WIDTH}{HEIGHT} for every PNG in a directory
// (pixel sizes from the PNG header), so TeX can size images it never opens.
// Usage: node figdims.mjs DIR PREFIX > figdims.tex
import {readFileSync, readdirSync} from 'node:fs';
const [dir, prefix] = process.argv.slice(2);
for (const n of readdirSync(dir).filter(n => n.endsWith('.png')).sort()) {
  const b = readFileSync(`${dir}/${n}`);
  console.log(`\\figdim{${prefix}${n}}{${b.readUInt32BE(16)}}{${b.readUInt32BE(20)}}`);
}
