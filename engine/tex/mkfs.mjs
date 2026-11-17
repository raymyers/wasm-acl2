// Build the host file directory for tex.wasm: the bundled TeX files plus the
// font metrics (TFM), decoded from dvi2html's fonts.json.
// Usage: node mkfs.mjs DL_DIR OUT_DIR
import {readFileSync, writeFileSync, readdirSync, mkdirSync, copyFileSync} from 'node:fs';
const [dl, out] = process.argv.slice(2);
mkdirSync(out, {recursive: true});
for (const n of readdirSync(`${dl}/tex_files`)) copyFileSync(`${dl}/tex_files/${n}`, `${out}/${n}`);
const fonts = JSON.parse(readFileSync(`${dl}/fonts.json`, 'utf8'));
for (const [name, b64] of Object.entries(fonts)) writeFileSync(`${out}/${name}.tfm`, Buffer.from(b64, 'base64'));
console.log(readdirSync(out).length, 'files in', out);
