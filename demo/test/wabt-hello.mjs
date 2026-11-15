// W0 item 1: wabt's JS build (from the flake, $WABT_JS) turns WAT into a
// binary that node's WebAssembly runs.
import { createRequire } from 'node:module';
const require = createRequire(import.meta.url);
const wabt = await require(process.env.WABT_JS)();
const wat = '(module (func (export "add") (param i32 i32) (result i32) local.get 0 local.get 1 i32.add))';
const mod = wabt.parseWat('hello.wat', wat);
const { buffer } = mod.toBinary({});
const { instance } = await WebAssembly.instantiate(buffer);
const got = instance.exports.add(2, 3);
console.log(`wabt.js: ${buffer.length} bytes, add(2,3) = ${got}`);
process.exit(got === 5 ? 0 : 1);
