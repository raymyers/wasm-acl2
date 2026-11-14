// Generate numeric test vectors for the translated semantics, using a real
// WebAssembly engine (Node/V8) as the oracle.
//
//   node gen-numeric-vectors.mjs > ../sem/numeric-vectors.lsp
//
// Each vector is (OP-NAME ARG-BITS... RESULT), where floats are given as bit
// patterns, RESULT is the result bit pattern, :TRAP, or :NAN (any NaN: NaN
// payloads are nondeterministic in WASM). Deterministic: fixed PRNG seed.
import { execFileSync } from "node:child_process";
import { mkdtempSync, writeFileSync, readFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const T = { i32: "i32", i64: "i64", f32: "i32", f64: "i64" }; // carrier of bits
const F2I = { f32: "i32", f64: "i64" };

// [name, param types, result type, body]
const ops = [];
const ibin = ["add", "sub", "mul", "div_s", "div_u", "rem_s", "rem_u", "and", "or", "xor", "shl", "shr_s", "shr_u", "rotl", "rotr"];
const iun = ["clz", "ctz", "popcnt"];
const irel = ["eq", "ne", "lt_s", "lt_u", "gt_s", "gt_u", "le_s", "le_u", "ge_s", "ge_u"];
const fbin = ["add", "sub", "mul", "div", "min", "max", "copysign"];
const fun = ["abs", "neg", "sqrt", "ceil", "floor", "trunc", "nearest"];
const frel = ["eq", "ne", "lt", "gt", "le", "ge"];
const get = (i, t) => `local.get ${i}` + (t[0] === "f" ? ` ${t}.reinterpret_${F2I[t]}` : "");
const put = (t) => (t[0] === "f" ? ` ${F2I[t]}.reinterpret_${t}` : "");
for (const t of ["i32", "i64"]) {
  for (const o of ibin) ops.push([`${t}.${o}`, [t, t], t]);
  for (const o of iun) ops.push([`${t}.${o}`, [t], t]);
  for (const o of irel) ops.push([`${t}.${o}`, [t, t], "i32"]);
  ops.push([`${t}.eqz`, [t], "i32"]);
}
for (const t of ["f32", "f64"]) {
  for (const o of fbin) ops.push([`${t}.${o}`, [t, t], t]);
  for (const o of fun) ops.push([`${t}.${o}`, [t], t]);
  for (const o of frel) ops.push([`${t}.${o}`, [t, t], "i32"]);
}
const cvts = [
  ["i32.wrap_i64", "i64", "i32"], ["i64.extend_i32_s", "i32", "i64"], ["i64.extend_i32_u", "i32", "i64"],
  ["f32.demote_f64", "f64", "f32"], ["f64.promote_f32", "f32", "f64"],
  ["i32.reinterpret_f32", "f32", "i32"], ["i64.reinterpret_f64", "f64", "i64"],
  ["f32.reinterpret_i32", "i32", "f32"], ["f64.reinterpret_i64", "i64", "f64"],
];
for (const it of ["i32", "i64"]) for (const ft of ["f32", "f64"]) for (const sx of ["s", "u"]) {
  cvts.push([`${it}.trunc_${ft}_${sx}`, ft, it]);
  cvts.push([`${ft}.convert_${it}_${sx}`, it, ft]);
}
for (const [n, a, r] of cvts) ops.push([n, [a], r]);

const wat = "(module\n" + ops.map(([name, ps, r]) => {
  const params = ps.map((p) => T[p]).join(" ");
  const args = ps.map((p, i) => get(i, p)).join("\n    ");
  return `  (func (export "${name}") (param ${params}) (result ${T[r]})\n    ${args}\n    ${name}${put(r)})`;
}).join("\n") + ")\n";

const dir = mkdtempSync(join(tmpdir(), "w1t-vec-"));
writeFileSync(join(dir, "ops.wat"), wat);
execFileSync("wat2wasm", [join(dir, "ops.wat"), "-o", join(dir, "ops.wasm")]);
const { instance } = await WebAssembly.instantiate(readFileSync(join(dir, "ops.wasm")));
const ex = instance.exports;

// xorshift64* PRNG, fixed seed
let st = 0x9E3779B97F4A7C15n;
const M64 = (1n << 64n) - 1n;
function rnd64() { st ^= st >> 12n; st ^= (st << 25n) & M64; st ^= st >> 27n; return (st * 0x2545F4914F6CDD1Dn) & M64; }
const bits = (t) => (t === "i32" || t === "f32" ? 32n : 64n);
const mask = (t) => (1n << bits(t)) - 1n;

const special = {
  i32: [0n, 1n, 2n, 31n, 32n, 0x7fffffffn, 0x80000000n, 0xffffffffn, 0xfffffffen],
  i64: [0n, 1n, 63n, 64n, 0x7fffffffffffffffn, 0x8000000000000000n, M64, 0xffffffffn, 0x100000000n],
  f32: [0x00000000n, 0x80000000n, 0x3f800000n, 0xbf800000n, 0x3f000000n, 0x3fc00000n, 0x40200000n, 0xc0200000n,
        0x7f800000n, 0xff800000n, 0x7fc00000n, 0x00000001n, 0x80000001n, 0x007fffffn, 0x7f7fffffn, 0x4f000000n, 0xcf000000n, 0x4f800000n],
  f64: [0n, 0x8000000000000000n, 0x3ff0000000000000n, 0xbff0000000000000n, 0x3fe0000000000000n, 0x3ff8000000000000n,
        0x4004000000000000n, 0xc004000000000000n, 0x7ff0000000000000n, 0xfff0000000000000n, 0x7ff8000000000000n,
        1n, 0x8000000000000001n, 0x000fffffffffffffn, 0x7fefffffffffffffn, 0x41e0000000000000n, 0xc1e0000000000000n, 0x43e0000000000000n],
};
// random floats biased to moderate exponents, so arithmetic is exercised
function randomVal(t) {
  const r = rnd64();
  if (t === "f32" && (r & 3n)) return (r & 0x803fffffn) | (((r >> 40n) % 40n + 107n) << 23n);
  if (t === "f64" && (r & 3n)) return (r & 0x800fffffffffffffn) | (((r >> 52n) % 80n + 983n) << 52n);
  if (t[0] === "i" && (r & 1n)) return (r >> 7n) % 1000n; // small ints
  return r & mask(t);
}
const toJS = (t, v) => (T[t] === "i64" ? BigInt.asIntN(64, v) : Number(BigInt.asIntN(32, v)));
const fromJS = (t, v) => BigInt.asUintN(T[t] === "i64" ? 64 : 32, BigInt(v));
const isNaN = (t, v) => {
  if (t === "f32") return (v & 0x7f800000n) === 0x7f800000n && (v & 0x7fffffn) !== 0n;
  if (t === "f64") return (v & 0x7ff0000000000000n) === 0x7ff0000000000000n && (v & 0xfffffffffffffn) !== 0n;
  return false;
};

const out = [];
out.push("; GENERATED by tests/oracle/gen-numeric-vectors.mjs (Node " + process.version + " as oracle).");
out.push("; (OP ARG... RESULT): bit patterns; RESULT may be :TRAP or :NAN. Do not edit.");
out.push("(");
for (const [name, ps, r] of ops) {
  const n = ps.length === 1 ? 40 : 60;
  const pool = special[ps[0]];
  const cases = [];
  if (ps.length === 1) for (const a of special[ps[0]]) cases.push([a]);
  else for (let i = 0; i < pool.length; i++) cases.push([pool[i], special[ps[1]][(i * 7 + 3) % special[ps[1]].length]]);
  for (let i = 0; i < n; i++) cases.push(ps.map((p) => randomVal(p)));
  for (const args of cases) {
    let res;
    try {
      const raw = name.includes("reinterpret"); // bit-exact, even for NaNs
      const v = fromJS(r, ex[name](...args.map((a, i) => toJS(ps[i], a))));
      res = !raw && isNaN(r, v) ? ":NAN" : v.toString();
    } catch (e) {
      res = ":TRAP";
    }
    out.push(` ("${name}" ${args.map(String).join(" ")} ${res})`);
  }
}
out.push(")");
console.log(out.join("\n"));
