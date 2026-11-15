// T7 conformance data: convert wast2json output (one directory per .wast of
// spec-test-1, each with NAME.json and NAME.N.wasm) into ACL2 command lists.
//
//   node gen-spec-tests.mjs IN_DIR OUT_DIR [SUITE]      (SUITE: spec-test-1 by default)
//
// writes OUT_DIR/NAME.lsp for every IN_DIR/NAME/NAME.json (wast2json) or
// IN_DIR/NAME/NAME.bin.wast (reference interpreter, see below), plus
// OUT_DIR/index.lsp, the list of names. Each NAME.lsp holds ONE object, the
// list of commands of that script:
//   (:module FILE NAME)            NAME is a string or NIL
//   (:register AS NAME)
//   (:action ACTION)
//   (:assert_return ACTION (VAL...))
//   (:assert_trap ACTION TEXT)
//   (:assert_exhaustion ACTION TEXT)
//   (:assert_invalid FILE TEXT) (:assert_malformed FILE TEXT KIND)
//   (:assert_unlinkable FILE TEXT) (:assert_uninstantiable FILE TEXT)
//   ACTION = (:invoke MODULE FIELD (VAL...)) | (:get MODULE FIELD)
//   VAL    = (:I32 n) (:I64 n) (:F32 bits) (:F64 bits) | (:F32 :NAN-CANONICAL) ...
//            3.0: (:V128 :F32 (lane ...)) (:EXTERNREF :NULL|n) (:FUNCREF :ANY)
//            (:I32 :ANY) when the JSON gives no value; (:UNSUPPORTED "type").
//   (:ASSERT_EXCEPTION ACTION); an unknown command type becomes (:UNSUPPORTED "type").
// MODULE is a module name string or NIL (the current module); FIELD (and
// AS) is a name as a list of Unicode code points; KIND is :BINARY or :TEXT.
import { readFileSync, writeFileSync, readdirSync, existsSync } from "node:fs";
import { join } from "node:path";

const [inDir, outDir, suite = "spec-test-1"] = process.argv.slice(2);

const str = (s) => (s == null ? "NIL" : '"' + String(s).replace(/[\\"]/g, (c) => "\\" + c) + '"');
// names as lists of Unicode code points, as the generated Bname decoder yields them
const bytes = (s) => "(" + [...s].map((c) => c.codePointAt(0)).join(" ") + ")";
// one scalar or lane value: a number (float lanes and scalars as bit
// patterns), or a NaN class
function scalar(x) {
  if (x === "nan:canonical") return ":NAN-CANONICAL";
  if (x === "nan:arithmetic") return ":NAN-ARITHMETIC";
  return String(BigInt(x));
}
function val(v) {
  if (v.type === "either") return `(:EITHER ${vals(v.values)})`;  // reference interpreter scripts only
  const t = ":" + v.type.toUpperCase();
  if (v.type === "v128") {                       // (:V128 :I32 (lane ...)), 3.0
    if (!Array.isArray(v.value)) return `(:V128 :ANY)`;
    return `(:V128 :${String(v.lane_type).toUpperCase()} (${v.value.map(scalar).join(" ")}))`;
  }
  if (["i32", "i64", "f32", "f64"].includes(v.type)) {
    if (v.value === undefined) return `(${t} :ANY)`;        // e.g. results of a trapping action
    return `(${t} ${scalar(v.value)})`;
  }
  if (v.type.endsWith("ref")) {                  // (:EXTERNREF :NULL | n | :ANY), 2.0+
    if (v.value === undefined) return `(${t} :ANY)`;
    if (v.value === "null") return `(${t} :NULL)`;
    return `(${t} ${BigInt(v.value)})`;
  }
  return `(:UNSUPPORTED ${str(v.type)})`;
}
const vals = (vs) => "(" + (vs || []).map(val).join(" ") + ")";
function action(a) {
  if (a.type === "invoke") return `(:INVOKE ${str(a.module)} ${bytes(a.field)} ${vals(a.args)})`;
  if (a.type === "get") return `(:GET ${str(a.module)} ${bytes(a.field)})`;
  throw new Error("action " + a.type);
}
function command(c) {
  switch (c.type) {
    case "module": return `(:MODULE ${str(c.filename)} ${str(c.name)})`;
    case "register": return `(:REGISTER ${bytes(c.as)} ${str(c.name)})`;
    case "action": return `(:ACTION ${action(c.action)})`;
    case "assert_return": return `(:ASSERT_RETURN ${action(c.action)} ${vals(c.expected)})`;
    case "assert_trap": return `(:ASSERT_TRAP ${action(c.action)} ${str(c.text)})`;
    case "assert_exhaustion": return `(:ASSERT_EXHAUSTION ${action(c.action)} ${str(c.text)})`;
    case "assert_invalid":
    case "assert_unlinkable":
    case "assert_uninstantiable":
      return `(:${c.type.toUpperCase()} ${str(c.filename)} ${str(c.text)})`;
    case "assert_malformed":
      return `(:ASSERT_MALFORMED ${str(c.filename)} ${str(c.text)} :${(c.module_type || "binary").toUpperCase()})`;
    case "assert_exception": return `(:ASSERT_EXCEPTION ${action(c.action)})`;
    // anything else is kept as a command the driver counts as unsupported
    default: return `(:UNSUPPORTED ${str(c.type)})`;
  }
}

// --- Scripts that wast2json cannot read (wasm3 M0b) -----------------------
// The reference interpreter of the pinned spec rewrites such a script with
// every module in binary form (`wasm -d NAME.wast -o NAME.bin.wast`, the
// flake does it for the scripts wast2json skips). IN_DIR/NAME/NAME.bin.wast
// is read here into the same command objects as wast2json's JSON, so the
// output format is the same. Its shapes: (module definition [$D] binary
// S...) defines a module, (module instance [$I $D]) instantiates the last
// (or the named) definition; text-only commands (assert_malformed of
// quoted modules) are already gone from it. Extra value forms: GC
// references, e.g. (:I31REF :ANY), (:ANYREF :NULL), (:REF :NULL) for a
// bare (ref.null), (:HOSTREF n) for (ref.host n); (:EITHER (VAL...)).

function parseSexp(s) {
  let i = 0;
  const out = [];
  function skip() {
    for (;;) {
      while (i < s.length && /\s/.test(s[i])) i++;
      if (s.startsWith(";;", i)) { while (i < s.length && s[i] !== "\n") i++; continue; }
      if (s.startsWith("(;", i)) {
        let d = 0;
        do {
          if (s.startsWith("(;", i)) { d++; i += 2; } else if (s.startsWith(";)", i)) { d--; i += 2; } else i++;
        } while (d > 0 && i < s.length);
        continue;
      }
      return;
    }
  }
  function read() {
    skip();
    if (s[i] === "(") {
      i++;
      const l = [];
      for (;;) { skip(); if (s[i] === ")") { i++; return l; } if (i >= s.length) throw new Error("unclosed list"); l.push(read()); }
    }
    if (s[i] === '"') {
      let j = i + 1;
      while (s[j] !== '"') { if (s[j] === "\\") j++; j++; }
      const t = s.slice(i + 1, j);
      i = j + 1;
      return { str: t };
    }
    let j = i;
    while (j < s.length && !/[\s()]/.test(s[j])) j++;
    const t = s.slice(i, j);
    i = j;
    return t;
  }
  for (;;) { skip(); if (i >= s.length) return out; out.push(read()); }
}

// the bytes of a wast string literal
function strBytes(t) {
  const b = [];
  for (let i = 0; i < t.length; i++) {
    if (t[i] !== "\\") { b.push(...Buffer.from(t[i], "utf8")); continue; }
    const c = t[++i];
    if (/[0-9a-fA-F]/.test(c)) { b.push(parseInt(t.slice(i, i + 2), 16)); i++; }
    else if (c === "n") b.push(10);
    else if (c === "t") b.push(9);
    else if (c === "r") b.push(13);
    else if (c === "u") { const k = t.indexOf("}", i); b.push(...Buffer.from(String.fromCodePoint(parseInt(t.slice(i + 2, k), 16)), "utf8")); i = k; }
    else b.push(c.charCodeAt(0));                    // \" \' \\
  }
  return b;
}
const strText = (t) => Buffer.from(strBytes(t)).toString("utf8");

function intBits(t, n) {
  const s = t.replace(/_/g, "");
  const neg = s.startsWith("-");
  let v = BigInt(s.replace(/^[-+]/, ""));
  if (neg) v = -v;
  return String(BigInt.asUintN(n, v));
}

// exact bit pattern of a float literal as the interpreter prints it
// (hex floats, inf, nan, nan:0x..., nan:canonical/arithmetic)
function floatBits(t, n) {
  const [eb, mb] = n === 32 ? [8, 23] : [11, 52];
  const s = t.replace(/_/g, "");
  if (s === "nan:canonical") return "nan:canonical";
  if (s === "nan:arithmetic") return "nan:arithmetic";
  const neg = s.startsWith("-");
  const a = s.replace(/^[-+]/, "");
  const sign = neg ? 1n << BigInt(n - 1) : 0n;
  const expAll = ((1n << BigInt(eb)) - 1n) << BigInt(mb);
  if (a === "inf") return String(sign | expAll);
  if (a.startsWith("nan")) {
    const p = a.startsWith("nan:") ? BigInt(a.slice(4)) : 1n << BigInt(mb - 1);
    return String(sign | expAll | p);
  }
  const m = /^0x([0-9a-fA-F]*)(?:\.([0-9a-fA-F]*))?(?:p([-+]?[0-9]+))?$/.exec(a);
  if (!m) throw new Error("float literal not in hex form: " + t);
  const frac = m[2] || "";
  let M = BigInt("0x" + ((m[1] || "") + frac || "0"));
  let E = BigInt(m[3] || "0") - 4n * BigInt(frac.length);
  if (M === 0n) return String(sign);
  const bias = (1n << BigInt(eb - 1)) - 1n;
  const L = BigInt(M.toString(2).length);
  const e = L - 1n + E;
  const exact = (x, sh) => {                         // x * 2^sh, which must be an integer
    if (sh >= 0n) return x << sh;
    if (x & ((1n << -sh) - 1n)) throw new Error("inexact float literal: " + t);
    return x >> -sh;
  };
  if (e > bias) throw new Error("float literal overflows: " + t);
  if (e >= 1n - bias) {
    const f = exact(M, BigInt(mb) + 1n - L) - (1n << BigInt(mb));
    return String(sign | ((e + bias) << BigInt(mb)) | f);
  }
  return String(sign | exact(M, E + bias - 1n + BigInt(mb)));
}

const REFNULL = { func: "funcref", extern: "externref", any: "anyref", eq: "eqref", i31: "i31ref",
  struct: "structref", array: "arrayref", exn: "exnref", none: "nullref", nofunc: "nullfuncref",
  noextern: "nullexternref", noexn: "nullexnref" };
const REFANY = { "ref.func": "funcref", "ref.extern": "externref", "ref.i31": "i31ref",
  "ref.struct": "structref", "ref.array": "arrayref", "ref.eq": "eqref", "ref.any": "anyref",
  "ref.exn": "exnref", "ref.host": "hostref" };
const LANES = { i8x16: ["i8", 8], i16x8: ["i16", 16], i32x4: ["i32", 32], i64x2: ["i64", 64],
  f32x4: ["f32", 32], f64x2: ["f64", 64] };

// a value or result pattern -> the {type, value} of wast2json's JSON
function binVal(x) {
  const h = x[0];
  if (h === "i32.const" || h === "i64.const") return { type: h.slice(0, 3), value: intBits(x[1], +h.slice(1, 3)) };
  if (h === "f32.const" || h === "f64.const") return { type: h.slice(0, 3), value: floatBits(x[1], +h.slice(1, 3)) };
  if (h === "v128.const") {
    const [lt, w] = LANES[x[1]];
    return { type: "v128", lane_type: lt, value: x.slice(2).map((l) => (lt[0] === "f" ? floatBits(l, w) : intBits(l, w))) };
  }
  if (h === "ref.null") return x.length > 1 ? { type: REFNULL[x[1]] || x[1] + "ref", value: "null" } : { type: "ref", value: "null" };
  if (REFANY[h]) return x.length > 1 ? { type: REFANY[h], value: String(BigInt(x[1])) } : { type: REFANY[h] };
  if (h === "either") return { type: "either", values: x.slice(1).map(binVal) };
  return { type: String(h) };
}
const nameOf = (x) => (typeof x === "string" && x.startsWith("$") ? x : null);

function binAction(x) {
  let k = 1;
  const module = nameOf(x[k]) ? x[k++] : null;
  const field = strText(x[k++].str);
  if (x[0] === "invoke") return { type: "invoke", module, field, args: x.slice(k).map(binVal) };
  if (x[0] === "get") return { type: "get", module, field };
  throw new Error("action " + x[0]);
}

// the commands of NAME.bin.wast, as wast2json would give them; writes the
// modules to OUT_DIR/NAME.<k>.wasm
function binCommands(n, text) {
  const cmds = [];
  const defs = {};
  let last = null, k = 0;
  const writeModule = (x, from) => {                 // (module [definition] [$D] binary S...)
    const parts = x.slice(from).filter((y) => y && y.str !== undefined);
    const file = `${n}.${k++}.wasm`;
    writeFileSync(join(outDir, file), Buffer.from(parts.flatMap((p) => strBytes(p.str))));
    return file;
  };
  const isDef = (x) => Array.isArray(x) && x[0] === "module" && x[1] === "definition";
  const isInst = (x) => Array.isArray(x) && x[0] === "module" && x[1] === "instance";
  const instFile = (x) => (nameOf(x[3]) ? defs[x[3]] : last);   // (module instance $I? $D?)
  const modOf = (x) => {                             // a module inside an assertion -> its file
    if (isInst(x)) return instFile(x);
    if (x[1] === "binary" || nameOf(x[1])) return writeModule(x, 1);
    throw new Error("module form " + JSON.stringify(x).slice(0, 80));
  };
  for (const x of parseSexp(text)) {
    const h = x[0];
    if (isDef(x)) {
      const file = writeModule(x, 2);
      if (nameOf(x[2])) defs[x[2]] = file;
      last = file;
    } else if (isInst(x)) cmds.push({ type: "module", filename: instFile(x), name: nameOf(x[2]) });
    else if (h === "module") {                       // (module [$M] binary S...): define and instantiate
      const file = writeModule(x, 1);
      last = file;
      cmds.push({ type: "module", filename: file, name: nameOf(x[1]) });
    } else if (h === "register") cmds.push({ type: "register", as: strText(x[1].str), name: nameOf(x[2]) });
    else if (h === "invoke" || h === "get") cmds.push({ type: "action", action: binAction(x) });
    else if (h === "assert_return") cmds.push({ type: "assert_return", action: binAction(x[1]), expected: x.slice(2).map(binVal) });
    else if (h === "assert_trap" && x[1][0] === "module")
      cmds.push({ type: "assert_uninstantiable", filename: modOf(x[1]), text: strText(x[2].str) });
    else if (h === "assert_trap" || h === "assert_exhaustion")
      cmds.push({ type: h, action: binAction(x[1]), text: strText(x[2].str) });
    else if (h === "assert_exception") cmds.push({ type: h, action: binAction(x[1]) });
    else if (h === "assert_invalid" || h === "assert_unlinkable" || h === "assert_uninstantiable")
      cmds.push({ type: h, filename: modOf(x[1]), text: strText(x[2].str) });
    else if (h === "assert_malformed") cmds.push({ type: h, filename: modOf(x[1]), text: strText(x[2].str), module_type: "binary" });
    else cmds.push({ type: String(h) });
  }
  return cmds;
}

const isJson = (n) => existsSync(join(inDir, n, n + ".json"));
const isBin = (n) => existsSync(join(inDir, n, n + ".bin.wast"));
const names = readdirSync(inDir).filter((n) => isJson(n) || isBin(n)).sort();
for (const n of names) {
  const src = `${suite}/${n.replace(/--/g, "/")}.wast`;
  const [cs, how] = isJson(n)
    ? [JSON.parse(readFileSync(join(inDir, n, n + ".json"), "utf8")).commands, ""]
    : [binCommands(n, readFileSync(join(inDir, n, n + ".bin.wast"), "utf8")), " (via the reference interpreter's .bin.wast)"];
  writeFileSync(join(outDir, n + ".lsp"),
    `; GENERATED by gen-spec-tests.mjs from ${src}${how}. Do not edit.\n(\n` +
    cs.map((c) => " " + command(c)).join("\n") + "\n)\n");
}
writeFileSync(join(outDir, "index.lsp"), "(\n" + names.map((n) => " " + str(n)).join("\n") + "\n)\n");
