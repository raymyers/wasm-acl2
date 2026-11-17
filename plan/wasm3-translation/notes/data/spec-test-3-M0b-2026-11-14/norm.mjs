// normalize an .lsp command list for comparing the two converters
import { readFileSync } from "node:fs";
const W = { I8: 8, I16: 16, I32: 32, I64: 64, F32: 32, F64: 64 };
let t = readFileSync(process.argv[2], "utf8").split("\n").filter((l) => !l.startsWith(";") && !l.includes(":ASSERT_MALFORMED")).join("\n");
t = t.replace(/"[^"]*\.(wasm|wat)"/g, "F");
// v128 with numeric lanes -> 16 little-endian bytes
t = t.replace(/\(:V128 :(I8|I16|I32|I64|F32|F64) \(([^()]*)\)\)/g, (m, lt, ls) => {
  if (/NAN/.test(ls)) return m.replace(/:(I8|I16|I32|I64|F32|F64) /, ":" + lt + " ");
  const w = W[lt], bytes = [];
  for (const l of ls.trim().split(/\s+/)) { let v = BigInt.asUintN(w, BigInt(l)); for (let i = 0; i < w / 8; i++) { bytes.push(Number(v & 255n)); v >>= 8n; } }
  return "(:V128 :BYTES (" + bytes.join(" ") + "))";
});
t = t.replace(/\(:[A-Z]*REF :NULL\)/g, "(NULL)").replace(/\(:FUNCREF (0|:ANY)\)/g, "(FUNC)");
t = t.replace(/\(:UNSUPPORTED "either"\)/g, "(EITHER)").replace(/\(:EITHER \((?:[^()]|\([^()]*\)|\((?:[^()]|\([^()]*\))*\))*\)\)/g, "(EITHER)");
console.log(t);
