// demo/driver/sexp.js: a reader for the generated ACL2 data files of the
// conformance tests (translate/tests/spec/data-3.0/*.lsp, written by
// tests/oracle/gen-spec-tests.mjs): lists, strings, integers (BigInt beyond
// 2^53 - 1, as num.js), keywords, NIL and T. Comments start with ';'.
'use strict';
function readSexp(src, L) {
  let i = 0;
  const ws = () => { for (;;) { while (i < src.length && /\s/.test(src[i])) i++; if (src[i] === ';') { while (i < src.length && src[i] !== '\n') i++; } else return; } };
  function read() {
    ws();
    const c = src[i];
    if (c === '(') {
      i++; const xs = [];
      for (;;) { ws(); if (src[i] === ')') { i++; return L.list(xs); } if (src[i] === '.' && /\s/.test(src[i + 1])) { i++; const tail = read(); ws(); i++; let l = tail; while (xs.length) l = new L.I.Cons(xs.pop(), l); return l; } xs.push(read()); }
    }
    if (c === '"') {
      let s = ''; i++;
      while (src[i] !== '"') { if (src[i] === '\\') i++; s += src[i++]; }
      i++; return L.I.make_lisp_string(s);
    }
    let a = ''; while (i < src.length && !/[\s()";]/.test(src[i])) a += src[i++];
    if (/^[-+]?\d+$/.test(a)) { const b = BigInt(a); return (b >= -9007199254740991n && b <= 9007199254740991n) ? Number(b) : b; }
    const up = a.toUpperCase();
    if (up === 'NIL') return L.NIL;
    if (up === 'T') return L.T;
    if (up[0] === ':') return L.kw(up.slice(1));
    throw new Error(`sexp.js: unsupported atom ${a} at ${i}`);
  }
  return read();
}
if (typeof module !== 'undefined') module.exports = readSexp;
