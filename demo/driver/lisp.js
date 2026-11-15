// demo/driver/lisp.js: JS <-> Lisp values for the JSCL build (node and
// browser). Lisp lists are JSCL conses; numbers are canonical (num.js).
'use strict';
function makeLisp(jscl) {
  const I = jscl.internals;
  const NIL = I.intern('NIL', 'COMMON-LISP'), T = I.intern('T', 'COMMON-LISP');
  const fn = (pkg, name) => { const s = I.intern(name, pkg); return (...a) => s.fvalue(...a); };
  const sym = (pkg, name) => I.intern(name, pkg);
  const kw = name => I.intern(name, 'KEYWORD');
  const list = xs => xs.reduceRight((acc, x) => new I.Cons(x, acc), NIL);
  const isCons = x => x instanceof I.Cons;
  function toArray(l) { const r = []; while (isCons(l)) { r.push(l.$$jscl_car); l = l.$$jscl_cdr; } return r; }
  const value = (pkg, name) => I.intern(name, pkg).value;
  // printable form of a Lisp value (for logs and tests)
  function show(x, depth = 0) {
    if (x === NIL) return 'NIL';
    if (x === T) return 'T';
    if (typeof x === 'number' || typeof x === 'bigint') return String(x);
    if (x instanceof globalThis.ACL2N.Q) return globalThis.ACL2N.toString(x);
    if (isCons(x)) {
      if (depth > 40) return '(...)';
      const parts = []; let n = 0;
      while (isCons(x)) { if (n++ > 60) { parts.push('...'); x = NIL; break; } parts.push(show(x.$$jscl_car, depth + 1)); x = x.$$jscl_cdr; }
      if (x !== NIL) parts.push('.', show(x, depth + 1));
      return '(' + parts.join(' ') + ')';
    }
    if (x && x.name !== undefined && x.package !== undefined) return (x.package && x.package.packageName === 'KEYWORD' ? ':' : '') + x.name;
    if (x && x.stringp) return JSON.stringify(x.join(''));
    return String(x);
  }
  return { I, NIL, T, fn, sym, kw, list, isCons, toArray, value, show };
}
if (typeof module !== 'undefined') module.exports = makeLisp;
