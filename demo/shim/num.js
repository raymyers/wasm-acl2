// demo/shim/num.js: the ACL2 number tower for the JSCL build (plan/wasm3-demo
// D5, option A; W1 note). JSCL's numbers are JS doubles only (no bignums, no
// ratios: W0), and the semantics computes with i64/v128 integers and exact
// rationals (rt/builtins.lisp floats). Representation, canonical so that
// EQL/EQUAL keep working:
//   integer  a JS number when |n| <= 2^53 - 1, else a JS BigInt
//   ratio    a Q object {n, d}: BigInts, d > 1, gcd(n, d) = 1
// Every function takes canonical values and returns canonical values;
// predicates return the Lisp T / NIL passed to init(). A non-number where a
// number is required throws (ACL2 would report a guard violation).
// The Lisp side (acl2.lisp) calls these through JSCL's FFI (#j:ACL2N:fn).
(function () {
  'use strict';
  let T = true, NIL = false;
  const MAX = Number.MAX_SAFE_INTEGER, MIN = -MAX;
  const MAXB = BigInt(MAX), MINB = -MAXB;
  const I31 = 2147483647;

  class Q { constructor(n, d) { this.n = n; this.d = d; } }

  const isNum = x => typeof x === 'number';
  const isInt = x => typeof x === 'number' || typeof x === 'bigint';
  const isRat = x => isInt(x) || x instanceof Q;
  function need(x, ok, what) { if (!ok(x)) throw new Error(`ACL2 shim: ${what} expected, got ${String(x)}`); }
  const needInt = x => need(x, isInt, 'integer');
  const needRat = x => need(x, isRat, 'rational');
  const B = x => typeof x === 'bigint' ? x : BigInt(x);
  const norm = b => (b >= MINB && b <= MAXB) ? Number(b) : b;          // BigInt -> canonical
  const bool = c => c ? T : NIL;
  const babs = b => b < 0n ? -b : b;
  function gcd(a, b) { a = babs(a); b = babs(b); while (b) { [a, b] = [b, a % b]; } return a; }
  function mkq(n, d) {                                                   // n/d, d != 0
    if (d < 0n) { n = -n; d = -d; }
    const g = gcd(n, d);
    if (g !== 1n) { n /= g; d /= g; }
    return d === 1n ? norm(n) : new Q(n, d);
  }
  const qn = x => x instanceof Q ? x.n : B(x);
  const qd = x => x instanceof Q ? x.d : 1n;
  const bfloor = (a, b) => { const q = a / b; return (a % b !== 0n && ((a < 0n) !== (b < 0n))) ? q - 1n : q; };

  function add(a, b) {
    if (isNum(a) && isNum(b)) { const r = a + b; if (r >= MIN && r <= MAX) return r; return norm(B(a) + B(b)); }
    needRat(a); needRat(b);
    if (isInt(a) && isInt(b)) return norm(B(a) + B(b));
    return mkq(qn(a) * qd(b) + qn(b) * qd(a), qd(a) * qd(b));
  }
  function neg(a) {
    if (isNum(a)) return a === 0 ? 0 : -a;
    needRat(a);
    return a instanceof Q ? new Q(-a.n, a.d) : norm(-a);
  }
  const sub = (a, b) => add(a, neg(b));
  function mul(a, b) {
    if (isNum(a) && isNum(b)) { const r = a * b; if (r >= MIN && r <= MAX) return r === 0 ? 0 : r; return norm(B(a) * B(b)); }
    needRat(a); needRat(b);
    if (isInt(a) && isInt(b)) return norm(B(a) * B(b));
    return mkq(qn(a) * qn(b), qd(a) * qd(b));
  }
  function div(a, b) {                                                   // exact
    needRat(a); needRat(b);
    if (b === 0) throw new Error('ACL2 shim: division by zero');
    return mkq(qn(a) * qd(b), qd(a) * qn(b));
  }
  function cmp(a, b) {                                                   // -1 0 1
    if (isNum(a) && isNum(b)) return a < b ? -1 : a > b ? 1 : 0;
    needRat(a); needRat(b);
    const x = qn(a) * qd(b), y = qn(b) * qd(a);
    return x < y ? -1 : x > y ? 1 : 0;
  }
  function eqn(a, b) {
    if (isNum(a) && isNum(b)) return a === b;
    needRat(a); needRat(b);
    if (a instanceof Q || b instanceof Q) return a instanceof Q && b instanceof Q && a.n === b.n && a.d === b.d;
    return a === b;                                                      // canonical: number vs BigInt never equal
  }
  // floor/ceiling/truncate/round of a/b for rationals (ACL2: one value)
  function floor(a, b) {
    if (isNum(a) && isNum(b) && b !== 0 && a >= -I31 && a <= I31 && b >= -I31 && b <= I31) return Math.floor(a / b);
    needRat(a); needRat(b);
    if (b === 0) throw new Error('ACL2 shim: floor by zero');
    return norm(bfloor(qn(a) * qd(b), qd(a) * qn(b)));
  }
  function truncate(a, b) {
    if (isNum(a) && isNum(b) && b !== 0 && a >= -I31 && a <= I31 && b >= -I31 && b <= I31) return Math.trunc(a / b) || 0;
    needRat(a); needRat(b);
    if (b === 0) throw new Error('ACL2 shim: truncate by zero');
    return norm((qn(a) * qd(b)) / (qd(a) * qn(b)));
  }
  const ceiling = (a, b) => neg(floor(neg(a), b));
  function round(a, b) {                                                 // nearest, ties to even
    const q = div(a, b), f = floor(q, 1), r = sub(q, f), c = cmp(r, new Q(1n, 2n));
    if (c < 0) return f;
    if (c > 0) return add(f, 1);
    return evenp(f) ? f : add(f, 1);
  }
  const mod = (a, b) => sub(a, mul(b, floor(a, b)));
  const rem = (a, b) => sub(a, mul(b, truncate(a, b)));
  function expt(r, i) {
    needRat(r); needInt(i);
    if (i < 0) return div(1, expt(r, neg(i)));
    if (r === 2 && i <= 52) return 2 ** Number(i);
    if (r instanceof Q) return mkq(r.n ** B(i), r.d ** B(i));
    return norm(B(r) ** B(i));
  }
  function ash(i, c) {
    needInt(i); needInt(c);
    if (isNum(i) && isNum(c)) {
      if (c <= 0) return c > -53 ? Math.floor(i / 2 ** -c) : (i < 0 ? -1 : 0);
      if (c < 53) { const r = i * 2 ** c; if (r >= MIN && r <= MAX) return r; }
    }
    return c >= 0 ? norm(B(i) << B(c)) : norm(B(i) >> B(neg(c)));
  }
  const small = x => isNum(x) && x >= -I31 - 1 && x <= I31;
  function logand(a, b) { if (small(a) && small(b)) return a & b; needInt(a); needInt(b); return norm(B(a) & B(b)); }
  function logior(a, b) { if (small(a) && small(b)) return a | b; needInt(a); needInt(b); return norm(B(a) | B(b)); }
  function logxor(a, b) { if (small(a) && small(b)) return a ^ b; needInt(a); needInt(b); return norm(B(a) ^ B(b)); }
  function lognot(a) { needInt(a); return sub(-1, a); }
  function logbitp(i, j) { needInt(i); needInt(j); return bool(((B(j) >> B(i)) & 1n) === 1n); }
  function integerLength(i) {
    needInt(i);
    let b = B(i); if (b < 0n) b = -b - 1n;
    return b === 0n ? 0 : b.toString(2).length;
  }
  function logcount(i) {
    needInt(i);
    let b = B(i); if (b < 0n) b = -b - 1n;
    let n = 0; for (const ch of b.toString(2)) if (ch === '1') n++;
    return n;
  }
  function evenp(i) { needInt(i); return isNum(i) ? i % 2 === 0 : i % 2n === 0n; }

  globalThis.ACL2N = {
    init(t, nil) { T = t; NIL = nil; return t; },
    Q,
    add, sub, mul, div, neg,
    lt: (a, b) => bool(cmp(a, b) < 0),
    le: (a, b) => bool(cmp(a, b) <= 0),
    gt: (a, b) => bool(cmp(a, b) > 0),
    ge: (a, b) => bool(cmp(a, b) >= 0),
    eq: (a, b) => bool(eqn(a, b)),
    eqRaw: eqn,                                                          // JS boolean (for EQUAL in JS)
    min: (a, b) => cmp(a, b) <= 0 ? a : b,
    max: (a, b) => cmp(a, b) >= 0 ? a : b,
    abs: a => cmp(a, 0) < 0 ? neg(a) : a,
    signum: a => cmp(a, 0),
    floor, ceiling, truncate, round, mod, rem, expt, ash,
    logand, logior, logxor, lognot, logbitp, logcount, integerLength,
    evenp: i => bool(evenp(i)),
    oddp: i => bool(!evenp(i)),
    zerop: a => bool(eqn(a, 0)),
    plusp: a => bool(cmp(a, 0) > 0),
    minusp: a => bool(cmp(a, 0) < 0),
    numerator: x => { needRat(x); return x instanceof Q ? norm(x.n) : x; },
    denominator: x => { needRat(x); return x instanceof Q ? norm(x.d) : 1; },
    integerp: x => bool(isInt(x)),
    rationalp: x => bool(isRat(x)),
    isRat,                                                               // JS boolean
    q: (n, d) => mkq(B(n), B(d)),
    big: s => norm(BigInt(s)),
    toString: x => x instanceof Q ? `${x.n}/${x.d}` : String(x),
  };
})();
