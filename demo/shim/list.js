// demo/shim/list.js: the ACL2 list primitives for the JSCL build, as JS
// loops (plan/wasm3-demo W3). Same definitions as in ACL2's axioms.lisp
// (cited in acl2.lisp, which calls these through the FFI). Why JS: JSCL's
// compiled loops cost about 40x SBCL's per element (an IIFE and a type
// check per iteration), and the semantics takes LEN, TRUE-LISTP, EQUAL and
// ACL2-COUNT of the 65,536-element byte list of a memory on memory steps
// (measured: 5.7 s for a 16-instruction run with the Lisp loops).
// Lisp values: conses are instances of JSCL's Cons (passed to init), NIL and
// T the Lisp symbols, numbers canonical (num.js), strings JSCL strings
// (arrays with a stringp mark), characters and symbols compared by identity.
(function () {
  'use strict';
  let C = null, NIL = null, T = null, N = null;
  const isCons = x => x instanceof C;
  const isStr = x => Array.isArray(x) && x.stringp === 1;

  function len(x) { let n = 0; while (x instanceof C) { n++; x = x.$$jscl_cdr; } return n; }
  function trueListp(x) { while (x instanceof C) x = x.$$jscl_cdr; return x === NIL ? T : NIL; }
  function eqStr(a, b) { if (a.length !== b.length) return false; for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return false; return true; }
  function equal(a, b) {                                                 // loop on cdr, recursion on car
    for (;;) {
      if (a === b) return true;
      if (a instanceof C) {
        if (!(b instanceof C) || !equal(a.$$jscl_car, b.$$jscl_car)) return false;
        a = a.$$jscl_cdr; b = b.$$jscl_cdr; continue;
      }
      if (a instanceof N.Q) return b instanceof N.Q && a.n === b.n && a.d === b.d;
      if (isStr(a)) return isStr(b) && eqStr(a, b);
      return false;                                                      // numbers are canonical: === above
    }
  }
  // (acl2-count x): conses 1 + car + cdr; integers |i|; ratios |num| + den;
  // strings their length; else 0. Summed exactly. W4: the generated size
  // checks (rt/prelude.lisp %SIZE) count the inputs of every step, which was
  // 80% of node's time with num.js adds and recursion on CAR (fac(25)
  // through call_indirect: 12.4 of 15.2 s). So: an explicit stack, and a JS
  // number sum moved into a BigInt before it can lose precision.
  const SPILL = 2 ** 52, MAXB = BigInt(Number.MAX_SAFE_INTEGER);
  // Memoized by identity (WeakMap) for subtrees of at least CACHE_MIN: the
  // configurations of successive steps share most of their conses (store,
  // frames), and the extracted code never mutates a cons it has returned
  // (ACL2 is pure; the shim only mutates fresh conses before returning
  // them), so a cached count stays right. Recursion on CAR to depth 1000,
  // then the uncached walk below (countWalk).
  const cache = new WeakMap(), CACHE_MIN = 256;
  function count(x) { return x instanceof C ? countCons(x, 0) : countWalk(x); }
  function countCons(x, depth) {
    const hit = cache.get(x);
    if (hit !== undefined) return hit;
    let s = 0, big = 0n, y = x;
    while (y instanceof C) {
      s += 1;
      const a = y.$$jscl_car;
      if (a instanceof C) {
        const v = depth < 1000 ? countCons(a, depth + 1) : countWalk(a);
        if (typeof v === 'number') s += v; else big += v;
      } else if (typeof a === 'number') s += Math.abs(a);
      else if (typeof a === 'bigint') big += a < 0n ? -a : a;
      else if (a instanceof N.Q) big += (a.n < 0n ? -a.n : a.n) + a.d;
      else if (isStr(a)) s += a.length;
      if (s > SPILL) { big += BigInt(s); s = 0; }
      y = y.$$jscl_cdr;
    }
    if (typeof y === 'number') s += Math.abs(y);
    else if (typeof y === 'bigint') big += y < 0n ? -y : y;
    else if (y instanceof N.Q) big += (y.n < 0n ? -y.n : y.n) + y.d;
    else if (isStr(y)) s += y.length;
    let r = s;
    if (big !== 0n) { big += BigInt(s); r = big <= MAXB ? Number(big) : big; }
    if (r >= CACHE_MIN) cache.set(x, r);
    return r;
  }
  function countWalk(x) {
    let s = 0, big = 0n;
    const stack = [x];
    while (stack.length) {
      let y = stack.pop();
      for (;;) {
        while (y instanceof C) {
          s += 1;
          const a = y.$$jscl_car;
          if (a instanceof C) stack.push(a); else if (a !== NIL) stack.push(a);
          y = y.$$jscl_cdr;
        }
        if (typeof y === 'number') s += Math.abs(y);
        else if (typeof y === 'bigint') big += y < 0n ? -y : y;
        else if (y instanceof N.Q) big += (y.n < 0n ? -y.n : y.n) + y.d;
        else if (isStr(y)) s += y.length;
        if (s > SPILL) { big += BigInt(s); s = 0; }
        break;
      }
    }
    if (big === 0n) return s;
    big += BigInt(s);
    return big <= MAXB ? Number(big) : big;
  }
  // (take n l), (update-nth n v l): NIL-padded; n a natural (nfix'd by the caller)
  function take(n, l) {
    const head = new C(NIL, NIL); let tail = head;
    for (let k = 0; k < n; k++) {
      const c = new C(l instanceof C ? l.$$jscl_car : NIL, NIL);
      tail.$$jscl_cdr = c; tail = c; l = l instanceof C ? l.$$jscl_cdr : NIL;
    }
    return head.$$jscl_cdr;
  }
  function updateNth(n, v, l) {
    const head = new C(NIL, NIL); let tail = head;
    for (let k = 0; k < n; k++) {
      const c = new C(l instanceof C ? l.$$jscl_car : NIL, NIL);
      tail.$$jscl_cdr = c; tail = c; l = l instanceof C ? l.$$jscl_cdr : NIL;
    }
    tail.$$jscl_cdr = new C(v, l instanceof C ? l.$$jscl_cdr : NIL);
    return head.$$jscl_cdr;
  }
  // binary-append: copies x up to its last cons, then y
  function append2(x, y) {
    if (!(x instanceof C)) return y;
    const head = new C(x.$$jscl_car, NIL); let tail = head; x = x.$$jscl_cdr;
    while (x instanceof C) { const c = new C(x.$$jscl_car, NIL); tail.$$jscl_cdr = c; tail = c; x = x.$$jscl_cdr; }
    tail.$$jscl_cdr = y;
    return head;
  }
  function revappend(x, y) { while (x instanceof C) { y = new C(x.$$jscl_car, y); x = x.$$jscl_cdr; } return y; }
  function memberEqual(x, l) { while (l instanceof C) { if (equal(x, l.$$jscl_car)) return l; l = l.$$jscl_cdr; } return NIL; }
  function memberEq(x, l) { while (l instanceof C) { if (x === l.$$jscl_car) return l; l = l.$$jscl_cdr; } return NIL; }
  function assocEqual(x, l) {
    while (l instanceof C) { const p = l.$$jscl_car; if (p instanceof C && equal(x, p.$$jscl_car)) return p; l = l.$$jscl_cdr; }
    return NIL;
  }

  globalThis.ACL2L = {
    init(t, nil, aCons) { T = t; NIL = nil; C = aCons.constructor; N = globalThis.ACL2N; return t; },
    len, trueListp, count, take, updateNth, append2, revappend, memberEqual, memberEq, assocEqual,
    equal: (a, b) => equal(a, b) ? T : NIL,
  };
})();
