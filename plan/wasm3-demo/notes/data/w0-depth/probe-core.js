// W0 item 4: largest n for which each probe of probe.lisp returns (binary
// search; a stack overflow is caught). Shared by node and the browsers.
function w0Probe(jscl) {
  const I = jscl.internals;
  const pkg = 'COMMON-LISP-USER';
  const call = (name, ...a) => I.intern(name).fvalue(...a);
  const ok = (name, args) => { try { call(name, ...args); return true; } catch (e) { return false; } };
  function maxN(name, mk) {
    let lo = 0, hi = 1024;
    while (ok(name, mk(hi)) && hi < (1 << 20)) { lo = hi; hi *= 2; }
    if (hi >= (1 << 20)) return '>=' + lo;
    while (hi - lo > 1) { const m = (lo + hi) >> 1; if (ok(name, mk(m))) lo = m; else hi = m; }
    return lo;
  }
  function plainJs(n) { return n === 0 ? 0 : 1 + plainJs(n - 1); }
  let lo = 0, hi = 1024;
  const jsOk = n => { try { plainJs(n); return true; } catch (e) { return false; } };
  while (jsOk(hi) && hi < (1 << 22)) { lo = hi; hi *= 2; }
  while (hi - lo > 1) { const m = (lo + hi) >> 1; if (jsOk(m)) lo = m; else hi = m; }
  return {
    'W0-ITER (allocmem shape)': maxN('W0-ITER', n => [0, n]),
    'EQUAL on two n-lists': maxN('W0-EQUAL', n => [n]),
    'APPEND of an n-list': maxN('W0-APPEND', n => [n]),
    'plain JS recursion': lo,
  };
}
if (typeof module !== 'undefined') module.exports = w0Probe;
