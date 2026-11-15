// W0 item 5: BigInt slow paths of the prototype tower (tower.lisp).
globalThis.W0BIG = {
  norm: b => (b >= -9007199254740991n && b <= 9007199254740991n) ? Number(b) : b,
  add: (a, b) => BigInt(a) + BigInt(b),
  mul: (a, b) => BigInt(a) * BigInt(b),
  floor: (a, b) => { a = BigInt(a); b = BigInt(b); const q = a / b; return (a % b !== 0n && ((a < 0n) !== (b < 0n))) ? q - 1n : q; },
  logand: (a, b) => BigInt(a) & BigInt(b),
  ash: (x, y) => y >= 0 ? BigInt(x) << BigInt(y) : BigInt(x) >> BigInt(-y),
};
