# The shim and the numerics in node (demo/shim)
- Milestone: W3 (shim and numerics in node)
- Date: 2026-11-15
- Repo commit: see the W3 commit (built on the W7 tagged gen/wasm-3.0 and the W2 extractor)
- JSCL: 54c8849
- Status: final
- Feeds demo plan: W3, W4, W5
- Incorporated in demo plan: yes (W3)

## Summary
`demo/shim/` is the ACL2 layer under JSCL: the D5 number tower
(`num.js`, option A), the hot list functions as JS loops (`list.js`), the
ACL2 definitions the books call (`acl2.lisp`) and the W7 tag (`rule.lisp`,
the identity until W8). The extractor's list of ACL2 functions called but
not defined (W2 report: 59 names in package ACL2) is covered, 0 left. On
the JSCL build in node: numeric vectors **8,724/8,724**, SIMD vectors
**1,008/1,008** (480 relaxed; full profile 480/480), shim unit tests
**119/119** against values printed by ACL2. `make -C demo vectors units`.

## Findings

### Shim contents (each with its reason in the source)
| part | what | reason |
|---|---|---|
| `num.js` (`globalThis.ACL2N`) | integers: JS number when \|n\| ≤ 2^53 − 1, else `BigInt`; ratios: `Q{n,d}` (BigInts, normalized) | D5 A: JSCL has doubles only; canonical values keep `EQL` working (W1) |
| | `add sub mul div neg`, `lt le gt ge eq`, `min max abs signum`, `floor ceiling truncate round mod rem` (int31 fast path; `round` to even), `expt ash logand logior logxor lognot logbitp logcount integerLength`, `evenp oddp zerop plusp minusp integerp rationalp numerator denominator`, `q`, `big` | the numeric CL functions the extractor prints as `ACL2::` (W2 `+SHADOWED+`) |
| `acl2.lisp`, numbers | macros `ACL2::+ * - / 1+ 1- < > <= >= = /= ...` expanding to the `#j:ACL2N:` call | no extra Lisp frame on the hot path |
| | `%Q`, `%BIG` | literals the extractor rewrote (JSCL reads `1/2` as a symbol) |
| | `natp posp zp nfix ifix rfix` | ACL2 definitions (axioms.lisp), on the tower |
| `list.js` (`globalThis.ACL2L`) | `equal len trueListp count take updateNth append2 revappend memberEqual memberEq assocEqual` | JSCL's `EQUAL`/`APPEND` recurse on `CDR` (a Chromium Worker holds about 1,600 frames, W0 item 4), and `LOOP` costs a JS exception per iteration |
| `list.js` `count` (`ACL2-COUNT`) | an explicit stack, an exact sum (JS number, spilled into a `BigInt` before 2^53), memoized by cons identity (`WeakMap`) for subtrees of at least 256 | found in W4: the generated size checks (`rt/prelude.lisp` `%SIZE`) count the inputs of every step, about 33,000 conses per `STEP` call on `call_indirect`; `fac-i64(25)` there took 15.2 s, 80% in `count`; 9.8 s with the stack walk, 2.0 s memoized (`data/w4/size-cost.js`). Sound because the extracted code never mutates a cons it has returned (ACL2 is pure; the shim mutates only fresh conses before returning them) |
| `acl2.lisp`, lists | `EQUAL LEN TRUE-LISTP APPEND REVERSE TAKE UPDATE-NTH MEMBER-EQUAL MEMBER-EQ ASSOC-EQUAL ACL2-COUNT` on `list.js`; `PUT-ASSOC-EQUAL ALISTP REMOVE-DUPLICATES-EQUAL SUBSETP-EQUAL IFF HONS-COPY MAKE-ORD` as `WHILE` loops | ACL2 functions called by the books, not in JSCL (or wrong there) |
| | `MV`, `MV-LET` | `VALUES`, `MULTIPLE-VALUE-BIND` |
| | `%DEFATTACH`, `%MEMOIZE`, `INTERN$` | events the extractor maps (W2); `%MEMOIZE` is the identity (performance only) |
| | `WHILE` | `jscl-xc::%while`: a plain JS `while` |
| `rule.lisp` | `WRT::%RULE` = its result | W7 tags; the W8 recorder replaces it |

### Facts learned
- A JS `true`/`false` returned through the FFI is a Lisp true value
  either way (JS `false` is not `NIL`): every predicate in `num.js` and
  `list.js` returns the Lisp `T`/`NIL` handed to `init()`.
- JSCL's own `EQL` works on `BigInt` (by value), so the canonical
  representation is enough for `EQL`, `MEMBER`, `ASSOC` with `EQL` tests.
- ACL2's `ZP` outside its guard (`(zp -1)`, `(zp 1/2)`) differs between
  the logic and raw Lisp; the unit tests use in-guard inputs only, as the
  semantics does.

### Vector runner (item 2)
The runner re-implements no test logic: the extractor pulls the test
books' own checking functions by name (`CHECK-VECTORS` and helpers from
`tests/sem-3.0/t3-numerics-3.0.lisp`, `CHECK-SIMD` from
`t3-simd-3.0.lisp`) into `demo/build/lisp/tests/`, and converts the data
files to JSON (`data/*.json`). `test/vectors-glue.lisp` turns their
multiple values into a list; `test/vectors.js` reads the JSON into Lisp
values and prints the counts.

| run | result | ACL2 count |
|---|---|---|
| numerics (1.0 + 2.0 vectors) | 8,724/8,724 (8,015 from 1.0, 709 2.0-only), 243 ms | 8,724 (wasm3 M1) |
| SIMD (deterministic profile) | 1,008/1,008, 356 ms | 1,008, 480 relaxed |
| SIMD, full relaxed profile | 480/480 | 480 |

### Unit tests (item 3)
`test/units.lsp`: 119 forms (`equal` on numbers, strings, symbols, nested
and dotted lists; `acl2-count`; ratios: arithmetic, `floor`/`ceiling`/
`truncate`/`round`/`mod`/`rem` with negative operands, `numerator`;
bignums: 2^53 ± 1, 2^64, 2^128, `ash` both ways, `logand`/`logior`/
`logxor`/`lognot` on negatives, `logbitp`, `logcount`, `integer-length`,
`expt`; list functions). The extractor evaluates them in ACL2 and writes
the printed values (`tests/units-expected.json`); `test/units.js`
compares them, as printed strings, with the JSCL results: 119/119 agree.

## Data
`make -C demo vectors units` (the output lines above); inputs regenerate
with `make -C demo extract`.
