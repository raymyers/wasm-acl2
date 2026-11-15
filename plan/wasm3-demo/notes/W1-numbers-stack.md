# Numbers and stack: the D5 design, confirmed
- Milestone: W1 (numbers and stack, confirm D5)
- Date: 2026-11-15
- Repo commit: d716fa8 (W0 numbers); JSCL 54c8849
- Status: final
- Feeds demo plan: D5, W2 items 6 and 7, W3
- Incorporated in demo plan: yes (D5 final, W1)

## Summary
The user's conditional decision D5 (numbers by option A, a shim tower;
stack by option (b), a mechanical rewrite of self-recursion in the
extractor; node `--stack-size` / worker stack and the Worker as fallback)
is **final**. Both conditions hold on W0's measurements: option A costs at
most 4.04× plain JSCL on the sample (limit 20×), and the only recursion
that overflows (65,541 frames on a 1-page module) is `$ALLOCMEM/ITER2`
calling itself, tail recursive modulo `cons`.

## Numbers

### Options
- **(A) Shim tower in Lisp** (chosen). The demo's packages shadow the CL
  numeric functions the extracted code uses (`+ - * / < <= > >= = floor
  mod rem truncate ceiling expt ash logand logior logxor lognot logbitp
  logcount integer-length numerator denominator integerp rationalp`, plus
  `1+ 1- min max evenp` and the comparisons hidden in `zp`, `natp`,
  `nfix`, `ifix`...) and `equal`. Integers are canonical: a JS number when
  |n| ≤ 2^53 − 1, a JS `BigInt` otherwise, normalized after every
  operation, so `eql` on fixnums keeps working and a BigInt never equals a
  number by accident. Ratios are a normalized struct (numerator,
  denominator > 1, coprime). JSCL itself is unchanged.
- (B) Patch JSCL's number tower with BigInt and ratios: a fork to carry
  (perhaps upstreamable), and every JSCL primitive that checks
  `typeof == "number"` (W0: `+` throws a type error on a BigInt) would
  change. Rejected by D5.
- (C) Change the encodings in `rt/`: rejected, `rt/` is source of truth.

### How the extracted code reaches the tower
The extractor prints every symbol package-qualified (W0 item 2). For the
shadowed names it prints the shim's symbol instead of `COMMON-LISP::X`
(a closed list in the extractor, reported in W2's run report), so no
generated or rt/ source changes. Ratio literals (3, in `rt/builtins.lisp`)
become a shim constructor call (W0 item 2: JSCL reads `1/2` as a symbol,
silently).

### Cost (W0 item 5)
| op | tower / plain JSCL |
|---|---|
| `+` | 3.24 (3.03) |
| `*` | 3.28 (3.06) |
| `floor` | 3.93 (4.04) |
| `logand` | 0.14 (0.14) |
| `ash` left / right | 0.89 / 0.75 (0.86 / 0.74) |

(two runs; prototype in `data/w0-numbers/tower.lisp`). **D5 (i)** asked
for at most 20×: the maximum is 4.04×. Holds.

## Stack

### Measured (W0 item 4)
- Deepest recursion of the generated semantics on a 1-page module:
  decode 33, instantiate **65,541** (65,537 frames of
  `$ALLOCMEM/ITER2`), invoke 38.
- JSCL frames of that shape that fit: node 9,695 (default), 55,095
  (`--stack-size=3900`), 229,711 (worker thread, `stackSizeMb: 16`);
  Chromium Worker 2,047, Firefox Worker 4,095, Chromium page 6,655,
  Firefox page 30,927.
- JSCL's own `equal` and `append` recurse on `cdr` (2,951 / 1,705 elements
  in a Firefox Worker, 1,599 / 621 in a Chromium Worker).

### Options
- (a) node `--stack-size` / a worker thread with a larger stack, and a
  browser Worker: enough in node (worker, 16 MB), **not** in browsers,
  which give a Worker no way to ask for more stack. Kept as the fallback
  for node only.
- **(b) Mechanical rewrite in the extractor** (chosen): for a
  self-recursive function, the same rewrite for every function:
  tail calls into a loop; tail recursion modulo `cons` (the recursive call
  is the last argument of a `cons` that is the result) into an
  accumulate-and-reverse loop. Checked by W3/W4 like everything else the
  extractor writes. Covers `$ALLOCMEM/ITER2`
  (`(IF (< K N) (CONS 0 (REC (+ 1 K) N)) NIL)`).
- (c) Shim overrides for named hot functions: rejected, it duplicates
  semantics; only if (b) cannot cover a function that W3/W4 show to
  overflow.

The shim's `equal`, `append`, `len`, `acl2-count`, `take`, `update-nth`,
`true-listp` and friends are written as loops (§3 already planned this).

**D5 (ii)** asked that the overflowing recursion be self-recursion of a
shape (b) can remove: it is (`$ALLOCMEM/ITER2`, tail recursive modulo
`cons`). Holds.

### What (b) does not cover (to watch in W2-W4)
Recursions whose depth grows with the input and whose result is built
after the recursive call in a non-`cons` way: `GRAM/BEXPR/REP2` (one frame
per instruction of a function body), `$FREE_*/ITER*`, `SEQ-RUN` (the
`Instrs_ok` sequencer), `%COMP-FIELDS`. On W0's module they stay at 17 or
less. With about 2,000 JSCL frames in a Chromium Worker, a function body
of a few thousand instructions would overflow; the demo's examples are
far smaller. W2's report lists every self-recursive function and whether
(b) rewrote it; a limit found later is recorded as a demo limit (or, if
it bites the W4 subset, handled under (c) with its reason written next
to it).

**Later (W4, recorded in W2-extractor):** the W4 subset hit this case:
`br_table.0.wasm` (a `br_table` with a long label vector) overflows node's
default stack in `GRAM/BINSTR/REPn`, `$FREE_LIST` and `$SHIFT_LABELIDXS`,
all self-recursive. (b) was extended there, still one mechanical rewrite
for every function (continuations for a call that is bound or passed on,
and calls inside clause chains), not (c). D5 (ii) still holds: every
overflow found is self-recursion.

## D5 final
Both conditions hold. D5 is final: option A for numbers, (b) for the
stack, (a) as the node-only fallback. No stop for the user.

## Data
W0's data: `data/w0-numbers/` (cost), `data/w0-depth/` (depth and stack
capacity). No new measurement in W1.
