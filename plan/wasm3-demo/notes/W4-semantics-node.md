# The whole semantics in node
- Milestone: W4 (the whole semantics in node)
- Date: 2026-11-15
- Repo commit: baseline results at 0f36ff1 (W7: `results-3.0/` of the
  after-W7 spec run, same `translate/` tree); the work in the W4 commit
- JSCL: 54c8849
- Status: final
- Feeds demo plan: W4, W5 (driver API, host imports), W8 (`%RULE` order)
- Incorporated in demo plan: yes (W4)

## Summary
All 27 books, the extracted t7 driver helpers and the glue load in node
(`wasm3.js` 3.96 MB, 0.13 s after `jscl.js` 0.17 s). The driver
(`demo/driver/glue.lisp`) offers decode, instantiate, invoke with fuel,
host imports through `%HOSTCALL-HOOK`, and t7's own `RUN-CMD`. On the
fixed spec-test-3 subset the JSCL build agrees with ACL2 command by
command: **7,087 of 7,087 commands** in 12 of 12 scripts (the 7,086 `T7-CMD` lines plus one ACL2 CRASH). Speed: 0.32–3.8 ms per step in node; from
about 32× slower than ACL2 (`fac-iter`, at `time$`'s 0.01 s resolution) to 4× faster (`fac-i64` through
`call_indirect`, where node's memoized `acl2-count` saves the size-check
walks that ACL2 repeats).

## Findings

### Driver (item 1)
`demo/driver/glue.lisp` (package `DEMO`), over the extracted
semantics and the t7-lib-3.0 helpers extracted by name (W2); it only turns
multiple values into lists for JS:

| entry | what |
|---|---|
| `DECODE bytes` | `GRAM/BMODULE`, complete parse, or NIL |
| `INSTANTIATE m env`, `DO-ACTION a env` | t7's own, as lists |
| `EMPTY-ENV` | t7's empty environment (`*s0*`, no instances) |
| `LOAD-MODULE bytes env` | decode + t7 `INSTANTIATE`; `(status env')`, the module the current instance |
| `INVOKE env name args fuel` | t7 `DO-ACTION` on `(:invoke nil name args)`, with `*spec-fuel*` bound to FUEL; `(result env')` |
| `REGISTER-HOST env modname bytes` | host imports (item 2) |
| `RUN-CMD c env`, `SPECTEST-ENV` | t7's command runner and its spectest environment; `READ-BYTES` asks the JS host (`DEMOIO.readBytes`) |

Values are t7's: arguments `(:I32 n)`, `(:I64 n)` (unsigned), `(:F32
bits)`, ...; results `((:CONST (:I64) n) ...)` or `:TRAP`, `:EXCEPTION`,
`:FUEL`, `:ERROR`. `driver/lisp.js` and `driver/sexp.js` are the JS side
(Lisp values, the data files' reader).

### Host imports (item 2)
The 3.0 semantics calls a host function, a function instance whose code
is `(:_HOSTFUNC hf)`, through `%HOSTCALL-HOOK` (`rt/builtins-3.0.lisp`):
`(hf store vals)` returns a list headed by `(:RES store' (:_VALS
results))`, or nothing (no rule applies; the run stops there). The glue
attaches `HOST-CALL`, which asks `globalThis.DEMOHOST.call(hf, vals,
none)` (`driver/host.js` is the default: no result). `REGISTER-HOST`
instantiates a module that declares the host functions' signatures, turns
each exported function into `(:_HOSTFUNC (modname field))`, and registers
the instance under MODNAME, as t7's `:register` does; the types are the
semantics' own.
- Facts: the rules pass `(:_HOSTFUNC hf)`, not `hf`; and they call
  `$HOSTCALL` several times per step (a length check, then the binding,
  for each candidate split of the arguments, in both
  `Step/call_ref-hostfunc-res` and `-div`). A host must answer as a
  function of `(hf, vals)`; a host with an effect (the page's `print`)
  records it once per step and argument list.
- `test/host.js` (`make -C demo host`): host `env.inc` (i32 → i32, +1) in
  JS, guest `f(x) = inc(x) * 2`: `f(20) = 42`, the host saw one distinct
  call `env.inc(20)`; with the default host the run stops at the call.
- The spectest module of the conformance runs is an ordinary module
  (`spectest-3.0.wat`: its prints are no-op wasm functions).

### Conformance (item 3)
`test/conformance.js` runs each script's commands in order through t7's
`RUN-CMD` and compares every command's kind and verdict with ACL2's
(`results-3.0/<name>.out`, the after-W7 run of 0f36ff1's tree). ACL2's
verdicts are read per `T7-TRY` as `summarize-3.0.sh` reads them: a TRY
with no `T7-CMD` aborted on a Lisp resource (CRASH, a failure). Aligning
by command matters: in `call_indirect`, ACL2 aborted `fib-i64(20)` (TRY
#72) with no line, and a line-by-line comparison shifted every later
line. A run that ACL2 did not finish (`call_indirect`: `T7-EXIT 137`) is
compared on the commands ACL2 completed (its last, unfinished one is
dropped), and node stops there too ("ACL2 prefix").

| script | commands agreeing | node pass | node time |
|---|---|---|---|
| `i32` | 460/460 | 458 | 1.2 s |
| `i64` | 416/416 | 414 | 0.9 s |
| `f32` | 2,514/2,514 | 2,512 | 4.7 s |
| `f64` | 2,514/2,514 | 2,512 | 4.3 s |
| `memory` | 86/86 | 86 | 0.3 s |
| `call_indirect` (ACL2 prefix, `T7-EXIT 137`) | 77/77 | 76 | 836 s |
| `br_table` | 186/186 | 186 | 6.6 s |
| `simd--simd_i32x4_arith` | 194/194 | 194 | 0.4 s |
| `simd--simd_lane` | 475/475 | 369 | 0.7 s |
| `gc--struct` | 29/29 | 29 | 0.1 s |
| `gc--i31` | 72/72 | 72 | 0.2 s |
| `exceptions--try_table` | 64/64 | 64 | 0.5 s |
| **total** | **7,087/7,087** | | |

The commands that fail in ACL2 fail in node too (the same verdict).
One command fails on both sides in a different way, listed by the
runner: `call_indirect` #72 `fib-i64(20)`, ACL2 CRASH (resource abort),
node `:FUEL` (200,000 steps). `call_indirect` is slow on both sides: ACL2
did not finish it in 600 s (nor 1,200 s, W7 reruns); node needs 836 s for
ACL2's 77 commands, 789 s of them in `fib-i64(20)`. `make -C demo check`
runs the other 11 scripts (`conformance-quick`, about 20 s);
`make -C demo conformance` runs all 12.

### Bugs found by the subset (fixed, not "known differences")
- **Stack (extractor):** `br_table.0.wasm` (a `br_table` with a long label
  vector) overflowed node's stack in `GRAM/BINSTR/REPn`, `$FREE_LIST` and
  `$SHIFT_LABELIDXS`, self-recursions the W2 rewrite did not cover. The
  stack rewrite gained continuations and calls inside clause chains (W2
  note); `br_table` then agrees 186/186.
- **Time (shim):** `acl2-count` was 80% of node's time on call-heavy
  runs: the generated size checks (`%SIZE`) count the inputs of every
  step, about 33,000 conses per `STEP` call on `call_indirect`
  (`data/w4/size-cost.js`). An explicit-stack exact walk (15.2 → 9.8 s
  for `fac-i64(25)`) and memoization by cons identity (→ 2.0 s); W3 note.
- A first comparison by `T7-CMD` line index reported `call_indirect` as
  differing at line #72; it was the CRASH alignment above, not a
  semantic difference. Node's `fib-i64(20)` ends with `:FUEL` (200,000
  steps), so it fails on both sides.

### Timing (item 4)
`data/w4/timing.js` (node) and `timing-acl2.sh` (ACL2, `time$`, the same
invokes through t7-lib-3.0). Steps are top-level `STEP` calls; node:
median of 3 after a warm-up; ACL2: `time$` real time, 3 runs (equal to
the shown precision, 0.01 s).

| invoke | steps | node ms | node ms/step | ACL2 s | node / ACL2 |
|---|---|---|---|---|---|
| `fac.0` `fac-iter(25)` | 367 | 320.9 | 0.874 | 0.01 | ~32× |
| `fac.0` `fac-rec(25)` | 334 | 1,282.3 | 3.84 | 0.73 | 1.8× |
| `call_indirect.0` `fac-i64(25)` | 384 | 1,443.6 | 3.76 | 6.39–6.43 | 0.23× |
| `memory_redundancy.0` `test_redundant_load` | 12 | 5.1 | 0.43 | 0.00 | (below 0.01 s) |
| `br_table.0` `large(100)` | 10 | 3.2 | 0.32 | 0.01 | ~0.3× |

ACL2's 0.011 ms per step (wasm3 M3) matches `fac-iter` here (0.01 s /
367 ≈ 0.027 ms, at `time$`'s resolution). Node's time is spread over
JSCL's generated code (a `LET` is a JS closure call; the profile has no
single hotspot left). Recursive calls make ACL2 slower per step too
(`fac-rec`, `fac-i64`: the configuration grows with the call depth and
the size checks walk it); node's memoized count mostly removes that cost.

### Page impact
For the W5 page, `fac(20)` (240 steps) took 161–183 ms in a Chromium
Worker (W5 note), about the node rate.

## Data
`data/w4/`: `conformance.js`'s output (`conformance.out`, `.json`,
`.raw`), `percmd.js` (time per command), `one-cmd.js`, `size-cost.js`
(+ the `acl2-count` cost), `fib-cache.js` / `fib-cache.out` (memoized
count: `fib-i64(20)` ends with `:FUEL` after 10,697,826 STEP calls, 789 s),
`timing.js` / `timing.out`, `timing-acl2.sh` / `timing-acl2.out`.
