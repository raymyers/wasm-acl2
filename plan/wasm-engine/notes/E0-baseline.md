# Baseline: the generated 3.0 semantics runs 20,000 to 40,000 steps per second, and three costs grow with the program

- Milestone: E0 (all four items)
- Date: 2026-11-15
- Repo commit: e0b7898 plus this note's commit
- Status: final
- Feeds engine plan: E0, E5 (machine design, confirmed), E6, E7 (go/no-go), E9 (host layer), §5 (risks)
- Incorporated in engine plan: yes (E0, "Current state")

## Summary

- On flat code (a counting loop, a factorial loop, nested blocks, a
  `try_table` that catches a `throw`) the generated `STEP` makes **23,000
  to 40,000 steps per second** (25 to 43 µs a step), the same at 1, 16
  and 64 pages of memory.
- Three costs grow with the program. The engine of E6/E7 removes each of
  them by design:
  1. **Memory size.** Each `load` and `store` costs time proportional to
     the memory: 20,652 steps/s at 1 page, 4,366 at 16, 1,261 at 64. The
     cause is the out-of-bounds rules, which `STEP` tries before the
     in-bounds rules. They take the length of the memory's byte list.
  2. **Call depth.** A recursive call chain of depth d takes time
     proportional to d³ (d steps, each costing d²): 5,036 steps/s at depth
     10, 80 at depth 100, 36 at depth 150. The cause is the termination
     check, `ACL2-COUNT` of the inner term before each recursive context
     premise (69% of the time at depth 50).
  3. **Memory at instantiation.** `$ALLOCMEM/ITER2` builds the byte list
     by plain recursion. With SBCL's default 64 MB control stack it fails
     near 2.09 million bytes (32 pages). The benchmarks at 64 pages need
     `SBCL_USER_ARGS='--control-stack-size 1000'`. MuPDF has 352 pages.
- On flat code, **allocation is the main cost: about 9 KB per step**,
  made by the rule functions that are tried and fail before the one that
  fires. Zeroing fresh allocation regions (`__bzero`) is 67% to 96% of the
  CPU samples. GC is not the cost: one collection in the whole counting
  run, and shrinking the nursery to 64 MB changes the time by 1.5%.
- `STEP` returns `NIL` (no rule applies) or a list of exactly one
  configuration. This held at every step of every probe. A trap ends as
  `((:TRAP))` and an uncaught exception as `((:REF.EXN_ADDR a)
  (:THROW_REF))`, and `STEP` of either is `NIL`.

## Findings

### Benchmarks (item 1)

`engine/bench/`: six WAT programs, each exporting `run` (and `fac.wat`
also `run_rec`), each assembled with its memory at 1, 16 and 64 pages
(`build.sh`, wabt from `nix develop`). `bench.lsp` takes each `.wasm`
through the generated decoder (`GRAM/BMODULE`), `$instantiate` (with
`Module_ok`) and `$invoke`, then iterates `STEP` until it returns `NIL`.
Only the `STEP` loop is timed (`read-run-time`). `run.lsp` is the run.

| Program | What one iteration does | Steps per iteration |
|---|---|---|
| `count` | the M3 counting loop: `br_if` out, `i32.sub`, `br` back | 8 |
| `memloop` | the same with one `i32.store` and one `i32.load` at address 0 | 12 |
| `nested` | enter 8 nested blocks, `br` out of all 8 | 24 |
| `throw` | call a function that throws tag `$e`; a `try_table` around the call catches it | 23 |
| `fac` | the demo's factorial: the loop (`run`) and the recursion (`run_rec`) | 12 (loop) |
| `calls` | `run(n) = n + run(n-1)`: a call chain of depth n | 13 per level |
| `trap` | (not timed) `7 / x` and an uncaught `throw`, for item 4 | |

Every result was checked: `count` and `nested` return 0, `memloop` 1,
`throw` with n = 3000 returns 4,501,500 (= 3000·3001/2), `fac` with
n = 20 returns 2,432,902,008,176,640,000, `calls` with n = 100 returns
5,050.

### Rates (item 2)

`data/e0-baseline/bench-raw-1.out` and `bench-calls.out`. M1 Max, SBCL
2.6.6, ACL2 8.7 (`acl2-with-wasm-books`), 2026-11-15. While these runs
were made, a MuPDF build was using other cores (load average 4 to 5 of
10). The counting loop measured alone later gave the same rate (40,100
steps/s in `profile-raw.out`).

| Program | n | Steps | 1 page | 16 pages | 64 pages |
|---|---|---|---|---|---|
| `count` | 20,000 | 160,011 | 39,604 | 40,610 | 40,447 |
| `memloop` | 10,000 | 120,011 | **20,652** | **4,366** | **1,261** |
| `nested` | 5,000 | 120,011 | 24,872 | 24,664 | 25,148 |
| `throw` | 3,000 | 69,011 | 23,515 | 23,543 | 23,398 |
| `fac` (loop) | 10,000 | 120,000 | 32,238 | 32,424 | 32,323 |
| `fac` (`run_rec`) | 20 | 255 | 1,591 | 1,612 | 1,604 |

Steps per second. Call chain, 1 page only:

| Depth n | Steps | Time | Steps/s |
|---|---|---|---|
| 10 | 138 | 0.027 s | 5,036 |
| 25 | 333 | 0.312 s | 1,068 |
| 50 | 658 | 2.18 s | 302 |
| 100 | 1,308 | 16.3 s | 80 |
| 150 | 1,958 | 54.2 s | 36 |

From 50 to 100 the time grows 7.5 times, and from 100 to 150 3.3 times
(cubes: 8 and 3.4). Depths 300 and 1,000 were started and stopped after
several minutes. At depth 300 the formula gives about 7 minutes.

For comparison, wasm3 M3 gave 0.011 ms a step for the counting loop on a
configuration built by hand. That bench, re-run today on the current
books, gives 0.015 ms a step over 327 steps. Here, through
`$instantiate` and `$invoke`, it is 0.025 ms. Two things differ: the body
here runs inside a `FRAME_` and the function's `LABEL_`, which are two
more context levels, and the runs here are 490 times longer. The two were
not measured apart.

### Profile (item 3)

`engine/bench/profile.lsp`: SBCL `sb-sprof` in cpu mode, 1 ms interval,
graph reports in `data/e0-baseline/profile-raw.out`. `classify.py`
assigns each function's self samples to a class by name. Samples in
`__bzero` and `_platform_memset` are SBCL zeroing a fresh allocation
region. They are charged to the callers of `__bzero` in proportion to the
caller counts of the graph. The result is `profile-classified.txt`.

sb-sprof names no member of a mutual-recursion clique here ("Unknown fn
N"). From the graph, these are the relation functions themselves: the one
that `STEP/R-PURE` calls and that calls every `STEP_PURE/R-*` is
`STEP_PURE`, and the one that calls every `STEP/R-*` is `STEP`. They are
a class of their own below.

Share of CPU time, with allocation charged to its caller:

| Class | `count` | `nested` | `memloop` 16 pages | `calls` depth 50 |
|---|---|---|---|---|
| rule matching: rule functions and their `SEARCH`/`MATCH` helpers | 58.9% | 45.2% | 26.5% | 16.7% |
| relation functions `STEP`, `STEP_PURE`, `STEP_READ` | 36.6% | 30.1% | 15.1% | 10.8% |
| termination check (`ACL2-COUNT`, its `+`) | 0.9% | 14.8% | 3.1% | **69.3%** |
| list and shape tests (`TRUE-LISTP`, `LEN`, `TAKE`, `*-P`) | 1.4% | 6.1% | 2.3% | 2.4% |
| contexts: `STEP/R-CTXT-*`, `STEP/SEARCH*` (own time) | 1.5% | 2.3% | 0.9% | 0.5% |
| store and memory | 0.1% | 0.7% | **51.5%** | 0.0% |
| of which allocation (`__bzero`, memset) | 95.5% | 67.3% | 40.0% | 24.5% |

Bytes consed (`sb-ext:get-bytes-consed`, without the profiler):
`count` 1,466 MB for 160,011 steps (9.2 KB a step), `nested` 1,069 MB
for 120,011 (8.9 KB), `memloop` at 16 pages 389 MB for 2,000 iterations,
`calls` at depth 50 75 MB for 658 steps. GC time was 0 ms in all four.
`gc-probe.lsp` re-ran the counting loop with the nursery at ACL2's 1.6
GB, 256 MB, 64 MB and 16 MB: 1, 6, 22 and 88 collections, 3,975, 4,048,
4,033 and 4,473 ms of real time (`gc-probe.out`). The cost is the allocation itself, not collection.

The classes the plan asked for, ranked:

1. **Rule matching, by allocation.** On flat code nearly all the time
   goes to rules that are tried and fail. `STEP` tries its rules in
   order, and each rule function and its `SEARCH`/`MATCH` helpers build
   candidate splits of the instruction list before failing. About 9 KB a
   step. The machine's `case` on the head instruction (E5) removes the
   search.
2. **The termination check, by depth.** Before each recursive premise the
   generated code compares `%SIZE` of the inner term with the outer
   (`ACL2-COUNT`). A step at depth d makes d such checks of terms of size
   about d, so it costs d². At depth 50 this is 69% of the time, and at
   depth 100 a step takes 12 ms. MuPDF's call depth was not measured. The
   machine has no such check: its contexts are an explicit stack (E5).
3. **The store, by memory size.** In `memloop` at 16 pages, 51% of the
   time is in two rule functions, `STEP_READ/SPLIT/R-LOAD-NUM-OOB` (26.9%)
   and `STEP/R-STORE-NUM-OOB` (24.2%). These are the out-of-bounds rules.
   They come before the in-bounds rules, and their premise takes the
   length of the memory's byte list. So every load and store walks the
   whole memory. The machine checks bounds against a stored length (E7
   stobj: an array size).
4. **Contexts and term rebuilding, own time**: 0.5% to 2.3%. Small,
   except for the allocation of the searches that `STEP/SEARCH21`
   (`ctxt-instrs`) makes, which is charged to rule matching above.

### Instantiation at 64 pages and MuPDF's 352

`$ALLOCMEM/ITER2` in `gen/wasm-3.0/4_4-execution_modules.lisp` is
`(CONS 0 ($ALLOCMEM/ITER2 (+ 1 K) N))`. It is not tail-recursive, so it
uses one stack frame per byte. The backtrace of the 64-page failure
(`Control stack exhausted`) ends at `($ALLOCMEM/ITER2 2092918 4194304)`.
With `SBCL_USER_ARGS='--control-stack-size 1000'` (1,000 MB; the
`acl2` launcher passes `SBCL_USER_ARGS` to SBCL after its own
`--control-stack-size 64`, and the later one wins) every 64-page
benchmark instantiates. MuPDF's 23,068,672 bytes need about 11 times
2.09 million frames. E1 item 5 and E9 run with 4,000 MB.

This is an execution-time property of the generated book, not an error
in it. The book is the specification and is not changed (step.md). The
engine's own loader (E6) allocates memory without recursion.

### What STEP returns (item 4)

`probe-step.lsp`, `data/e0-baseline/probe-step.out`. It records the shape
of every `STEP` result in four runs (the counting loop with n = 50, the
throw loop with n = 5, `7 / 0`, an uncaught `throw`):

| Run | Results of length 1 | `NIL` | Final instructions |
|---|---|---|---|
| `count` 50 | 411 | 1 | `((:CONST (:I32) 0))` |
| `throw` 5 | 126 | 1 | `((:CONST (:I32) 15))` |
| `div` 0 | 5 | 1 | `((:TRAP))` |
| `uncaught` 3 | 5 | 1 | `((:REF.EXN_ADDR 0) (:THROW_REF))` |

So `STEP` is a function to "zero or one configuration": a list of one
configuration, or `NIL` when no rule applies. It returns the result of
the first rule function that fires (E5). A configuration is
`(:|%;%| (:|%;%| store frame) instrs)`. There is no separate trap
result. A trap is the instruction list `((:TRAP))`, on which no rule
fires. The same holds for a value list and for an uncaught exception.
E3's constraint C3 (a value sequence does not step, `TRAP` alone does
not step) states exactly this, and the probe agrees for the cases it
ran.

## What this means for the engine

- E5's design is confirmed on the three points that the profile ranks
  first: dispatch on the head instruction instead of trying rules in
  order, an explicit control stack instead of nested terms with a size
  check, and a stored memory length. No finding here asks for a change
  of the design.
- The E7 go/no-go compares the machine's rate with these rates. Flat
  code: 23,000 to 40,000 steps/s. Code with memory traffic at MuPDF's
  352 pages: below 1,261 steps/s (the 64-page rate). Call depth: d²
  per step.
- E6's differential test runs the spec next to the machine. On deep
  recursion and large memories the spec side is slow, so test programs
  should keep call depth under about 50 and memory small.

## Open questions

- MuPDF's call depth and the share of loads and stores in its instruction
  stream. These decide how slow the spec is on it. They are not needed
  for the engine, only for E9's expectations of the spec as an oracle.
- Why the relation functions themselves are charged 11% to 37% of the
  allocation. The graph says they call `__bzero` directly, which suggests
  inlined rule bodies or `LET` bindings that cons. This was not looked
  into, since the engine does not use them.

## Data

`engine/bench/`: `*.wat`, `build.sh`, `bench.lsp`, `run.lsp`,
`profile.lsp`, `gc-probe.lsp`, `probe-step.lsp`, `trap.wat`. Wasm files are made by
`build.sh` and are not checked in.
`data/e0-baseline/`: `bench-raw-1.out` (the rate table; the run was
stopped during the call chain at depth 300), `bench-calls.out` (the call
chain table), `profile-raw.out`, `classify.py`,
`profile-classified.txt`, `gc-probe.out`, `probe-step.out`.
