# Runtime baseline of the generated 1.0 semantics

- Milestone: P6 (all three items: measure; decide the 3.0 approach; list
  where `:program` code can crash)
- Date: 2026-11-14
- Repo commit: 3f31c9a (measurements); this note's commit
- Machine: 10-core aarch64-darwin, 69 GB, SBCL ACL2 8.7 (flake)
- Status: final for the measurements; the approach is a recommendation
- Feeds wasm3 plan: risks, milestones (runtime), scheme delta
- Incorporated in wasm3 plan: no

## Summary

A step without memory costs **0.03-0.05 ms**. With memory it costs **about
10.4 ms per 64 KiB page, on every step**, whether or not the step touches
memory: 15.1 ms at 1 page, 62.8 ms at 4 pages, 181 ms at 16 pages. The cost
equals about 19 full traversals of the configuration per step (one `%SIZE` =
`acl2-count` costs 0.80 ms at 1 page and 3.39 ms at 4 pages). These are the
generated termination checks, not memory access itself (a load plus a store
per iteration adds about 1 ms). All five spec-test-1 crashes build huge
lists (locals, `memory.grow`, segment bounds); none is in `:program` code.
Estimate for spec-test-3 (228 convertible scripts) at today's speed: about
1.5-2 h wall with 8 sessions, plus a tail of scripts at the time limit.

## Findings

### Item 1: measurements

`bench.lsp`: counting loop `count(n)` under the generated `STEP`, steps to
normal form, `read-run-time`:

| Module | Memory | Steps (n=80) | ms / step |
|---|---|---|---|
| `loop-0` | none | 732 | 0.031 |
| `loop-1` | 1 page | 732 | 10.47 (n=20: 10.28) |
| `loop-4` | 4 pages | 732 | 44.5 |
| `loop-16` | 16 pages | 732 | 181 |
| `memloop-1` | 1 page, `i32.store` + `i32.load` per iteration | 892 | 11.4 |

(Steps per iteration: 9 for `loop`, 11 for `memloop`; results correct.)

`size-cost.lsp`: one `%SIZE` of the configuration, and one `STEP` of the
call configuration and of a configuration 12 steps into the loop:

| Module | `%SIZE` | `STEP` (call) | `STEP` (in loop) | ratio in-loop / `%SIZE` |
|---|---|---|---|---|
| `loop-0` | 1 µs | 1 µs | 46 µs | — |
| `loop-1` | 797 µs | 0 µs | 15,105 µs | 19.0 |
| `loop-4` | 3,392 µs | 1 µs | 62,818 µs | 18.5 |

- Reading: inside the loop the configuration is nested (frame, label, loop
  contexts), and `Step/ctxt-*` recurses through the `rec` group. Before
  every recursive premise call the generated code compares `%SIZE` of the
  callee inputs with `%SIZE` of its own inputs (wasm1 T8's termination
  scheme). Both include the store, so its byte lists are traversed about 19
  times per step. The constant ratio supports this. I did not count `%SIZE`
  calls directly.
- spec-test-1 (`make spec`, P5): 163 min CPU in total. 120 min of that are the
  two scripts that hit the 1 h limit (`call`, `call_indirect`, deep
  recursion at about 30 ms per step); the other 65 scripts took about 43 min
  for about 11,500 commands, **0.22 s CPU per command** on average. Session
  start-up (load the generated books) is 1.0 s.
- Slow script profile: `call_indirect` reached 76 of 78 commands in 1 h;
  `call` 31 of 32. Both are recursion-heavy (`fac`, `fib`, `even`/`odd`),
  and the driver gives each action 3,000 steps.

### Item 2: the 3.0 approach (recommendation)

Keep the byte-list encoding (spec-faithful, and the proofs stay simple), and
remove the measured cost at its source:

1. **Generated termination checks that ignore the store.** In the recursive
   `Step` premises (`Step/ctxt-label`, `ctxt-frame`, `ctxt-instrs`, and 3.0's
   `ctxt-handler`) the store is passed through and only the instruction part
   shrinks (to confirm rule by rule, see open questions). A measure over the
   non-store part of the configuration, or a
   config entry like `:decreasing` that names a sub-component, removes the
   19 traversals. Expected effect: steps cost about as much as `loop-0`
   (0.03-0.05 ms), a factor of about 300 at 1 page. Translator work for the
   wasm3 plan; 1.0 byte-identity no longer applies to `STEP` there.
2. If (1) cannot be justified for some rule: guard-verify `STEP` and wrap
   the checks in `mbe` with `:exec t`, with a proof that they hold. That is the
   T8 obligation already listed in wasm1 W13.
3. Not recommended: a different memory encoding (string or natural). It
   changes every load/store rule's meaning, which then needs an equivalence
   proof.

Independently, the driver needs limits for the cases in item 3: a declared
local count or a memory/table growth above a bound is reported as a
resource limit (like `assert_exhaustion`), not run.

### Item 3: where generated code can crash

- Observed (spec-test-1): 5 crashes, all resource limits of list-building
  code in **logic-mode** functions:

| Script, command | Crash | What builds the list |
|---|---|---|
| `binary` 48th, "too many locals" | control stack | `GRAM/BLOCALS` expands `n:u32 t` into `t^n` |
| `memory_grow`, `grow(800)` | control stack | growing a memory by 800 pages (52 MB of bytes) |
| `memory_trap`, `memory.grow(65537)` (must fail) | control stack | the new byte list is built before the limit check decides |
| `data`, "data segment does not fit" | heap | instantiation with an out-of-bounds data segment |
| `elem`, "elements segment does not fit" | heap | the same for an element segment |

- `:program` functions (35, from `gen/wasm-1.0/modes.lsp`): the
  instruction-typing clique (`INSTR_OK`, `INSTRS_OK` and their `/SPLIT`,
  `/SEARCHn`, `/%M` variants), `EXPR_OK`, `EXPR_OK_CONST`, `FUNC_OK`,
  `GLOBAL_OK`, `ELEM_OK`, `DATA_OK`, the `Module_ok` override functions
  (`MODULE_OK`, `MODULE_OK/%GLOBALS`, `%FUNCS-OK`, `%ELEMS-OK`,
  `%DATAS-OK`) and `$INSTANTIATE`. They run without guard checks, so an
  argument of the wrong shape can raise a raw Lisp error. Coverage: every
  input comes from `GRAM/BMODULE`, whose output has the shape of the
  syntax by construction, and from the driver's value conversion. No crash
  in spec-test-1 came from these functions. A well-formedness check in the
  driver (the generated `MODULE-P` recognizer on the parser output) would
  make this explicit; not done.
- For 3.0: same risks, plus GC heaps (struct and array allocation sized by
  operands) and 64-bit memories (`memory64`: sizes beyond any list).

### Exit: time estimate for spec-test-3

Measured inputs: 62,383 commands in the 228 convertible scripts (P5);
memories: 81% of the 5,365 modules declare no memory and 18% one page, versus
92% and 7% for spec-test-1's 2,381 modules (`memory-pages.mjs`).

- Base: 62,383 × 0.22 s ≈ 3.8 CPU hours. The larger share of modules with
  memory (2.4×: 19.0% vs 8.0%) raises this, by an unmeasured factor that is at most the
  memory-bound fraction of today's cost; take 4-9 CPU hours.
- Tail: in 1.0, 2 of 67 scripts reached the 1 h limit. At the same rate,
  about 7 of 228 scripts would, adding about 7 CPU hours.
- With 8 parallel sessions: about **1.5-2 h wall**, plus scripts beyond the
  limit. With recommendation (1), the per-step cost with memory drops to
  the no-memory level, so the tail and most of the memory share go away.
- This is an estimate from the measurements above, not a run; GC, SIMD and
  exception rules have no 1.0 counterpart to measure.

## Open questions

- Count the `%SIZE` calls per step directly (profile) to confirm the 19.
- Whether every recursive `Step` premise passes the store unchanged in 3.0
  (needed for recommendation 1).

## Data

`data/runtime-P6-2026-11-14/` (run from `translate/tests/spec/` after
`make spec`, which certifies `t7-lib`): `loop-{0,1,4,16}.wat`,
`memloop-1.wat` (and `.wasm`, built with `wat2wasm`), `bench.lsp` →
`bench.out`, `size-cost.lsp` → `size-cost.out`, `memory-pages.mjs` →
`memory-pages-{1.0,3.0}.out` (`node memory-pages.mjs DIR`, DIR the
converted spec data).
