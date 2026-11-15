# Execution: all reduction rules, a store-free termination check, crash containment

- Milestone: M3 (items 1-3)
- Date: 2026-11-14
- Repo commit: 6972016 plus this note's commit
- Status: final; item 3 is done for the decode driver, and the execution
  limits move to the M4 driver (reason below)
- Feeds wasm3 plan: §2, §3, §5 M3 (done), §6, §7, M4

## Summary

- **218 of 218 reduction rules translated.** The last one,
  `Step_read/array.new_data-num`, compiles once the inverse rule solves for
  a middle argument.
- **A step no longer pays for the memory.** The size check before a
  recursive `Step` premise now compares the instruction part of the
  configuration, not the whole configuration with the store. Counting loop
  (`bench.lsp`, configuration built by hand and checked with the generated
  recognizers):

| Store | ms / step before | ms / step after |
|---|---|---|
| no memory | 0.014 | 0.012 |
| 1 page (64 KiB) | **5.39** | **0.011** |
| 4 pages | 22.2 | 0.011 |
| 1 page, `i32.store` + `i32.load` per iteration | — | 0.029 |
| 4 pages, the same | — | 0.059 |

  The exit asks for a 1-page step "within a small factor of the no-memory
  step (0.03 ms)". Measured: the same cost. A store still rebuilds the
  byte list (0.029 ms at 1 page, 0.059 at 4).
- **Crashes are contained in the decode driver.** Each module is decoded
  by its own top-level form. The two `binary.wast` "too many locals"
  modules exhaust the Lisp stack, and they are now reported as
  `CRASHED`. Before, they silently ended the session, which hid the rest
  of the script (see the correction in M2-decode).

Gates: 1.0 `make check` (`gen/wasm-1.0` byte-identical), `check-2.0`
(8,724/8,724, 528/528), `check-3.0` (all four counts as after M1). The
M5/M6 typing cases give the same 50 results.

## Item 1: `Step_read/array.new_data-num`

Premise: `$concatn_(byte, $zbytes_(zt, c)^n, $zsize(zt)/8) = bytes`, with
`c*` unknown. The inverse case of `cpat` assumed the unknown is the last
argument (`f(a.., x) = s`). Here it is the first of `$concatn_(xs, k)`.
The translator now takes the only argument with unbound variables
(`inverse-arg-index`), and the inverse gets the other arguments in order,
then `s`: `$inv_concatn_(k, s)`. The iterated pattern `$zbytes_(zt,
c)^n` is then matched element by element, through the inverse of
`$zbytes_`. The generated code takes the `n·zsize/8` bytes at `i`, splits
them, decodes each chunk with `$inv_zbytes_` and checks it re-encodes,
checks the count, and re-checks the whole equation. An out-of-range
slice fails the check, which leaves it to the `-oob` rule. Behaviour is
not tested yet: building a state with a `deftype` by hand is costly, so
the check is the GC script `array_new_data` in M4.

A consequence that had to be fixed. With all its rules compiling,
`Step_read` took the existing rule "a relation that calls a `:multi`
relation becomes `:multi`" (it calls `Ref_ok`). `Step` followed, and its
split variant read `z'; instr'*` as input `z'`, output `instr'*`. `Steps`
then called `STEP` with the wrong arity and certification failed. Now
the propagation skips the step relation of a closure (`Step` for
`Steps`). `Step` stays `:fun`. `Step_read` is `:multi`, and its output
variant `STEP_READ/SPLIT` drops no rule. 1.0 output is unchanged.

## Item 2: termination check without the store

`:decreasing` pairs can now name a path into an input: `("Step" 0 2)` is
element 2 of input 0, the instructions of `(:|%;%| state instrs)`
(`dec-size` / `nth-path` in `compile.lisp`, validated in `emit.lisp`). The
check before a recursive premise is lexicographic: first the instruction
part is smaller, or else it is equal and the whole input is smaller.
Every `Step` rule with a `Step` premise (`ctxt-instrs`, `ctxt-label`,
`ctxt-handler`, `ctxt-frame`) steps a proper part of the instruction
list. So the first comparison decides every real derivation, and the
store is never traversed. No derivation is cut: this order accepts every
call that the old one did. The entry is the 3.0 `:decreasing` entry, with
its reason updated. 1.0 keeps its own entry and output.

For M9 (logic mode), the same `dec-size` term is the measure's first
component, so the termination argument keeps its shape.

## Item 3: driver limits

The five spec-test-1 crashes of P6 are "too many locals" in the decoder,
two `memory.grow`, and two out-of-bounds segments at instantiation.
- **Decoder (done):** `tests/spec/decode/decode-one.lsp` runs each module
  as its own form under `ld ... :ld-error-action :continue`, after a line
  `D3-TRY`. A module whose form aborts is listed in `CRASHED`, and the
  scripts that never print `D3-DONE` in `NOT-FINISHED` (none now).
  spec-test-3: 2 crashed (`binary.43`, `binary.44`, both "too many
  locals"; the spec rejects them by the bound `< 2^32`, which the parser
  checks only after expanding the locals).
- **Execution (moved to M4):** `memory.grow` by 800 pages and segment
  bounds happen while stepping and instantiating, so the limits belong to
  the 3.0 execution driver's step loop and `$instantiate` path. That
  driver does not exist yet (M4 item 1). There is nothing to attach them
  to without writing that driver first, so they are listed in M4.

## Data

`data/runtime-M3-2026-11-14/`: `bench.lsp`, `bench-before.txt` (before
the `:decreasing` path; loop only), `bench-after.txt`;
`decode-TOTALS-3.0.txt`, `decode-MISSES-3.0.txt`,
`decode-CRASHED-3.0.txt` (the decode run with crash containment).
