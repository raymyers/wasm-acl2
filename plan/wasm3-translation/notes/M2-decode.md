# Binary decode of spec-test-3 in-tree

- Milestone: M2 (item 1)
- Date: 2026-11-14
- Repo commit: e9634fb plus this note's commit
- Status: final; two findings for the user (2.0 `Belem`, 1.0 import misses)
- Feeds wasm3 plan: §3, §5 M2 (done), §6, M4, M8

## Summary

`make decode SPEC=3.0` (new; 23 s with 8 sessions) runs every module of
the 259 converted spec-test-3 scripts through the generated parser
`GRAM/BMODULE` (`tests/spec/decode/`):

| Command kind | Modules | Decoded | As expected |
|---|---|---|---|
| `module` | 2,250 | 2,250 | **2,250** |
| `assert_invalid` (binary) | 2,728 | 2,724 | 2,724 |
| `assert_unlinkable` | 200 | 200 | **200** |
| `assert_uninstantiable` | 54 | 54 | **54** |
| `assert_malformed` (binary; must not decode) | 643 | 0 | **643** |

**Every well-formed module decodes, and every binary malformed one is
rejected.** The exception is 4 `assert_invalid` modules. As wabt wrote
them, they are binary-malformed: they use `memory.init` / `data.drop`
without a data count section. The reference interpreter's decoder
rejects them the same way ("data count section required"). The prep's
experiment had 4,562 of 4,639 well-formed (98.3%) and 604 of 643
malformed (93.9%). It had fewer modules, because 31 scripts were not
converted then.

## What was wrong, and the fixes

When first run in-tree, 113 modules were not as expected. Each miss was
given to the reference interpreter's decoder (`wasm -u -d`,
`misses-ref-interp.sh`; `MISSES-3.0-before-fixes-with-ref-interp.txt`):

1. **70 well-formed modules, a wabt artifact.** These are all of
   `table_copy` / `table_copy64` (36) and 34 in `linking`, `imports`,
   `data` and `multi-memory`. wast2json ran with `--enable-all`, which in
   wabt 1.0.41 includes the *compact import section* proposal (not in
   3.0). wabt then writes imports from one module in the compact form,
   which the 3.0 grammar does not have. The reference interpreter rejects
   them too ("malformed import kind"). The generated parser was right.
   **Fix (flake):** wast2json for 3.0 gets exactly the 3.0 proposals
   (annotations, exceptions, extended-const, function-references, gc,
   memory64, multi-memory, relaxed-simd, tail-call). That leaves out
   compact-imports, custom-page-sizes, threads, wide-arithmetic and
   code-metadata. Effect on the data: exactly these 70 `.wasm` files
   change. No command list changes, the same 31 scripts go through the
   reference interpreter, and none is skipped.
2. **39 malformed modules accepted: UTF-8 in names.** `Bname` decodes
   with `$inv_utf8` and checks `$utf8(name) = b*`. That re-encoding
   check rejects overlong forms and bad continuation bytes. But `rt/`'s
   `$utf8` (shared with 1.0) also encoded surrogates and values above
   U+10FFFF (e.g. from lead bytes `F5`-`FF`). Those inputs re-encoded to
   themselves and were accepted. **Fix (`rt/builtins.lisp`):** a value
   that is not a `char` encodes to `256`, which is not a byte, so the
   check fails. Valid characters encode as before. 1.0 gains from this
   too: `make decode SPEC=1.0` now rejects **638 of 638** malformed
   modules (599 before; `MISSES-1.0-before-utf8-fix.txt`). `make check`
   (1.0) stays green; generated code does not change.
3. **4 `assert_invalid` without a data count section**, as above: the
   binary is malformed as wabt wrote it. The test is a text module that
   is meant to fail validation. These are listed, not fixed.

## Found on the way: elem segments decode to the wrong shape

`Belem` flags 0-3 (`ELEM rt (REF.FUNC y)* ...`) decoded to one
expression holding all the `ref.func`s. Flags 4-7 give one expression
per element. The cause is the IL: SpecTec elaborates `(REF.FUNC y)*`
against the type `expr*` = `(instr*)*` by wrapping the whole `instr*`
in a one-element list, `[(REF.FUNC y)*]`, where the prose has one
expression per function index. Decoding does not notice. Validation
(`Elem_ok`: each element a constant expression of one reference) and
instantiation (M4) would. **Fix: new config entry `:il-patch "Belem"`**
(reason in the config). It rewrites the term to `[REF.FUNC y]*` in all
4 rules. Checked: `0x00 (i32.const 2) [3 1 4 1]` now decodes to four
expressions `((ref.func 3)) ((ref.func 1)) ...`.

**2.0's IL has the same shape** (`A-binary.spectec`, `Belem`), and
`gen/wasm-2.0` is not patched. 2.0 is a regression target and its gate
(numerics, SIMD) does not decode modules, so I left it. For the user to
decide.

## Open, outside M2: 54 well-formed 1.0 modules do not decode

`make decode SPEC=1.0` (the same driver on spec-test-1): 54 modules that
the reference interpreter decodes are rejected by the 1.0 parser (24
`module`, 28 `assert_unlinkable`, 2 `assert_invalid`; mostly `imports`
and `linking`, also `binary-leb128`, `start`, `names`, `func_ptrs`).
They are the same before and after the UTF-8 fix. On `imports.1.wasm`
the first failing section is the import section. The 3.0 parser decodes
the 3.0 versions of these scripts. This is 1.0 parser work (or the 1.0
data's wabt flags), not M2's.

## Data

`data/decode-M2-2026-11-14/`: `TOTALS-3.0.txt`, `MISSES-3.0.txt`,
`MISSES-3.0-with-ref-interp.txt` (the 4 left);
`MISSES-3.0-before-fixes-with-ref-interp.txt` (the 113 of the first
run, with the interpreter's verdict); `TOTALS-1.0.txt`,
`MISSES-1.0.txt`, `MISSES-1.0-with-ref-interp.txt`,
`MISSES-1.0-before-utf8-fix.txt`; `misses-ref-interp.sh`. The driver is
`translate/tests/spec/decode/` (`run-decode.sh`, `decode-one.lsp`, and
`sections.lsp`, which decodes growing prefixes of a module to find the
section that fails).

## Correction 2026-11-14 (M3)

The totals above miss the end of `binary`. Its session stopped at
`binary.43.wasm` ("too many locals": the parser builds the list of
declared locals and exhausts the Lisp stack). ACL2 still exited 0, so
the run did not report the script as unfinished. M3 decodes each module
as its own form and reports such a module as crashed
([M3-execution](M3-execution.md)). Corrected, spec-test-3:

| Command kind | Modules | Decoded | As expected | Crashed |
|---|---|---|---|---|
| `module` | 2,266 | 2,266 | **2,266** | 0 |
| `assert_invalid` (binary) | 2,729 | 2,725 | 2,725 | 0 |
| `assert_unlinkable` | 200 | 200 | 200 | 0 |
| `assert_uninstantiable` | 54 | 54 | 54 | 0 |
| `assert_malformed` (binary) | 712 | 0 | **710** | 2 |

So every well-formed module still decodes. Of the binary malformed ones,
710 are rejected and 2 crash ("too many locals"); the 4 `assert_invalid`
are as above.
