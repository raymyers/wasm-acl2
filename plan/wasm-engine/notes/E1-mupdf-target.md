# MuPDF as the engine's target module

- Milestone: E1 (items 1 to 3 done; item 4 partly; the others are open)
- Date: 2026-11-15
- Repo commit: d845f70 plus this note's commit
- Status: draft
- Feeds engine plan: §2 (starting point), D5 (subset), E1, E9 (host layer)
- Incorporated in engine plan: yes (§2 table, D5)

## Summary

- The published `mupdf` 1.28.6 module cannot be decoded by the 3.0
  semantics: it uses the legacy exception encoding (`try`, `catch`,
  `delegate`), which is not in WebAssembly 3.0.
- The encoding is chosen by two Emscripten flags in MuPDF's own build.
  A branch of the fork `raymyers/mupdf` adds
  `-sWASM_LEGACY_EXCEPTIONS=0` to compile and link.
- Apart from exceptions the module needs floats, one table with
  `call_indirect`, `memory.copy`, `memory.fill` and sign extension. No
  SIMD, no GC. It starts with 352 pages of memory and imports 22 host
  functions.

## Findings

### The published binary (npm `mupdf` 1.28.6, `dist/mupdf-wasm.wasm`)

sha256 in `data/e1-mupdf/npm-1.28.6-sha256.txt`. From `wasm-objdump -h`
and `-x` (wabt 1.0.41):

| | |
|---|---|
| Size | 10,416,688 bytes |
| Functions | 7,410 defined, 22 imported |
| Types | 196 |
| Memory | 1, initial 352 pages, max 32,768 |
| Table | 1, funcref, 3,246 entries, 1 element segment |
| Tags | 1 |
| Globals | 1 |
| Exports | 556 (555 functions and the memory) |
| Data segments | 3,140 (with a DataCount section) |
| Instructions | 1,891,411 |

Post-1.0 instructions, from the census
(`data/e1-mupdf/npm-1.28.6-opcodes.txt`):

| Group | Instructions |
|---|---|
| Legacy exceptions | `try` 2,492; `delegate` 1,290; `catch` 1,202; `throw` 1 |
| Bulk memory | `memory.copy` 710; `memory.fill` 662 |
| Sign extension | `i32.extend8_s` 150; `i32.extend16_s` 264; `i64.extend16_s` 58; `i64.extend32_s` 17 |
| Not present | saturating truncation, SIMD, reference types beyond funcref, GC, tail calls |

Also relevant to the engine's subset: `call_indirect` 3,267; `select`
7,418; `f32.*` and `f64.*` throughout.

The 22 imports (names from the name section): `emscripten_asm_const_int`,
`emscripten_asm_const_ptr`, `exit`, `emscripten_date_now`,
`__wasi_fd_write`, `__wasi_fd_close`, `__wasi_fd_seek`, `__wasi_fd_read`,
`__wasi_environ_sizes_get`, `__wasi_environ_get`,
`__wasi_clock_time_get`, `__syscall_unlinkat`, `__syscall_openat`,
`__syscall_fcntl64`, `__syscall_ioctl`, `__syscall_ftruncate64`,
`__syscall_rmdir`, `emscripten_resize_heap`, `_tzset_js`, `_timegm_js`,
`_gmtime_js`, `_abort_js`. What the two `asm_const` imports run has not
been read yet (E1 item 7).

### Why the 3.0 semantics rejects it

`translate/gen/wasm-3.0/5_3-binary_instructions.lisp` has `:TRY_TABLE`,
`:THROW` and `:THROW_REF`, and has no `:DELEGATE` or `:RETHROW`. This was
read from the generated parser. The module was not run through the
decoder (E1 item 5 does that for the rebuilt module).

### Where MuPDF chooses the encoding

MuPDF 1.28.6, Emscripten 4.0.8 (the version its `BUILDING.md` names):

- `Makerules`, for `OS=wasm` and `OS=wasm-mt`:
  `CFLAGS += -fwasm-exceptions` and `CFLAGS += -sSUPPORT_LONGJMP=wasm`
- `platform/wasm/tools/build.sh`, the `emcc` link line: the same two

MuPDF's error handling (`fz_try` / `fz_catch`) is `setjmp`/`longjmp`,
which these flags compile to wasm exceptions. That is why the module
cannot be built for 1.0 without a JavaScript trampoline for `longjmp`.

### The change

Fork: `https://github.com/raymyers/mupdf` (fork of
`ArtifexSoftware/mupdf`, created 2026-11-15). Branch `wasm3-exceptions`,
from tag `1.28.6`:

- `Makerules`: `CFLAGS += -sWASM_LEGACY_EXCEPTIONS=0` after each of the
  two `-sSUPPORT_LONGJMP=wasm` lines
- `platform/wasm/tools/build.sh`: `-sWASM_LEGACY_EXCEPTIONS=0` on the
  link line

### The rebuilt module (fork commit `3eae43d`, 2026-11-15)

Built by hand on darwin arm64 with Emscripten 4.0.8
(`data/e1-mupdf/build-by-hand.sh`). sha256 in
`data/e1-mupdf/fork-3eae43d-sha256.txt`; census in
`data/e1-mupdf/fork-3eae43d-opcodes.txt`.

| | Published 1.28.6 | Fork `3eae43d` |
|---|---|---|
| Size | 10,416,688 | 10,429,496 |
| Defined functions | 7,410 | 7,035 |
| Imports | 22 | 22 |
| Instructions | 1,891,411 | 1,899,382 |
| `try` / `catch` / `delegate` | 2,492 / 1,202 / 1,290 | 0 / 0 / 0 |
| `try_table` / `throw_ref` / `throw` | 0 / 0 / 1 | 2,492 / 1,201 / 1 |
| `memory.copy` / `memory.fill` | 710 / 662 | 710 / 662 |

The function count differs (7,410 against 7,035). The cause was not
looked for: the published binary was built by Artifex on Linux, this one
on darwin, and the two builds were not otherwise compared.

**It behaves the same in V8** (`data/e1-mupdf/results.txt`, node 24.18.1,
no flags):

- `render.mjs` on `test1.pdf` (two base-14 fonts, a filled rectangle, a
  stroked curve): 612 x 792, and the sha256 of the 1,454,112 RGB samples
  is the same for both modules.
- `errpath.mjs` raises two errors inside MuPDF (not a PDF; a page number
  out of range). Both modules report the same two messages, so the
  `try_table` path is exercised and works.

One PDF is not a test suite. E1 item 6 asks for three, one of them a
slide.

## Open questions

- Why do the two builds differ by 375 functions?
- Does the generated decoder finish on a 10 MB module, and does
  `Module_ok` accept it? (E1 item 5)
- Can the build drop features to shrink the module and its initial
  memory? (E1 item 9)

## Data

`data/e1-mupdf/`: `census.sh` (the opcode count); census and checksum of
both binaries; `build-by-hand.sh`; `test1.pdf`, `render.mjs`,
`errpath.mjs` and `results.txt`. The binary itself is not stored:
`npm pack mupdf@1.28.6`.
