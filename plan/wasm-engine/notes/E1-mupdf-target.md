# MuPDF as the engine's target module

- Milestone: E1 (items 1 to 4 and 6 to 9 done; item 5 below)
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

## Second session (2026-11-15, evening): items 4, 6, 7, 8, 9

### Item 8: the build as a script

`engine/mupdf/build.sh WORKDIR [COMMIT]` clones the fork, installs
Emscripten 4.0.8 with emsdk inside a `nix shell` (python 3.12, node, make,
sed, git; nixpkgs has Emscripten 6.0.9, not 4.0.8), runs MuPDF's
`platform/wasm/tools/build.sh` and writes `WORKDIR/out/BUILD-INFO`.

Two things the hand build did not record:

- The fork's `.gitmodules` uses relative URLs (`../thirdparty-curl.git`,
  `../mujs.git`), which from `raymyers/mupdf` point to repositories that do
  not exist. The script maps `https://github.com/raymyers/` to
  `https://github.com/ArtifexSoftware/` for the submodule update only.
- `nproc` is missing on darwin; a shim is put on `PATH`.

**The script reproduces the hand build bit for bit**: sha256
`e3c67c2e8529a89116ed643c05782cbe199ff91f4864a1a03a92e500efb3af14`, the
checksum recorded for `3eae43d` (`fork-3eae43d-BUILD-INFO.txt`; emsdk
`708dcbc`, darwin arm64).

### Item 4: census (fixes D5)

`fork-3eae43d-census.txt` (sections, memory, table, globals, tag, the 22
imports with signatures) and `d5-groups-fork-3eae43d.txt` (every opcode of
the census in its group, by `d5-groups.py`):

| | |
|---|---|
| Memory | 352 pages initial (23,068,672 bytes), max 32,768 |
| Table | funcref, 3,246 fixed (initial = max); one active segment at offset 1 with 3,245 functions |
| Global | one, `__stack_pointer`, i32 mutable, 6,261,248 |
| Tag | one, `(i32) -> ()` |
| Data | 3,140 segments, 6,057,960 bytes of section |

| Group | Instructions | Occurrences |
|---|---|---|
| S0 integer core | 97 | 1,848,200 |
| S1 floats, `call_indirect` | 59 | 37,628 |
| S2 `memory.copy`, `memory.fill`, sign extension | 6 | 1,861 |
| S3 `try_table`, `throw`, `throw_ref` | 3 | 3,694 |
| outside D5 | 0 | 0 |

So D5 is exactly S0 to S3 and H: 165 instructions. Two instructions of D5
as first written do not occur: **`memory.grow` and `nop`**. The memory
grows only through the import `emscripten_resize_heap` (the glue calls
`wasmMemory.grow`), so in the engine growing memory is a host function
that changes the store (E9).

### Items 6 and 7: reference renders and what the imports must do

Two PDFs were added, written byte for byte by `gen-pdfs.py` (stdlib
Python, deterministic): `slide.pdf` (960 x 540, a title, bullets, an
axial shading, a Flate RGB image, filled and stroked paths: the slide) and
`text.pdf` (612 x 792, four base-14 fonts, rotated and scaled text, dashed
and clipped paths, a CMYK and a gray fill). `ref-render.mjs` renders page
1 of each at 72 dpi (identity matrix, DeviceRGB, no alpha) in node 24.18.1
and prints the sha256 of the samples (`ref-render.out`):

| PDF | Size | sha256 of the RGB samples (fork `3eae43d`) |
|---|---|---|
| `test1.pdf` | 612 x 792 | `e1e83ad30c2bfc21f25c734954a4431c937940d4d3c63460a7fc04b2ed54dae8` (as in the first session) |
| `slide.pdf` | 960 x 540 | `86375811de1a8e1f218d82b80b12d533eda035652ff778ed953caf1f3c5cac5a` |
| `text.pdf` | 612 x 792 | `77dcea3e9642fdc24e13d16864667d10d94ad958ca8f583b2fec39dc65428b42` |

The pixel files are not checked in. `ref-render.mjs` regenerates them
from the module, and E9 compares checksums.

The same script wraps every import and export and counts calls per phase
(load, open, render). For these three PDFs only six imports are called:

| Phase | Imports called |
|---|---|
| load (instantiate, `__wasm_call_ctors`, `wasm_init_context`) | `__wasi_environ_sizes_get` 1, `__wasi_environ_get` 1, `_tzset_js` 1, `emscripten_date_now` 9, `_gmtime_js` 9 |
| open (`openDocument`, `loadPage`) | none |
| render | `emscripten_asm_const_ptr` 2 to 4 (always the snippet at 6164637, `$libmupdf_load_font_file`), and for the slide and text 3 or 4 each of `emscripten_date_now` and `_gmtime_js` |

`$libmupdf_load_font_file` (`mupdf.js` line 3156) returns 0 when no
JavaScript font loader is set, which is the case here. MuPDF then uses its
built-in base-14 fonts. So for "open a PDF from memory, render page n",
the host must give: an environment (0 variables), a time zone, the time
(`date_now`, `gmtime`), and 0 for the font loader. The other 16 imports
(files, `exit`, `abort`, `resize_heap`) were not called by these PDFs. A
PDF that needs more memory calls `emscripten_resize_heap`.

The exports the JavaScript API calls, in order (`exports-called.txt`, names
from the name section): `__wasm_call_ctors`, `wasm_init_context`,
`wasm_device_gray`/`rgb`/`bgr`/`cmyk`/`lab`, `wasm_pdf_keep_obj`; then per
document `wasm_malloc`, `wasm_new_buffer_from_data`,
`wasm_open_document_with_buffer`, `wasm_drop_buffer`, `wasm_load_page`,
`wasm_pdf_document_from_fz_document`, `wasm_pdf_page_from_fz_page`; per
render `wasm_pdf_new_pixmap_from_page_with_usage`, `wasm_pixmap_get_w`,
`wasm_colorspace_get_n`, `wasm_pixmap_get_stride`,
`wasm_pixmap_get_samples`, `wasm_free`. This is the call sequence E9's
driver makes.

### Item 9: a smaller build (second target)

`engine/mupdf/build-small.sh` turns off everything a PDF of the talk does
not need: every document type but PDF, the HTML engine, JavaScript, ICC,
JPEG 2000, barcodes, OCR and office output, and every font but the
base-14 set. Built from the same commit (`small-BUILD-INFO.txt`):

| | Full (`3eae43d`) | Small |
|---|---|---|
| sha256 | `e3c67c2e...af14` | `97239ccb67f175a8caab6c38d52fc9576297f20af72a43c0879a6dcaf21d1f97` |
| Size | 10,429,496 | 4,537,938 |
| Functions | 7,035 | 4,470 |
| Imports | 22 | 21 (no `_abort_js`) |
| Instructions | 1,899,382 | 1,174,580 |
| Memory | 352 pages | 288 pages |
| Table | 3,246 | 2,035 |
| Data segments / bytes | 3,140 / 6,057,960 | 1,456 / 1,897,295 |
| D5 groups | S0 to S3 | S0 to S3 (S0 96, S1 56, S2 6, S3 3 instructions) |

`test1.pdf` and `slide.pdf` render to the same samples as with the full
build. **`text.pdf` differs in exactly the 200 x 120 CMYK rectangle**
(24,000 pixels): cyan is `00adef` with ICC and `00ffff` without
(`FZ_ENABLE_ICC=0`). sha256 with the small build:
`6f4be006e6f5bd44174dec4c7ea01f9b2060949198a45bb00b1d90d2944400a3`. The
comparison of E9 is always the engine against V8 on the same module, so
each target has its own reference checksums.

### Item 5: the module through the generated decoder and `Module_ok`

`engine/mupdf/decode.lsp` reads the module as a byte list, runs
`GRAM/BMODULE` (the generated binary parser) and `MODULE_OK` (the
generated validator), and prints the time of each (`read-run-time`, CPU
seconds). Run with `SBCL_USER_ARGS='--control-stack-size 4000'`.

**The small target passes** (`decode-small-97239cc.out`): the parse is
complete (no bytes left), and `Module_ok` returns `T`.

| | Small (`97239cc`, 4.5 MB) |
|---|---|
| Read 4,537,938 bytes | 83 ms |
| `GRAM/BMODULE` | complete, 4,378,762 ms (73 min) |
| Module fields | 158 types, 21 imports, 1 tag, 1 global, 1 memory, 1 table, 4,470 functions, 1,456 data, 1 element segment, no start, 556 exports |
| `Module_ok` | `T`, 85,040 ms |
| Peak memory | 10.8 GB |
| Wall time | 4,701 s |

The machine was loaded while this ran (up to 8 other ACL2 processes,
load average up to 128 for a few minutes, swap in use), so the times are
CPU time under contention, not clean rates. **The full module**
(`3eae43d`, 10.4 MB) was started at the same time. Its parse was stopped unfinished after 434
CPU minutes (2026-11-16, at the user's request, when L0 replaced MuPDF as
the next demo). The small target's result stands for item 5.

So the generated validator accepts MuPDF (at least the small build): the
risk "the rebuilt MuPDF does not validate under `Module_ok`" did not
happen for it. The decoder is the slow part. Its time grows faster than
the module (`decode-scale.out`, synthetic modules of N functions of 64
instructions, `engine/mupdf/scale/`):

| Module | Bytes | Parse | `Module_ok` |
|---|---|---|---|
| m-100 | 9,733 | 14 ms | 24 ms |
| m-400 | 40,637 | 120 ms | 114 ms |
| m-1600 | 164,237 | 1,391 ms | 645 ms |
| m-6400 | 658,637 | 21,199 ms | 7,123 ms |

Each step is 4 times the size; the parse time grows 8.6, 11.6 and 15.2
times, approaching the square of the size. A profile of the parse of
m-1600 (`profile-decode.lsp`, `profile-decode.out`) has 57% of the
samples in `__bzero` (zeroing fresh allocation, as in E0) and most of the
rest in an unnamed clique around `GRAM/BINSTR`, the instruction grammar.
The quadratic part was not pinned down further.

For the engine this means: E9 loads MuPDF through its own loader (the plan
already allows it, §5), and the generated decoder and validator are run
once, offline, as a check of the module (the litmus test prints the
module checksum, and a check that took an hour once is recorded, not
repeated).

## Open questions

- Why do the two builds differ by 375 functions?
- Does the generated decoder finish on a 10 MB module, and does
  `Module_ok` accept it? (E1 item 5)
- Can the build drop features to shrink the module and its initial
  memory? Answered (item 9): to 4.5 MB and 288 pages.

## Data

Second session: `engine/mupdf/build.sh`, `build-small.sh`, `decode.lsp`,
`scale/`; `data/e1-mupdf/fork-3eae43d-census.txt`,
`fork-3eae43d-BUILD-INFO.txt`, `small-BUILD-INFO.txt`,
`small-97239cc-opcodes.txt`, `d5-groups.py`, `d5-groups-*.txt`,
`gen-pdfs.py`, `slide.pdf`, `text.pdf`, `ref-render.mjs`,
`ref-render.out`, `exports-called.txt`, `decode-scale.out`.

First session, `data/e1-mupdf/`: `census.sh` (the opcode count); census and checksum of
both binaries; `build-by-hand.sh`; `test1.pdf`, `render.mjs`,
`errpath.mjs` and `results.txt`. The binary itself is not stored:
`npm pack mupdf@1.28.6`.
