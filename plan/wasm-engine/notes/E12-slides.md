# L0: the talk's slides, rendered by the engine, identical to V8

- Milestone: E12 (all five items), litmus milestone L0 (D10, decided by the user 2026-11-16)
- Date: 2026-11-16
- Repo commit: f6eb12b plus this note's commit
- Status: final
- Feeds engine plan: E12, L0, D10, E11 (a first module for the proved subset)
- Incorporated in engine plan: yes (E12, "Litmus milestones", "Current state")

## Summary

- **Every slide of the deck is rendered by the engine with pixels
  identical to V8's: 7 of 7** (`make -C engine slides`, 35 s in all,
  3.3 to 4.3 s per slide).
- The renderer is our own C program for decks in the plain-text format of
  suckless `sent` (one slide per paragraph, scaled to fit, black on white),
  compiled freestanding to wasm32: no imports, one page of memory, and
  only S0 instructions (census below).
- The engine is the list machine of E6. It runs the instantiation (which
  copies the deck and the font into memory) and every call of `render(n)`.
  The spec contributes the decoder and `$instantiate`'s configuration.
- **Proof status (D8): the module is not yet inside the proved subset.**
  The simulation proof for S0 (E11) is not finished: C1 and C3 hold for the
  machine, and C2 for its clock-0 steps. The viewer's caption says so.

## Findings

### The renderer (`engine/slides/`)

| File | What |
|---|---|
| `sent.c` | the renderer: `slide_count()`, `render(n)`, `framebuffer()`, `width()`, `height()` |
| `font.h` | Spleen 6x12 (BSD-2-Clause, copyright notice kept), printable ASCII, made by `gen-font.py` from nixpkgs' `spleen-6x12.bdf` |
| `deck.txt` | the deck (7 slides) |
| `gen-deck.mjs` | the deck as a data segment (`deck.h`) |
| `build.sh` | builds `sent.wasm` with clang 21.1.8 and lld from the repository's pinned nixpkgs (`nix shell --inputs-from .`); flags `--target=wasm32 -O2 -nostdlib -mcpu=mvp -fno-builtin`, 4 KiB stack, memory 1 page (initial = max) |
| `render.lsp` | the engine driver (ACL2): decode, instantiate, render every slide on the machine, write `slide-N.pbm` |
| `ref.mjs` | V8 renders every slide and writes PNGs |
| `check.mjs` | compares each engine PBM with V8's framebuffer, writes PNGs from the engine's pixels and the viewer |
| `run.sh` | all of it; `make -C engine slides` calls it |

The format follows sent: paragraphs separated by an empty line are
slides; a line starting with `#` is a comment (it does not end a
paragraph); a `\` at the start of a line is dropped, so `\#` and `\@` are
literal. sent's `@FILE` image slides need farbfeld images; this renderer
has no image decoder and draws such a line as text. Lines are centred as a
block and left-aligned within it, as sent does, and scaled by the largest
integer factor at which the block fits inside margins of 16 x 9 pixels.
The framebuffer is 320 x 180 pixels, 1 bit per pixel (7,200 bytes), shown
4 times larger.

The renderer is written for the list machine, whose memory accesses are
slow (E0, E6): `render` writes every framebuffer byte exactly once, and
loads a character and its glyph row only when the character changes.

### The module

`data/e12-slides/BUILD-INFO.txt`: deck sha256 `b03cf3be...f87a`, module
sha256 `33eb3567b3df61c5fcf8beaaf83f2d4e0ea947cfbac3c489a7a27812642e775b`
(the same in two builds). Memory 1 page (initial = max), no imports, six
exports (memory and the five functions).

Census (`data/e12-slides/census.txt`): `local.get/set/tee`, `i32.const`,
`i32.add/sub/mul/div_u/and/or/xor/shl/shr_u`, the `i32` comparisons and
`eqz`, `i32.load`, `i32.load8_u`, `i32.store`, `i32.store8`, `select`,
`block`, `loop`, `br`, `br_if`, `br_table`, `call`. **All S0.** No float,
no `call_indirect`, no bulk memory, no exceptions.

### The engine run

`data/e12-slides/engine-render.txt`, `check.out`:

| Slide | Scale | Engine time | Same as V8 |
|---|---|---|---|
| 0 | 2 | 3,512 ms | yes |
| 1 | 1 | 3,256 ms | yes |
| 2 | 2 | 4,241 ms | yes |
| 3 | 1 | 3,256 ms | yes |
| 4 | 2 | 4,282 ms | yes |
| 5 | 3 | 4,137 ms | yes |
| 6 | 5 | 3,725 ms | yes |

(The run of `make -C engine slides`; the first run, by hand, gave the same
pixels and times within 1.5%.) The checksums of the framebuffers are equal to V8's for
every slide (`check.out` lists both). `slide-0.png` and `slide-4.png` in
`data/e12-slides/` are made from the engine's pixels.

One change to the machine was needed: `data.drop` and `elem.drop` (arity
0), which instantiation runs after copying a data segment, were missing
from the arity table. All engine books certify again with it.

### The viewer

`engine/slides/build/view/index.html`: the slides from the engine's
pixels, full window, arrow keys or space to move, `f` for full screen, and
a caption naming the engine, the number of slides identical to V8 and the
proof status. The rendering is done in ACL2; the browser only shows the
images.

## What is trusted for L0

The translator and SpecTec (the spec), the generated decoder and
`$instantiate` (spec code, run once per deck), clang and lld (the module is
compared with V8 on the same bytes, so a compiler bug would show in both,
not as a difference), the PBM-to-PNG conversion and the viewer (display
only). No host functions.

## Open questions

- A larger deck, or a higher resolution: the time per slide grows with the
  framebuffer and the memory size (list memory, E0), until E7.
- Image slides (`@FILE`): a farbfeld decoder in the module would work, but
  images need memory, which is slow until E7.

## Data

`engine/slides/`; `data/e12-slides/`: `BUILD-INFO.txt`, `census.txt`,
`engine-render.txt`, `check.out`, `slide-0.png`, `slide-4.png`.
