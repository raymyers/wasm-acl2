# LaTeX on the engine

`tex.wasm` (web2js TeX, the TikZJax build: e-TeX with LaTeX preloaded) runs
on the engine's fast machine and writes a DVI file. `deck/` is the workshop
talk, typeset this way. Started as a spike on 2026-11-16; not part of
`make -C engine check`.

## Run

Inside `nix develop`, with the engine books certified:

```sh
sh engine/tex/fetch.sh                  # third-party files -> build/dl, build/fs
TEXMODE=build sh engine/tex/run.sh      # build/acl2-wasm-tex: an image that starts at TeX's main
engine/tex/build/acl2-wasm-tex FILE.tex # -> FILE.dvi, FILE.log in the current directory
sh engine/tex/tex.sh engine/tex/input.tex engine/tex/build/out   # the same with the driver's detail -> out.dvi, out.log
python3 -I engine/tex/dvitype.py engine/tex/build/out.dvi        # what the DVI sets (any python3; the dev shell has none)
```

`build/acl2-wasm-tex` is an executable: SBCL's runtime and the ACL2 image
with the engine books loaded and `tex.wasm` instantiated, about to call
`main`. Files that FILE.tex inputs are looked for next to it, then in
`build/fs`. `sh engine/tex/run.sh` without `TEXMODE` runs `input.tex` in one
process, without saving an image. To view a DVI: `dvipdfmx` from TeX Live
(`nix shell nixpkgs#texliveSmall`).

## Measured (2026-11-16, `input.tex`)

| | |
|---|---|
| Decoding `tex.wasm` (518 KB) with the generated decoder | 15.7 s, then cached (`build/tex.decoded`) |
| Building the image | 23 s, 2 GB |
| `main` on the engine | 55,065,266 steps, 17.4 s (3.17 M steps/s), 3,717 host calls |
| A one-character document | 28,265,778 steps, 8.9 s |
| One run from the image, wall clock | 19.5 s |
| Output | 860 bytes of DVI, 2 pages; the same bytes with and without the image |

## What runs where, and what is trusted

- Every WebAssembly instruction of `tex.wasm`: the engine (`WE::FAST-STEP`).
- Decoding and the instantiation configuration: the generated 3.0 spec.
  `helper.wat` declares the types of the 18 imports, so `$instantiate` links
  them; the driver then makes those functions host functions in the store.
- The 18 imported functions (files, printing, date): `texrun.lisp`, raw
  Lisp, a port of TikZJax's `library.js`. Trusted, not proved. It reads and
  writes the engine's memory array and does not go through the spec's
  `$hostcall` hook.
- `data.drop`: the engine sends it to its fallback, which copies the whole
  memory (72 MB) out and back: 102 s for the 40 of them at instantiation.
  The driver applies the spec's rule function to the state without the
  bytes instead. That the rule does not touch the bytes is assumed here,
  not proved (the engine has no frame lemma for it yet).
- The module uses `f32` instructions and host calls, so it is outside the
  integer core (S0) of the engine's proof plan.

## Not done

- No comparison with another TeX: the DVI was read with `dvitype.py` and
  viewed through `dvipdfmx`, not checked byte for byte against a reference.
- No other format: the preloaded one is LaTeX with the `standalone` class
  and TikZ. `deck/slides.tex` works inside it (its own fixed-size pages).
- No beamer and no newer `tex.wasm`: see the end of the next section.

## The talk deck (`deck/`)

`deck/deck.tex` is `latex-slides/main.tex` rewritten for this TeX: no beamer,
no TikZ. `deck/slides.tex` is the macro layer (fixed 160 x 90 mm pages, a
`slide` environment, images, code blocks, and a few shapes drawn as dvipdfmx
specials).

```sh
sh engine/tex/deck/build.sh                # all slides -> build/deck/deck.pdf (from a snapshot)
sh engine/tex/deck/native.sh               # ordinary latex, for quick iteration -> build/deck/native.pdf
SLIDES=13,14 sh engine/tex/deck/build.sh   # only those
```

### The demo: commands that show it

In a shell with a TeX Live for `dvipdfmx`
(`nix shell --inputs-from . nixpkgs#texliveSmall nixpkgs#poppler-utils`),
from `engine/tex/deck`:

```sh
file ../build/dl/tex.wasm              # TeX, as a WebAssembly module
time ../build/acl2-wasm-tex deck.tex   # the ACL2 engine runs it on the deck -> deck.dvi
dvipdfmx deck.dvi                      # native: DVI -> deck.pdf, embeds fonts and images
pdfinfo deck.pdf | grep Pages
```

`acl2-wasm-tex` starts at the call of `main`, not from a snapshot. It prints
the ACL2 version, TeX's own terminal output (`[1] ... [33]` as pages are
shipped), a line every 100 M instructions, and the total. On 2026-11-16:
606,084,354 WebAssembly instructions in 195.4 s, 63,744 host calls, 33
pages; `dvipdfmx` then takes 2.4 s. Slide 32 of the deck shows that
transcript, with some of TeX's chatter left out.

The engine typesets and writes `deck.dvi`. `dvipdfmx` (native) turns it into
a PDF and embeds the fonts and the PNGs of `latex-slides/figs`; TeX never
opens an image, it gets the pixel sizes from `figdims.tex` (written by
`figdims.mjs`; the build scripts refresh it). `deck/figs` is a link to
`latex-slides/figs`.

Measured 2026-11-16:

| | |
|---|---|
| Whole deck (33 slides), from the call of `main` | 606 M steps, 3 min 16 s |
| Whole deck (29 slides then), from the snapshot | 508 M steps, 2 min 46 s |
| One slide, from the snapshot | 67 to 82 M steps, 21 to 26 s |
| Preamble and `\begin{document}` (in the snapshot) | 62 M steps |
| One TikZ picture (why the deck has none) | 66 M steps for a line, 500 M for a rotated rounded node |

The snapshot is an image of the engine saved when TeX is about to read the
line `%%% snapshot` of `deck.tex` (`TEXSNAP`, `TEXCORE` in `tex.sh`);
`build.sh` saves it again when anything before that line changes.

Why not beamer: this `tex.wasm` is revision `d78ef1f` of `drgrice1/web2js`
(its string pool checksum, 268807875, is in the binary). It is compiled for
75 fonts and 20,000 words of font metrics and has no `\strcmp` or
`\expanded`; `main.tex` under pdfTeX used 124 fonts and 748,218 words. The
current upstream source has larger limits and those primitives; building it
was not tried here.
