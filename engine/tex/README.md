# LaTeX on the engine

`tex.wasm` (web2js TeX, the TikZJax build: e-TeX with LaTeX preloaded) runs
on the engine's fast machine and writes a DVI file. `deck/` is the workshop
talk, typeset this way. Started as a spike on 2026-11-16; not part of
`make -C engine check`. The run is outside the engine's proved subset
(host calls); "What runs where" below says what is proved, checked and
trusted.

## Run

Inside `nix develop`, with the engine books certified
(`make -C engine check`):

```sh
sh engine/tex/fetch.sh                  # third-party files -> build/dl, build/fs (inside nix develop: it needs node)
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

`TEXCENSUS=plan/wasm-engine/notes/data/v0-ground/census.lisp` (an absolute
path) with `run.sh` counts the rule functions the run applies; results of
2026-11-17 are in `plan/wasm-engine/notes/V0-ground.md`.

## Measured (2026-11-16, `input.tex`)

| | |
|---|---|
| Decoding `tex.wasm` (518 KB) with the generated decoder | 15.7 s, then cached (`build/tex.decoded`) |
| Building the image | 23 s, 2 GB |
| `main` on the engine | 55,065,266 steps, 17.4 s (3.17 M steps/s), 3,717 host calls |
| A one-character document | 28,265,778 steps, 8.9 s |
| One run from the image, wall clock | 19.5 s |
| Output | 860 bytes of DVI, 2 pages; the same bytes with and without the image |

Since 2026-11-18 the driver calls the engine's `FAST-RUN` once per stretch
between host calls, where it called `FAST-STEP` in a Lisp loop. Measured
that day: `main` on `input.tex`, the same 55,065,266 steps and the same
DVI, 17.6 s (3.12 M steps/s), 3,720 stretches.

## What runs where, and what is trusted

`tex.wasm` calls host functions, so a TeX run is **outside the proved
subset** of the engine (plan/wasm-engine/plan2.md, P1): the theorem of
the engine as it is called (T3, `engine/run.lisp`) is about a run that
ends with a result, and the fast machine stops at a host call. What
follows is what does hold for a TeX run, part by part.

**A run is a sequence of stretches.** A stretch is one call of
`WE::FAST-RUN` (through `FAST-RUN-FUEL`, proved to return the same stobj
and the unused fuel). It ends when the fast machine stops: `:unsupported`
at a `call_ref` of a host function, or `:done`. The driver then sets the
status back to `:run`, makes the host step in Lisp and starts the next
stretch. There is no Lisp loop over instructions any more.

| Part | What is known about it |
|---|---|
| Every stretch of WebAssembly instructions | **Proved**, for a stretch that starts with the invariant `FM-INV`: the configuration the stobj stands for when the stretch stops is the one the generated semantics (`W3T::STEP`) reaches from the stretch's first configuration in a stated number of steps, and the stobj has the invariant again (`FAST-STRETCH-IS-SPEC-STEPS`, `FAST-RUN-IS-SPEC-STEPS`, `engine/fast/stretch.lisp`). A step that is refused changes the status and nothing else (`FAST-STEP-WHEN-REFUSED`) |
| The invariant at the start of a stretch | **Checked at run time**, at every stretch (`FM-INV-CHECK`, proved equal to `FM-INV`; `TEXNOCHECK=1` turns the check off). Proved to hold at the end of a stretch; not proved after a host step |
| The 18 host functions (files, printing, date) | **Trusted.** `texrun.lisp`, raw Lisp, a port of TikZJax's `library.js`. They read and write the engine's memory array and the operand stack and do not go through the spec's `$hostcall` hook. Evidence: the DVI comparison below |
| The loader | **Trusted.** `helper.wat` declares the types of the 18 imports, so the spec's `$instantiate` links them; the driver then makes those functions host functions in the store, sets memory 0 to 1,100 pages, and fills the array from `core.dump` (LaTeX preloaded). This is not `ENGINE-RUN`'s loader, which is proved |
| `data.drop` | **Assumed, and tested on this module.** The engine sends it to its fallback, which copies the whole memory (72 MB) out and back: 106 s for the 40 of them, and only with a larger Lisp stack (`SBCL_USER_ARGS='--control-stack-size 8000'`; with the default 64 MB the fallback exhausts the stack, most likely where it takes the length of the byte list by plain recursion, `len-t`; read from the code, no backtrace). `TEXNOSHORTCUT=1 sh run.sh` runs that way: the state after instantiation (`STATE-DIGEST`: memory, store, frame), the step counts and the DVI are the same as with the shortcut (2026-11-18). The driver applies the spec's rule function to the state without the bytes instead (an `sb-int:encapsulate` in `texrun.lisp`); that the rule does not touch the bytes is not proved (plan2.md V7b). A stretch that takes the shortcut is not a run of the function in the theorems. `tex.wasm` executes `data.drop` in the instantiation stretch only; the driver counts the shortcuts per stretch and prints the count |
| Decoding and instantiation | The generated 3.0 spec, run as it is (`GRAM/BMODULE`, `$instantiate`, `$invoke`). `$instantiate` and the decoder are in program mode, so no theorem starts from the module's bytes |

Without `TEXQUIET`, the driver prints for each run of stretches
`main: N stretches of FAST-RUN, M started with FM-INV; data.drop shortcut
taken K times`. A run in which `M = N` and `K = 0` is, between its host
steps, covered by the stretch theorems.

## The DVI comparison

```sh
sh engine/tex/ref.sh engine/tex/input.tex engine/tex/build/out.dvi   # inside nix develop
```

`ref.sh` typesets the same file with the same `tex.wasm` and `core.dump`
on V8 (node) and TikZJax's own host functions (`library.js` of npm
`node-tikzjax` 1.0.5, unmodified, fetched and checked by `fetch.sh`), and
compares the two DVI files byte for byte. `v8ref.cjs` sets the date the
driver's host functions return (2026-01-01) and gives the library the
font metrics as files.

| Input | Engine | V8 with `library.js` | |
|---|---|---|---|
| `input.tex` | 860 bytes, sha256 `91c83590...` | 860 bytes, `91c83590...` | identical |
| `deck/deck.tex` (33 pages) | 20,992 bytes, `b95d451f...` | 20,992 bytes, `b95d451f...` | identical |

Measured 2026-11-18. What this compares: another implementation of
WebAssembly and the original of the host functions, on the same module.
What it does not: another TeX. A native e-TeX of the same revision was
not built (`tex.wasm` is web2js's Pascal-to-WebAssembly translation of
`tex.web` with the e-TeX changes, with LaTeX 2020-02-02 preloaded in
`core.dump`; a native binary and format of the same sources would have to
be built from them).

## Not done

- No comparison with a native TeX (see above).
- No other format: the preloaded one is LaTeX with the `standalone` class
  and TikZ. `deck/slides.tex` works inside it (its own fixed-size pages).
- No beamer and no newer `tex.wasm`: see the end of the next section.
- Host calls inside a theorem (plan2.md P1, options (a) and (b)).

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

Measured 2026-11-18, with `FAST-RUN` per stretch (`sh engine/tex/tex.sh
deck/deck.tex OUT` with `TEXPATH` set to `deck`): 606,866,720 steps in
188.3 s (3.22 M steps/s), 63,681 host calls, 63,712 stretches, each
started with the invariant; `deck.dvi` 20,992 bytes, identical to V8's
(`ref.sh`).

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
