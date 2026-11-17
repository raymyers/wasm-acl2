# LaTeX on the engine (spike)

`tex.wasm` (web2js TeX, the TikZJax build: e-TeX with LaTeX preloaded) runs
on the engine's fast machine and writes a DVI file. A spike of 2026-11-16,
not part of `make -C engine check`.

## Run

Inside `nix develop`, with the engine books certified:

```sh
sh engine/tex/fetch.sh                  # third-party files -> build/dl, build/fs
TEXMODE=build sh engine/tex/run.sh      # build/tex.core: an image that starts at TeX's main
sh engine/tex/tex.sh engine/tex/input.tex engine/tex/build/out   # -> out.dvi, out.log
python3 -I engine/tex/dvitype.py engine/tex/build/out.dvi        # what the DVI sets (any python3; the dev shell has none)
```

`sh engine/tex/run.sh` without `TEXMODE` does the same in one process,
without saving an image. To view a DVI: `dvipdfmx` from TeX Live
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
- The preloaded format is LaTeX with the `standalone` class and TikZ: pages
  are cropped to their content. Slides need a fixed page size.
- About 9 s of every run is LaTeX's fixed work at `\begin{document}` and
  shipout; a memory dump taken after the preamble would remove most of it.
