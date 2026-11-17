#!/bin/sh
# Typeset deck.tex with tex.wasm on the engine and make a PDF of it.
#   sh build.sh                (inside nix develop; needs ../build/acl2-wasm-tex)
#   SLIDES=13,14 sh build.sh   only those slides, for a quick look
# -> ../build/deck/deck.dvi (written by the engine) and deck.pdf (dvipdfmx,
#    native, which also embeds the images of latex-slides/figs).
# The first run saves an image of the engine just after \begin{document}
# (deck.core, 2 GB); later runs start there until the preamble changes.
set -e
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../../.." && pwd)
out=$here/../build/deck; mkdir -p "$out"
node "$here/figdims.mjs" "$root/latex-slides/figs" figs/ > "$here/figdims.tex"
in=$here/deck.tex
if [ -n "$SLIDES" ]; then in=$out/picked.tex; node "$here/pick.mjs" "$here/deck.tex" "$SLIDES" > "$in"; fi
export TEXPATH=$here:$out
stamp=$( { sed '/^%%% snapshot/q' "$here/deck.tex"; cat "$here/slides.tex" "$here/figdims.tex"
           ls -l "$here/../build/acl2-wasm-tex"; } | shasum | cut -d' ' -f1)
if [ ! -f "$out/deck.core" ] || [ "$(cat "$out/deck.stamp" 2>/dev/null)" != "$stamp" ]; then
  TEXSNAP=$out/deck.core sh "$here/../tex.sh" "$here/deck.tex" "$out/snap" > "$out/snap.out" 2>&1 || true
  grep -E '^SNAPSHOT|^DRIVER' "$out/snap.out"
  [ -f "$out/deck.core" ] && echo "$stamp" > "$out/deck.stamp"
fi
TEXCORE=$out/deck.core sh "$here/../tex.sh" "$in" "$out/deck" > "$out/run.out" 2>&1 || true
grep -E '^TOTAL|^DRIVER' "$out/run.out" || true
grep -n -A4 '^!' "$out/deck.log" | head -60 || true   # TeX errors, if any
cd "$here"   # figs/ is here
nix shell --inputs-from "$root" nixpkgs#texliveSmall -c dvipdfmx -q -o "$out/deck.pdf" "$out/deck.dvi"
echo "$(sed -n 's/^SLIDES //p' "$out/deck.log") slides -> $out/deck.pdf"
