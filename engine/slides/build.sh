#!/bin/sh
# Build the slide renderer for a deck: sh build.sh DECK.txt OUTDIR
# -> OUTDIR/sent.wasm and OUTDIR/BUILD-INFO (with the sha256). clang and lld
# come from the repository's pinned nixpkgs (flake.lock).
set -e
here=$(cd "$(dirname "$0")" && pwd); deck=$(cd "$(dirname "$1")" && pwd)/$(basename "$1"); out=$2
[ -n "$1" ] && [ -n "$out" ] || { echo "usage: $0 DECK.txt OUTDIR"; exit 2; }
mkdir -p "$out"; out=$(cd "$out" && pwd)
node "$here/gen-deck.mjs" "$deck" > "$out/deck.h"
cp "$here/font.h" "$here/sent.c" "$out/"
cd "$here/../.."
nix shell --inputs-from . nixpkgs#llvmPackages.clang-unwrapped nixpkgs#lld -c sh -c "
  cd '$out' && clang --target=wasm32 -O2 -nostdlib -mcpu=mvp -fno-builtin \
    -Wl,--no-entry -Wl,-z,stack-size=4096 -Wl,--initial-memory=65536 -Wl,--max-memory=65536 \
    -o sent.wasm sent.c && clang --version | head -1 > clang-version"
{ echo "deck: $(basename "$deck") sha256 $(shasum -a 256 "$deck" | cut -d' ' -f1)"
  echo "clang: $(cat "$out/clang-version")"
  echo "sha256 sent.wasm: $(shasum -a 256 "$out/sent.wasm" | cut -d' ' -f1)"; } > "$out/BUILD-INFO"
cat "$out/BUILD-INFO"
