#!/bin/sh
# Assemble the E0 benchmarks: each NAME.wat with its memory at 1, 16 and 64
# pages -> wasm/NAME-PAGES.wasm. Run inside `nix develop` (wabt).
set -e; cd "$(dirname "$0")"; mkdir -p wasm
for w in *.wat; do n=${w%.wat}
  for p in 1 16 64; do
    sed "s/PAGES/$p/" "$w" > wasm/$n-$p.wat
    wat2wasm --enable-exceptions wasm/$n-$p.wat -o wasm/$n-$p.wasm
    rm wasm/$n-$p.wat
  done
done
ls wasm
