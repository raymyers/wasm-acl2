#!/bin/sh
# Build the synthetic modules m-N.wasm (python3 from the host, wat2wasm from
# nix develop).
set -e; cd "$(dirname "$0")"
for n in 100 400 1600 6400; do python3 -I gen.py $n > m-$n.wat; done
nix develop ../../.. -c sh -c 'for n in 100 400 1600 6400; do wat2wasm m-$n.wat -o m-$n.wasm; done' > /dev/null
rm m-*.wat; ls -l *.wasm
