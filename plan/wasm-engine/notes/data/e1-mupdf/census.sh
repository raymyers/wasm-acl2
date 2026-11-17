#!/bin/sh
# Opcode census of a wasm binary: count per mnemonic, most frequent first.
# Usage (inside `nix develop`, which provides wabt): sh census.sh module.wasm > opcodes.txt
wasm-objdump -d "$1" 2>/dev/null \
  | awk -F'|' 'NF>1{split($2,a," "); print a[1]}' | sort | uniq -c | sort -rn
