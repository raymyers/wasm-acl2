#!/bin/sh
# W0 item 2: run the throwaway slice extractor. From the repo root, inside
# `nix develop`, after `make -C translate gen SPEC=3.0`.
# Usage: sh plan/wasm3-demo/notes/data/w0-slice/run-extract.sh OUT.lisp
set -e
D=$(cd "$(dirname "$0")" && pwd)
OUT=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
cd translate/gen/wasm-3.0
$ACL2 <<LISP
(ld "portcullis.acl2")
:q
(load "$D/extract-slice.lisp")
(setq w0::*flatten* ${FLATTEN:-nil})
(w0::extract-slice "${ROOT:-1_4-syntax_modules}.lisp" "$OUT" (quote ${PREFIXES:-("0_" "1_")}))
LISP
