#!/bin/sh
# W0 item 5: option A cost sample. From the repo root inside `nix develop`,
# after ../w0-slice/measure.sh (which puts jscl.js in demo/build/w0/).
set -e
D=plan/wasm3-demo/notes/data/w0-numbers
sh plan/wasm3-demo/notes/data/w0-slice/run-compile.sh demo/build/w0/tower.js $D/tower.lisp > /dev/null
cd $D && node bench.js ../../../../../demo/build/w0 2>&1 | grep W0-NUM
