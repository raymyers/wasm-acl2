#!/bin/sh
# W0 item 4: stack capacity probes. From the repo root inside `nix develop`.
# Compiles probe.lisp to demo/build/w0/probe.js (needs demo/build/w0/jscl.js,
# written by ../w0-slice/measure.sh), then runs it in node (main thread,
# default and --stack-size=3900; workers with 16 and 64 MB) and in headless
# Chromium and Firefox (page and Worker).
set -e
D=plan/wasm3-demo/notes/data/w0-depth
sh plan/wasm3-demo/notes/data/w0-slice/run-compile.sh demo/build/w0/probe.js $D/probe.lisp > /dev/null
(cd $D && node probe-node.js ../../../../../demo/build/w0 16 64 && node --stack-size=3900 probe-node.js ../../../../../demo/build/w0) 2>&1 | grep W0-PROBE
node $D/probe-browser.mjs demo/build/w0 2>&1 | grep W0-PROBE
