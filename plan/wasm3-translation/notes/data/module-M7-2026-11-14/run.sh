#!/bin/sh
# Probe 3.0 (D3 scope) with Module_ok compiled in mode (:given "C" "C'"): the
# two contexts are extra inputs. From translate/ inside `nix develop ..`.
set -e
D=$(cd "$(dirname "$0")" && pwd)
T=$(mktemp -d)
perl -0pe 's/\n\)\s*\z/\n (:modes "x" :pairs (("Module_ok" . (:given "C" "C\x27"))) :reason "experiment")\n)\n/' config/wasm-3.0.lsp > $T/given.lsp
make probe SPEC=3.0 EXCLUDE='X.* 6.* 7.*' PROBE_CONFIG=$T/given.lsp > /dev/null
cp .probe/3.0/report.txt $D/report-3.0-core-given.txt
cp .probe/3.0/rules.txt $D/report-3.0-core-given-rules.txt
rm -rf $T
