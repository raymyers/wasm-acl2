#!/bin/sh
# E7 differential test 3 over the spec-test-3 scripts (as run-all-3.0.sh:
# one ACL2 session per script, JOBS at a time, TIMEOUT seconds each).
#   sh difftest2-all.sh OUTDIR [JOBS] [TIMEOUT] [NAMES-FILE]   (inside nix develop)
# Needs translate/tests/spec/data-3.0 (make spec-data SPEC=3.0) and the
# certified t7-lib-3.0 and engine/fast/fast books.
set -e
out=$(mkdir -p "$1" && cd "$1" && pwd); jobs=${2:-8}; timeout=${3:-900}; names=$4
here=$(cd "$(dirname "$0")" && pwd)
cd "$here/../../translate/tests/spec"
if [ -n "$names" ]; then cp "$names" "$out/NAMES"; else
  sed -n 's/^ "\(.*\)"$/\1/p' data-3.0/index.lsp | grep -v '^skip-stack-guard-page$' > "$out/NAMES"; fi
export timeout out here
xargs -P "$jobs" -I{} sh -c '
  { echo "(assign t7-name \"{}\")"; cat "$here/difftest3-one.lsp"; } |
    timeout -s KILL "$timeout" acl2 > "$out/{}.out" 2>&1
  echo "D3-EXIT $?" >> "$out/{}.out"' < "$out/NAMES"
grep -ho "D3-CMD.*" "$out"/*.out | sort | uniq -c; grep -ho "D3-DIFF.*" "$out"/*.out | head -20; grep -L "D3-DONE" "$out"/*.out
