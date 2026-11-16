#!/bin/sh
# The spec-test-3 suite on the engine (suite-one.lsp), as run-all-3.0.sh: one
# ACL2 session per script, JOBS at a time, TIMEOUT seconds each; then the
# conformance driver's summary (same T7- lines) and who decided each action.
#   sh suite-all.sh OUTDIR [JOBS] [TIMEOUT] [NAMES-FILE]   (inside nix develop)
# Needs translate/tests/spec/data-3.0 and the certified t7-lib-3.0 and
# engine/fast/fast books.
set -e
out=$(mkdir -p "$1" && cd "$1" && pwd); jobs=${2:-8}; timeout=${3:-3600}; names=$4
here=$(cd "$(dirname "$0")" && pwd)
cd "$here/../../translate/tests/spec"
if [ -n "$names" ]; then cp "$names" "$out/NAMES"; else
  sed -n 's/^ "\(.*\)"$/\1/p' data-3.0/index.lsp | grep -v '^skip-stack-guard-page$' > "$out/NAMES"; fi
export timeout out here
xargs -P "$jobs" -I{} sh -c '
  { echo "(assign t7-name \"{}\")"; cat "$here/suite-one.lsp"; } |
    timeout -k 30 "$timeout" acl2 > "$out/{}.out" 2>&1
  echo "T7-EXIT $?" >> "$out/{}.out"' < "$out/NAMES"
sh summarize-3.0.sh "$out"
grep -ah "^ES-WHO" "$out"/*.out | awk '{ n[$3 " " $4]++ } END { for (k in n) print n[k], k }' | sort -rn > "$out/WHO"
cat "$out/WHO"
