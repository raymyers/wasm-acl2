#!/bin/sh
# Run every spec-test-3 script (data-3.0/index.lsp) in its own ACL2 session,
# JOBS at a time, each limited to TIMEOUT seconds, and summarize (wasm3 M4).
#   sh run-all-3.0.sh ACL2 JOBS TIMEOUT    (from tests/spec/; make spec SPEC=3.0)
# results-3.0/NAME.out holds a session's output plus its exit status.
# Not run: skip-stack-guard-page (no call-stack limit in the spec semantics).
# timeout -k: the acl2 wrapper starts SBCL as a child, and an ACL2 session
# does not stop on TERM while it computes; KILL follows 30 s later.
set -e
acl2=$1; jobs=${2:-8}; timeout=${3:-600}
out=results-3.0
rm -rf $out && mkdir -p $out
sed -n 's/^ "\(.*\)"$/\1/p' data-3.0/index.lsp | grep -v '^skip-stack-guard-page$' > $out/NAMES
export acl2 timeout out
xargs -P "$jobs" -I{} sh -c '
  { echo "(assign t7-name \"{}\")"; cat run-one-3.0.lsp; } |
    timeout -k 30 "$timeout" "$acl2" > "$out/{}.out" 2>&1
  echo "T7-EXIT $?" >> "$out/{}.out"' < $out/NAMES
sh summarize-3.0.sh $out
