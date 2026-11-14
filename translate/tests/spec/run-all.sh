#!/bin/sh
# Run every spec-test-1 script (data/index.lsp) in its own ACL2 session,
# JOBS at a time, each limited to TIMEOUT seconds, and summarize.
#   sh run-all.sh ACL2 JOBS TIMEOUT        (from tests/spec/; `make spec`)
# results/NAME.out holds a session's output plus its exit status.
# Not run: skip-stack-guard-page (the spec's own stack-overflow test; there is
# no call-stack limit in the spec semantics).
set -e
acl2=$1; jobs=${2:-4}; timeout=${3:-900}
mkdir -p results
sed -n 's/^ "\(.*\)"$/\1/p' data/index.lsp | grep -v '^skip-stack-guard-page$' > results/NAMES
export acl2 timeout
xargs -P "$jobs" -I{} sh -c '
  { echo "(assign t7-name \"{}\")"; cat run-one.lsp; } |
    timeout "$timeout" "$acl2" > "results/{}.out" 2>&1
  echo "T7-EXIT $?" >> "results/{}.out"' < results/NAMES
sh summarize.sh results
