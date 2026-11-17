#!/bin/sh
# W7 item 4: every script that timed out or crashed in either spec run
# (compare-3.0.out, compare-1.0.out), rerun once with a doubled TIMEOUT
# (3.0: 2 x 600 s; 1.0: 2 x 3600 s) before (worktree at d716fa8, BEFORE)
# and after (this tree). At most 10 sessions at a time (10 cores), so the
# timeouts are not skewed by load. data and elem (1.0) exhaust SBCL's heap
# in $INITDATA, so they run one at a time (each grows to about 32 GB).
#   sh rerun-all.sh BEFORE_TREE 1.0    (inside nix develop)
#   sh rerun-all.sh BEFORE_TREE 3.0
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../../../../.." && pwd)
before=$1
B=/Users/Apple/dev/wasm-acl2-w7-baseline; A=/Users/Apple/dev/wasm-acl2-w7-after
T3="bulk-memory--memory_copy call call_indirect call_ref memory64--memory_copy64"
if [ "$2" = 3.0 ]; then
  sh "$here/rerun.sh" "$before" 3.0 1200 $B/rerun-3.0 $T3
  sh "$here/rerun.sh" "$root" 3.0 1200 $A/rerun-3.0 $T3
else
  sh "$here/rerun.sh" "$root" 1.0 7200 $A/rerun-1.0 call call_indirect &
  sh "$here/rerun.sh" "$before" 1.0 7200 $B/rerun-1.0 call call_indirect &
  for n in data elem; do
    sh "$here/rerun.sh" "$root" 1.0 7200 $A/rerun-1.0 $n
    sh "$here/rerun.sh" "$before" 1.0 7200 $B/rerun-1.0 $n
  done
  wait
fi
