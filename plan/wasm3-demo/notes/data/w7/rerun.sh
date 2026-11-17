#!/bin/sh
# W7 item 4: rerun the scripts that timed out in either spec run, once, with
# a doubled TIMEOUT, in the given tree (the main tree for "after", a worktree
# at the parent commit d716fa8 for "before"). Same session form as
# tests/spec/run-all.sh / run-all-3.0.sh; the output goes to OUTDIR, not to
# the tree's results directory.
#   sh rerun.sh TREE SPEC TIMEOUT OUTDIR NAME...    (inside nix develop)
set -e
tree=$1; spec=$2; timeout=$3; out=$4; shift 4
acl2=${ACL2:-acl2}
cd "$tree/translate"
if [ "$spec" = 3.0 ]; then lib=t7-lib-3.0; one=run-one-3.0.lsp; else lib=t7-lib; one=run-one.lsp; fi
"$ACL2_SYSTEM_BOOKS/build/cert.pl" --acl2 "$acl2" tests/spec/$lib > /dev/null
mkdir -p "$out"
cd tests/spec
export acl2 timeout out one
for n in "$@"; do echo "$n"; done | xargs -P 8 -I{} sh -c '
  s=$(date +%s)
  { echo "(assign t7-name \"{}\")"; cat $one; } |
    timeout -k 30 "$timeout" "$acl2" > "$out/{}.out" 2>&1
  echo "T7-EXIT $?" >> "$out/{}.out"
  echo "rerun {} $(grep -o "T7-EXIT [0-9]*" "$out/{}.out" | tail -1) $(( $(date +%s) - s ))s"'
