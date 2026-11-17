#!/bin/sh
# W0 item 2: compile the extracted slice with JSCL (inside `nix develop`).
# Usage: sh run-compile.sh OUT.js FILE.lisp...   (prints the error, if any,
# without SBCL's backtrace)
D=$(cd "$(dirname "$0")" && pwd)
OUT=$1; shift
IN="$*" OUT=$OUT jscl-xc --non-interactive --load $D/compile.lisp > $OUT.log 2>&1
st=$?
grep -v '^loading\|^ *elapsed\|^ *compile \|^build standard' $OUT.log | sed -n '/^Backtrace/q;p' | tail -200
exit $st
