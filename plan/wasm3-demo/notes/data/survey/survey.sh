#!/bin/sh
# Survey of what a JSCL build of the 3.0 semantics must handle.
# Run from the repo root after `make -C translate gen SPEC=3.0`.
# Usage: sh plan/wasm3-demo/notes/data/survey/survey.sh JSCL_CHECKOUT
set -e
J=${1:?path to a jscl checkout}
T=translate
echo "== generated 3.0 books"; ls $T/gen/wasm-3.0/*.lisp | wc -l
cat $T/gen/wasm-3.0/*.lisp | wc -l
du -k $T/gen/wasm-3.0/*.lisp | sort -n | tail -5
ALL=$(mktemp); cat $T/gen/wasm-3.0/*.lisp $T/rt/*.lisp > "$ALL"
echo "== operator heads at line starts (top 30)"
grep -oE '^\s*\((\w|-|%|\$)+' "$ALL" | sed 's/^ *//' | sort | uniq -c | sort -rn | head -30
echo "== ACL2 / numeric constructs anywhere"
grep -oiE '\((let\*|natp|nfix|1\+|nthcdr|take|not|expt|1-|in-package|zp|include-book|ifix|cond|floor|mod|len|rem|case|the|ash|reverse|integer-length|catch|truncate|min|max|make-event|logior|logand|integerp|defthm|defmacro|mv|lognot|local|verify-guards|value-triple|table|stringp|rfix|posp|member-equal|in-theory|implies|assoc-equal|prog2\$|numerator|mv-let|memoize|logxor|logbitp|iff|evenp|er|encapsulate|denominator|defattach)[ )]' "$ALL" | tr A-Z a-z | sort | uniq -c | sort -rn
echo "== package-qualified heads"; grep -o '(ACL2[^ ]*' "$ALL" | sort | uniq -c | sort -rn | head
rm -f "$ALL"
echo "== jscl rev"; git -C "$J" log -1 --format='%H %cd'
echo "== jscl number predicates"; grep -n 'defun \(integerp\|rationalp\)' "$J"/src/numbers.lisp
grep -n 'most-integer-length\|BigInt' "$J"/src/numbers.lisp "$J"/src/format.lisp
echo "== jscl equal"; grep -n 'defun equal' -A8 "$J"/src/boot.lisp
