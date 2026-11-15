#!/bin/sh
# Validate the modules of the scripts converted through the reference
# interpreter with the interpreter itself: every instantiated module must
# validate, every assert_invalid module must be rejected. From the repo root.
W=$(nix build .#wasm-ref-interp --no-link --print-out-paths)/bin/wasm
REF=$(nix build .#wasm3-spec-tests --no-link --print-out-paths)
files() { for b in $(cat $REF/REFINTERP); do grep -o "^ (:$1 \"[^\"]*\"" $REF/$b.lsp | cut -d'"' -f2; done | sort -u; }
v=0; nv=0; for f in $(files MODULE); do if $W -d $REF/$f > /dev/null 2>&1; then v=$((v+1)); else nv=$((nv+1)); echo "does not validate: $f"; fi; done
r=0; a=0; for f in $(files ASSERT_INVALID); do if $W -d $REF/$f > /dev/null 2>&1; then a=$((a+1)); echo "accepted: $f"; else r=$((r+1)); fi; done
echo "instantiated modules (distinct files): $v validate, $nv do not"
echo "assert_invalid modules: $r rejected, $a accepted"
