#!/bin/sh
# Commands by kind in the scripts converted through the reference
# interpreter (REFINTERP of the wasm3-spec-tests flake output), per
# proposal directory and in total. From the repo root.
REF=$(nix build .#wasm3-spec-tests --no-link --print-out-paths)
echo "scripts: $(grep -c '^ "' $REF/index.lsp) in index.lsp; via the reference interpreter: $(wc -l < $REF/REFINTERP); skipped: $(cat $REF/SKIPPED 2> /dev/null | wc -l | tr -d ' ')"
for g in core exceptions gc memory64 bulk-memory; do
  if [ $g = core ]; then l=$(grep -v -- "--" $REF/REFINTERP); else l=$(grep "^$g--" $REF/REFINTERP); fi
  [ -n "$l" ] || continue
  printf "%-12s %2d scripts:" $g $(echo "$l" | wc -l)
  for b in $l; do grep -o "^ (:[A-Z_]*" $REF/$b.lsp; done | sort | uniq -c | sort -rn | awk '{printf " %s %s", substr($2,3), $1}'; echo
done
printf "%-12s %2d scripts:" total $(wc -l < $REF/REFINTERP)
for b in $(cat $REF/REFINTERP); do grep -o "^ (:[A-Z_]*" $REF/$b.lsp; done | sort | uniq -c | sort -rn | awk '{printf " %s %s", substr($2,3), $1}'; echo
