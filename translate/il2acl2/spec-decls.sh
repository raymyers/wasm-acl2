#!/bin/sh
# Print the declarations of the given .spectec files as an ACL2 list of
# (kind id file), kind one of "syntax" "def" "relation" "grammar", file the
# basename without .spectec, in file order. The flake writes it next to the IL
# (il/wasm-<v>.decls.lsp): gen splits its output into one book per source
# file, and `make probe` groups stubs by file. Only the first declaration of
# an id counts (later `syntax x/...` lines extend it).
echo "("
for f in "$@"; do
  b=$(basename "$f" .spectec)
  sed -n -E 's/^(syntax|def|relation|grammar)[[:space:]]+\$?([A-Za-z0-9_'"'"']+).*/\1 \2/p' "$f" |
    while read -r kind id; do echo "(\"$kind\" \"$id\" \"$b\")"; done
done | awk '!seen[$1 $2]++'
echo ")"
