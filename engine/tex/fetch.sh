#!/bin/sh
# Fetch the third-party files of the TeX spike into build/dl and check them.
#   sh fetch.sh
# tex.wasm, core.dump and the TeX files are the TikZJax build of web2js TeX
# (npm node-tikzjax 1.0.5, LPPL 1.3c); fonts.json holds the TFM font metrics
# (npm @prinsss/dvi2html 0.0.1). None of them is checked in.
set -e
here=$(cd "$(dirname "$0")" && pwd); dl=$here/build/dl
mkdir -p "$dl" && cd "$dl"
get() { [ -f "$2" ] || curl -sSL -o "$2" "$1"; echo "$3  $2" | shasum -a 256 -c -; }
t=https://cdn.jsdelivr.net/npm/node-tikzjax@1.0.5/tex
get $t/tex.wasm.gz tex.wasm.gz f8667f45e90039832df4f62550f10ff0c2f47781dbfdde9510f0ff3f360a61ba
get $t/core.dump.gz core.dump.gz ae9f69dfe3837606240c5b9cb50f86aa0ee7463bbae4c26f2843b17eb155b91f
get $t/tex_files.tar.gz tex_files.tar.gz 492271c589ab2d7b64c22a09f927ea09cd5ee3fc696a46067ddea2da4693c86f
get https://cdn.jsdelivr.net/npm/@prinsss/dvi2html@0.0.1/lib/tfm/fonts.json fonts.json \
  47501544fbf1a3ffc95346bb12b98e8c89ccee604d57f3092b35c8136e05cd76
gunzip -kf tex.wasm.gz core.dump.gz
rm -rf tex_files && mkdir tex_files && tar xzf tex_files.tar.gz -C tex_files
# the host's file directory: the TeX files and the font metrics, flat
node "$here/mkfs.mjs" "$dl" "$here/build/fs"
