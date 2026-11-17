#!/bin/sh
# Build the MuPDF module that the engine targets (plan/wasm-engine E1 item 8).
#
# Usage: sh engine/mupdf/build.sh WORKDIR [FORK_COMMIT]
#        [DEFINES=... FEATURES=... SUFFIX=...] (passed to MuPDF's build.sh;
#        unset means MuPDF's defaults: DEFINES="-DTOFU -DTOFU_CJK_EXT
#        -DFZ_ENABLE_HYPHEN=0", FEATURES="brotli=no mujs=no extract=no
#        xps=no svg=no"). The second target of E1 item 9 is built with
#        sh engine/mupdf/build-small.sh WORKDIR.
#
# Clones the fork raymyers/mupdf at FORK_COMMIT (default: the commit below),
# installs Emscripten 4.0.8 through emsdk (nixpkgs has 6.0.x; MuPDF's
# BUILDING.md names 4.0.8), runs MuPDF's own platform/wasm/tools/build.sh
# inside a Nix shell, and writes WORKDIR/out/{mupdf-wasm.wasm,mupdf-wasm.js,
# mupdf.js,...} and WORKDIR/out/BUILD-INFO with the commit, tool versions and
# the module's sha256. The binary is not checked in: the checksum is recorded
# in plan/wasm-engine/notes/data/e1-mupdf/.
set -e
W="$1"; COMMIT="${2:-3eae43d49c1ebe9d49cff2adc4245c034b2c0692}"
EMSCRIPTEN_VERSION=4.0.8
[ -n "$W" ] || { echo "usage: $0 WORKDIR [FORK_COMMIT]"; exit 2; }
mkdir -p "$W/shim" "$W/out"; W=$(cd "$W" && pwd); cd "$W"
if [ ! -d mupdf ]; then
  git clone --branch wasm3-exceptions https://github.com/raymyers/mupdf.git mupdf
fi
# The submodule URLs in .gitmodules are relative (../thirdparty-x.git), so from
# the fork they resolve to raymyers/x, which does not exist; take
# them from Artifex's repositories.
(cd mupdf && git fetch -q origin && git checkout -q "$COMMIT" \
   && git -c url."https://github.com/ArtifexSoftware/".insteadOf=https://github.com/raymyers/ \
          submodule update --init --depth 1 --jobs 8)
[ -d emsdk ] || git clone https://github.com/emscripten-core/emsdk.git emsdk
# MuPDF's build.sh calls nproc, which darwin does not have.
printf '#!/bin/sh\nsysctl -n hw.ncpu 2>/dev/null || getconf _NPROCESSORS_ONLN\n' > shim/nproc
chmod +x shim/nproc
# emsdk needs python >= 3.10. build.sh itself activates $EMSDK.
nix shell nixpkgs#python312 nixpkgs#nodejs nixpkgs#gnumake nixpkgs#gnused nixpkgs#git -c sh -c "
  set -e
  cd '$W/emsdk' && ./emsdk install $EMSCRIPTEN_VERSION && ./emsdk activate $EMSCRIPTEN_VERSION
  cd '$W/mupdf/platform/wasm'
  export PATH='$W/shim':\$PATH EMSDK='$W/emsdk'
  ${DEFINES+export DEFINES='$DEFINES'}
  ${FEATURES+export FEATURES='$FEATURES'}
  ${SUFFIX+export SUFFIX='$SUFFIX'}
  npm install -s && bash tools/build.sh
  node --version > '$W/out/node-version'"
OUT="out${SUFFIX}"; mkdir -p "$OUT"
cp mupdf/platform/wasm/dist/* "$OUT"/
{
  echo "fork: https://github.com/raymyers/mupdf"
  echo "commit: $(cd mupdf && git rev-parse HEAD)"
  echo "emscripten: $EMSCRIPTEN_VERSION (emsdk $(cd emsdk && git rev-parse --short HEAD))"
  echo "host: $(uname -sm)"
  echo "node: $(cat out/node-version)"
  echo "DEFINES: ${DEFINES-(MuPDF default)}"
  echo "FEATURES: ${FEATURES-(MuPDF default)}"
  echo "sha256 mupdf-wasm.wasm: $(shasum -a 256 "$OUT"/mupdf-wasm.wasm | cut -d' ' -f1)"
} > "$OUT"/BUILD-INFO
cat "$OUT"/BUILD-INFO
