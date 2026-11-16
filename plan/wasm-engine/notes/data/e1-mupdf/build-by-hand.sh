#!/bin/sh
# How the first build of the fork was made (2026-11-15, darwin arm64). Not yet a
# reproducible build: E1 has an item to move this into engine/mupdf/ under Nix.
# Usage: sh build-by-hand.sh WORKDIR
set -e
W="$1"; mkdir -p "$W/shim"; cd "$W"
git clone --depth 1 --branch wasm3-exceptions https://github.com/raymyers/mupdf.git mupdf
(cd mupdf && git submodule update --init --depth 1 --jobs 8)
git clone --depth 1 https://github.com/emscripten-core/emsdk.git emsdk
printf '#!/bin/sh\nsysctl -n hw.ncpu 2>/dev/null || getconf _NPROCESSORS_ONLN\n' > shim/nproc; chmod +x shim/nproc
# emsdk needs python >= 3.10; build.sh installs and activates Emscripten 4.0.8 itself
nix shell nixpkgs#python312 nixpkgs#nodejs nixpkgs#gnumake nixpkgs#gnused -c sh -c "
  cd emsdk && ./emsdk install 4.0.8 && ./emsdk activate 4.0.8 && cd ../mupdf/platform/wasm &&
  export PATH=$W/shim:\$PATH EMSDK=$W/emsdk && npm install -s && bash tools/build.sh"
shasum -a 256 mupdf/platform/wasm/dist/mupdf-wasm.wasm
