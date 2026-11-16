{
  description = "WASM 1.0 ACL2 formalization — certified with ACL2 + the Kestrel community books";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

    # SpecTec + the WASM 1.0 SpecTec source, pinned. Input to the
    # deterministic translation in translate/ (plan/wasm1-translation).
    wasm-spec = {
      url = "github:WebAssembly/spec/943c5df07e84f11d2b83078964df5812530afbd2";
      flake = false;
    };

    # JSCL, pinned (demo plan D2): compiles the extracted 3.0 semantics to JS.
    jscl-src = {
      url = "github:jscl-project/jscl/54c88494e9f8f22e4c24c666e84aab7053f18cee";
      flake = false;
    };
  };

  outputs =
    {
      self,
      nixpkgs,
      wasm-spec,
      jscl-src,
    }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      lib = nixpkgs.lib;

      forAllSystems = f: lib.genAttrs systems (system: f (pkgsFor system));

      # Every community book this tree pulls in with `:dir :system`, scraped
      # from the sources at eval time so the list cannot drift. Reading the
      # files during evaluation (rather than passing the tree into the ACL2
      # derivation) keeps ACL2 out of the rebuild path for ordinary edits: only
      # a change to the *set of includes* rebuilds it.
      systemBooks =
        let
          lispIn =
            dir:
            map (name: dir + "/${name}") (
              builtins.attrNames (lib.filterAttrs (n: t: t == "regular") (builtins.readDir dir))
            );
          sources = lispIn ./. ++ lispIn ./proofs ++ lispIn ./tests;
          includesIn =
            file:
            let
              parts = builtins.split ''include-book "([^"]+)" :dir :system'' (builtins.readFile file);
            in
            map builtins.head (builtins.filter builtins.isList parts);
        in
        lib.naturalSort (
          lib.unique (
            lib.concatMap includesIn (
              builtins.filter (f: lib.hasSuffix ".lisp" f || lib.hasSuffix ".acl2" f) sources
            )
          )
        );

      # The community books carry a couple of unfree-redistributable licenses,
      # which taints nixpkgs' `acl2` whenever books are included. We only build
      # a small subset of them, but the license attribute is per-package, so
      # allow it explicitly here rather than making every user set it.
      pkgsFor =
        system:
        import nixpkgs {
          inherit system;
          config.allowUnfreePredicate = pkg: nixpkgs.lib.hasPrefix "acl2" (nixpkgs.lib.getName pkg);
        };
    in
    {
      packages = forAllSystems (
        pkgs:
        let
          mkIl =
            spectec: v: exclude:
            pkgs.runCommand "wasm${builtins.head (lib.splitString "." v)}-il" { } ''
              mkdir -p $out
              files=
              for f in ${wasm-spec}/specification/wasm-${v}/*.spectec; do
                case $(basename $f) in
                  ${if exclude == [ ] then "__none__" else lib.concatStringsSep " | " exclude}) ;;
                  *) files="$files $f"; echo $(basename $f) >> $out/FILES ;;
                esac
              done
              ${spectec}/bin/spectec --ast --all-passes $files > $out/wasm-${v}.il.sexp
              sh ${./translate/il2acl2/spec-decls.sh} $files > $out/wasm-${v}.decls.lsp
            '';
          # The reference interpreter of the pinned spec (`wasm`), for the
          # spec-test-3 scripts that wast2json cannot read (wasm3 M0b): it
          # rewrites a .wast with every module in binary form (`-o x.bin.wast`).
          # Only the native executable is built (wast.js would need js_of_ocaml).
          wasmRefInterp =
            let
              ocp = pkgs.ocaml-ng.ocamlPackages_5_4;
            in
            pkgs.stdenv.mkDerivation {
              pname = "wasm-ref-interp";
              version = builtins.substring 0 7 wasm-spec.rev;
              src = wasm-spec;
              nativeBuildInputs = [
                ocp.ocaml
                ocp.dune_3
                ocp.findlib
                ocp.menhir
              ];
              buildPhase = ''
                runHook preBuild
                cd interpreter
                dune build --profile release ./wasm.exe
                runHook postBuild
              '';
              installPhase = ''
                runHook preInstall
                install -Dm755 _build/default/wasm.exe $out/bin/wasm
                runHook postInstall
              '';
              meta.description = "WebAssembly reference interpreter at ${wasm-spec.rev}";
            };

          # spec-test-<major> converted for the conformance driver (see below)
          mkSpecTests =
            major: flags: withSpectest: withRefInterp:
            # withSpectest: false, or the spectest .wat file to compile
            pkgs.runCommand "wasm${major}-spec-tests"
              {
                nativeBuildInputs = [
                  pkgs.wabt
                  pkgs.nodejs
                ]
                ++ lib.optional withRefInterp wasmRefInterp;
              }
              ''
                mkdir -p $out work
                suite=${wasm-spec}/spectec/test-interpreter/spec-test-${major}
                for f in $suite/*.wast $suite/*/*.wast; do
                  [ -e "$f" ] || continue
                  rel=''${f#$suite/}
                  b=$(echo "''${rel%.wast}" | sed 's|/|--|g')
                  mkdir -p work/$b
                  if ! (cd work/$b && wast2json ${flags} $f -o $b.json > /dev/null 2>&1); then
                    rm -rf work/$b
                    if [ -n "${lib.optionalString withRefInterp "y"}" ] \
                      && mkdir -p work/$b && wasm -d $f -o work/$b/$b.bin.wast > /dev/null 2>&1; then
                      echo $b >> $out/REFINTERP
                    else
                      echo $b >> $out/SKIPPED
                      rm -rf work/$b
                    fi
                  fi
                done
                for d in work/*; do cp $d/*.wasm $out/ 2> /dev/null || true; done
                node ${./translate/tests/oracle/gen-spec-tests.mjs} work $out spec-test-${major}
                ${lib.optionalString (withSpectest != false) "wat2wasm --enable-memory64 ${withSpectest} -o $out/spectest.wasm"}
              '';
        in
        rec {
        default = wasm-acl2;

        # Demo toolchain (plan/wasm3-demo D2, D8).
        jscl = import ./nix/jscl.nix {
          inherit pkgs;
          src = jscl-src;
        };
        # wabt's JS build (wabt.js, one file with the wasm inlined): the page
        # converts WAT to binary with it (D3). Pinned npm tarball.
        wabt-js =
          pkgs.runCommand "wabt-js-1.0.39"
            {
              src = pkgs.fetchurl {
                url = "https://registry.npmjs.org/wabt/-/wabt-1.0.39.tgz";
                hash = "sha256-oQ1PSxW5HeirLMtHAO8SGFc28LyW7oCeU6sX9+p0P9I=";
              };
            }
            ''
              mkdir -p $out/lib/node_modules/wabt
              tar xzf $src -C $out/lib/node_modules/wabt --strip-components=1
            '';

        # The WASM 3.0 demo page as a static directory (plan/wasm3-demo W9):
        # regenerates translate/gen/wasm-3.0 from the checked-in IL (`make gen`,
        # nothing certified but the translator), extracts it, compiles it with
        # JSCL and assembles demo/build/web (`make -C demo web`). $out is the
        # site root (index.html, the Worker, jscl.js, wasm3.js, wabt.js).
        wasm3-demo = pkgs.stdenv.mkDerivation {
          pname = "wasm3-demo";
          version = "0.1";
          src = builtins.path {
            path = ./.;
            name = "wasm3-demo-source";
            filter =
              path: type:
              !(builtins.elem (baseNameOf path) [
                ".git"
                "result"
                "plan"
                "build"
              ]);
          };
          nativeBuildInputs = [
            acl2
            jscl
            pkgs.gnumake
            pkgs.nodejs
            pkgs.perl
            pkgs.which
            pkgs.hostname
          ];
          # cert.pl wants a real HOME and a nonempty USER.
          buildPhase = ''
            export HOME=$TMPDIR/home USER=nobody
            mkdir -p $HOME
            export ACL2=${acl2}/bin/acl2
            export ACL2_SYSTEM_BOOKS=${acl2}/share/acl2/books
            export CERT=$ACL2_SYSTEM_BOOKS/build/cert.pl
            export JSCL_HOME=${jscl}/share/jscl
            export WABT_JS=${wabt-js}/lib/node_modules/wabt
            make -C translate gen SPEC=3.0 ACL2=$ACL2 CERT=$CERT JOBS=''${NIX_BUILD_CORES:-4}
            make -C demo web
          '';
          installPhase = ''
            mkdir -p $out
            cp -R demo/build/web/. $out/
          '';
          meta = {
            description = "WASM 3.0 run by its SpecTec semantics (ACL2, compiled to JavaScript by JSCL) in the browser";
            platforms = systems;
          };
        };

        # The reference interpreter (see wasmRefInterp above), wasm3 M0b.
        wasm-ref-interp = wasmRefInterp;

        # SpecTec (the WASM spec DSL toolchain) at the pinned wasm-spec rev.
        # Mirrors spectec/Makefile: the reference interpreter is copied into
        # the backend-interpreter tree before `dune build`.
        spectec =
          let
            ocp = pkgs.ocaml-ng.ocamlPackages_5_4;
          in
          pkgs.stdenv.mkDerivation {
            pname = "spectec";
            version = "0.5-${builtins.substring 0 7 wasm-spec.rev}";
            src = wasm-spec;
            # Print hint definitions in the --ast output (wasm3 prep P3, D5):
            # hint(inverse), hint(builtin), ... reach the translator.
            patches = [ ./nix/spectec-ast-print-hints.patch ];
            nativeBuildInputs = [
              ocp.ocaml
              ocp.dune_3
              ocp.findlib
              ocp.menhir
            ];
            buildInputs = [
              ocp.menhirLib
              ocp.zarith
            ];
            buildPhase = ''
              runHook preBuild
              cd spectec
              ref=src/backend-interpreter/reference-interpreter
              rm -rf $ref
              cp -R ../interpreter $ref
              chmod -R u+w $ref
              rm -r $ref/dune-project $ref/jslib
              cp src/backend-interpreter/dune-ref-interp $ref/dune
              dune build --profile release src/exe-spectec/main.exe
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              install -Dm755 _build/default/src/exe-spectec/main.exe $out/bin/spectec
              mkdir -p $out/share/spectec
              cp -R ../specification/wasm-1.0 $out/share/spectec/wasm-1.0
              echo ${wasm-spec.rev} > $out/share/spectec/REV
              runHook postInstall
            '';
            meta.description = "SpecTec ${wasm-spec.rev} with the WASM 1.0 spec sources";
          };

        # The WASM 1.0 IL as S-expressions: the contract between SpecTec and
        # the ACL2 translator. translate/il/wasm-1.0.il.sexp must equal this.
        wasm1-il = pkgs.runCommand "wasm1-il" { } ''
          mkdir -p $out
          ${spectec}/bin/spectec --ast --all-passes \
            ${spectec}/share/spectec/wasm-1.0/*.spectec > $out/wasm-1.0.il.sexp
          sh ${./translate/il2acl2/spec-decls.sh} ${spectec}/share/spectec/wasm-1.0/*.spectec > $out/wasm-1.0.decls.lsp
        '';

        # The 2.0 and 3.0 IL (wasm3 prep P2; `make -C translate il SPEC=<v>`).
        # The file list is the version's directory minus the globs in
        # `exclude`, listed in $out/FILES. 3.0 leaves out the notation (X.*),
        # text format (6.*) and soundness (7.*) files: decision D3 of
        # plan/wasm3-translation-prep, recommended and not yet confirmed.
        wasm2-il = mkIl spectec "2.0" [ ];
        wasm3-il = mkIl spectec "3.0" [
          "X.*"
          "6.*"
          "7.*"
        ];

        # Conformance data (wasm1 T7, wasm3 prep P5): spec-test-<major> of the
        # pinned spec as .wasm modules plus ACL2 command lists
        # (translate/tests/oracle/gen-spec-tests.mjs). `make -C translate
        # spec-data` copies 1.0's, with the `spectest` host module, to
        # translate/tests/spec/data. Scripts that wast2json cannot read (1.0:
        # the old assert_return_*_nan syntax; 3.0: wabt lacks some GC,
        # exception and module-definition syntax) go, for 3.0, through the
        # reference interpreter (a .bin.wast, read by the same script; listed in
        # REFINTERP, wasm3 M0b); the rest are left out and listed in SKIPPED.
        # Scripts of a subdirectory (3.0's proposals) are DIR--NAME.
        wasm1-spec-tests = mkSpecTests "1" (lib.concatStringsSep " " [
          "--disable-saturating-float-to-int"
          "--disable-sign-extension"
          "--disable-multi-value"
          "--disable-bulk-memory"
          "--disable-reference-types"
          "--disable-simd"
          "--disable-mutable-globals"
        ]) ./translate/tests/spec/spectest.wat false;
        # The 3.0 proposals only. Not --enable-all: it includes compact imports (not
        # in 3.0), which wabt then writes, and 70 modules no longer decode (wasm3 M2).
        wasm3-spec-tests = mkSpecTests "3" (lib.concatStringsSep " " [
          "--enable-annotations"
          "--enable-exceptions"
          "--enable-extended-const"
          "--enable-function-references"
          "--enable-gc"
          "--enable-memory64"
          "--enable-multi-memory"
          "--enable-relaxed-simd"
          "--enable-tail-call"
        ]) ./translate/tests/spec/spectest-3.0.wat true;

        # ACL2 plus just the community books this project depends on.
        #
        # Two changes on top of nixpkgs' acl2:
        #
        #  * ACL2 8.7 instead of 8.6 — `books/kestrel/wasm` (the portcullis this
        #    tree's package comes from) was only added after the 8.6 release.
        #    Both of the nixpkgs patches still apply; the extra fetchpatch for
        #    the input-files regression is already upstream in 8.7, so it goes.
        #
        #  * Certify only our dependency closure. nixpkgs either certifies
        #    *every* community book (many hours, >100GB RAM at high -j) or ships
        #    none at all; we need the books listed in `systemBooks` above, and
        #    the books Makefile pulls in whatever those transitively need.
        #
        # Everything is certified in place under $out because ACL2 proof
        # artifacts are not relocatable.
        acl2 = pkgs.acl2.overrideAttrs (old: {
          pname = "acl2-with-wasm-books";
          version = "8.7";

          src = pkgs.fetchFromGitHub {
            owner = "acl2";
            repo = "acl2";
            tag = "8.7";
            hash = "sha256-mkbi7xkUJSZyk7h/dUwSjlNSBS7dJGAwHD4qNHxwOYM=";
          };

          # Drop nixpkgs' first patch (the 8.6-only input-files fetchpatch),
          # keep the path-rewriting and aarch64-linux float-trap ones.
          patches = builtins.tail old.patches;

          certifyBooksPhase = ''
            pushd $out/share/acl2/books

            # cert.pl needs build/*.certdep, which only the books Makefile
            # generates.
            make ACL2=$out/share/acl2/saved_acl2 ACL2_MAKE_LOG=NONE \
              build/Makefile-features

            # Certify with cert.pl rather than `make <book>.cert`: the two
            # compute different dependency sets (cert.pl's is larger), and the
            # downstream build uses cert.pl — so anything it considers a
            # dependency has to exist here, in the store, already certified.
            build/cert.pl \
              --acl2 $out/share/acl2/saved_acl2 \
              -j ''${NIX_BUILD_CORES:-4} \
              ${lib.concatStringsSep " \\\n              " systemBooks}

            # NB: unlike nixpkgs, we do *not* delete the `@useless-runes.lsp`
            # files afterwards. They are recorded as make prerequisites of the
            # .cert files, so deleting them makes a downstream `make` treat
            # those books as out of date and try to recertify them inside the
            # read-only store.
            popd
          '';

          meta = old.meta // {
            description = "ACL2 with the community books needed by wasm-acl2 certified";
          };
        });

        # `nix build` == `make all`: certifies top + all 27 proof books + all 15
        # test books. A successful build *is* the proof that everything checks.
        wasm-acl2 = pkgs.stdenv.mkDerivation {
          pname = "wasm-acl2";
          version = "1.0";

          src = builtins.path {
            path = ./.;
            name = "wasm-acl2-source";
            filter =
              path: type:
              let
                base = baseNameOf path;
              in
              !(builtins.elem base [
                ".git"
                "result"
                "translate"
                "plan"
              ]);
          };

          nativeBuildInputs = [
            acl2
            pkgs.perl
            pkgs.which
            pkgs.hostname
          ];

          # cert.pl wants a real HOME and a nonempty USER.
          preBuild = ''
            export HOME=$TMPDIR/home
            mkdir -p $HOME
            export USER=nobody
            export ACL2_SYSTEM_BOOKS=${acl2}/share/acl2/books
          '';

          # Build in place: .cert files reference the tree they were made in.
          buildPhase = ''
            runHook preBuild

            mkdir -p $out/share/wasm-acl2
            cp -pR . $out/share/wasm-acl2
            cd $out/share/wasm-acl2

            make all \
              ACL2=${acl2}/bin/acl2 \
              CERT=${acl2}/share/acl2/books/build/cert.pl \
              JOBS=''${NIX_BUILD_CORES:-4}

            runHook postBuild
          '';

          installPhase = "true"; # already installed by buildPhase

          meta = {
            description = "Machine-checked WASM 1.0 operational semantics in ACL2";
            homepage = "https://github.com/raymyers/wasm-acl2";
            license = pkgs.lib.licenses.mit;
            platforms = systems;
          };
        };
        }
      );

      checks = forAllSystems (pkgs: {
        inherit (self.packages.${pkgs.stdenv.hostPlatform.system}) wasm-acl2;

        # Determinism of the SpecTec -> IL step: two independent runs agree,
        # and both equal the IL checked in under translate/il/.
        translate-il =
          let
            spectec = self.packages.${pkgs.stdenv.hostPlatform.system}.spectec;
          in
          pkgs.runCommand "translate-il-check" { } ''
            src=${spectec}/share/spectec/wasm-1.0
            ${spectec}/bin/spectec --ast --all-passes $src/*.spectec > a.sexp
            ${spectec}/bin/spectec --ast --all-passes $src/*.spectec > b.sexp
            cmp a.sexp b.sexp
            cmp a.sexp ${./translate/il/wasm-1.0.il.sexp}
            sh ${./translate/il2acl2/spec-decls.sh} $src/*.spectec > decls.lsp
            cmp decls.lsp ${./translate/il/wasm-1.0.decls.lsp}
            touch $out
          '';

        # Determinism of the IL -> ACL2 step (wasm3 prep P2, W12): two fresh
        # translator runs agree with the checked-in translate/gen/wasm-<v>/
        # (`make -C translate check-gen SPEC=<v>`). Only 1.0 is checked in.
        translate-gen-wasm1 =
          let
            acl2 = self.packages.${pkgs.stdenv.hostPlatform.system}.acl2;
          in
          pkgs.runCommand "translate-gen-wasm1-check"
            {
              nativeBuildInputs = [
                acl2
                pkgs.perl
                pkgs.which
                pkgs.hostname
                pkgs.gnumake
              ];
            }
            ''
              export HOME=$TMPDIR/home
              mkdir -p $HOME
              export USER=nobody
              export ACL2_SYSTEM_BOOKS=${acl2}/share/acl2/books
              cp -R ${./translate} translate
              chmod -R u+w translate
              make -C translate check-gen SPEC=1.0 \
                ACL2=${acl2}/bin/acl2 CERT=${acl2}/share/acl2/books/build/cert.pl
              touch $out
            '';
      });

      devShells = forAllSystems (pkgs: {
        default = pkgs.mkShell {
          packages = [
            self.packages.${pkgs.stdenv.hostPlatform.system}.acl2
            pkgs.gnumake
            pkgs.perl
            pkgs.which
            pkgs.hostname
            # tests/oracle: WAT -> wasm, then run it under Node.
            pkgs.wabt
            pkgs.nodejs
            # plan/wasm3-demo: JSCL, Playwright (headless Chromium and Firefox
            # from nixpkgs, so nothing is downloaded at test time), pngquant for
            # the progress screenshots. wabt.js is reached through $WABT_JS.
            self.packages.${pkgs.stdenv.hostPlatform.system}.jscl
            pkgs.playwright-test
            pkgs.pngquant
          ];

          shellHook =
            let
              acl2 = self.packages.${pkgs.stdenv.hostPlatform.system}.acl2;
            in
            ''
              export ACL2=${acl2}/bin/acl2
              export ACL2_SYSTEM_BOOKS=${acl2}/share/acl2/books
              export CERT=${acl2}/share/acl2/books/build/cert.pl
              export ACL2_LISP=sbcl
              export JSCL_HOME=${self.packages.${pkgs.stdenv.hostPlatform.system}.jscl}/share/jscl
              export WABT_JS=${self.packages.${pkgs.stdenv.hostPlatform.system}.wabt-js}/lib/node_modules/wabt
              export PLAYWRIGHT_NODE_MODULES=${pkgs.playwright-test}/lib/node_modules
              export PLAYWRIGHT_BROWSERS_PATH=${pkgs.playwright-driver.browsers}
              export PLAYWRIGHT_SKIP_VALIDATE_HOST_REQUIREMENTS=true

              echo "wasm-acl2 dev shell"
              echo "  make all      certify top + proofs + tests"
              echo "  make top      certify just the library"
              echo "  make proofs / make tests"
              echo "  (cd tests/oracle && bash check-all.sh)   Node.js oracle"
            '';
        };
      });

      formatter = forAllSystems (pkgs: pkgs.nixfmt-tree);
    };
}
