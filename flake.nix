{
  description = "WASM 1.0 ACL2 formalization — certified with ACL2 + the Kestrel community books";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs =
    { self, nixpkgs }:
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
      packages = forAllSystems (pkgs: rec {
        default = wasm-acl2;

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
      });

      checks = forAllSystems (pkgs: {
        inherit (self.packages.${pkgs.stdenv.hostPlatform.system}) wasm-acl2;
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
