# JSCL (demo plan D2): the Common Lisp to JavaScript compiler, unmodified,
# bootstrapped with nixpkgs' SBCL.
#
# $out/share/jscl          the source tree (jscl-xc reads src/ from it)
#   dist/jscl.js           the JSCL runtime (node, browser, worker)
#   dist/jscl-node.js      node REPL / script runner
# $out/bin/jscl            node dist/jscl-node.js [file.lisp]
# $out/bin/jscl-xc         SBCL image with the cross compiler loaded and the
#                          bootstrap environment in place (saved right after
#                          `bootstrap`), so an application compiles without
#                          rebuilding JSCL. Usage:
#                            jscl-xc --non-interactive --load build.lisp
#                          where build.lisp calls
#                            (jscl-xc::compile-application FILES OUT ...)
{
  pkgs,
  src,
}:
pkgs.stdenv.mkDerivation {
  pname = "jscl";
  version = "0.9.0-alpha.0-${builtins.substring 0 7 src.rev}";
  inherit src;
  nativeBuildInputs = [
    pkgs.sbcl
    pkgs.nodejs
    pkgs.makeWrapper
  ];
  dontConfigure = true;
  buildPhase = ''
    runHook preBuild
    # jscl.lisp asks git for the commit (stored as *git-commit-hash* and
    # checked when a compiled file is loaded); there is no .git in the store.
    mkdir -p $TMPDIR/fakebin
    printf '#!/bin/sh\necho ${src.rev}\n' > $TMPDIR/fakebin/git
    chmod +x $TMPDIR/fakebin/git
    export PATH=$TMPDIR/fakebin:$PATH
    export SOURCE_DATE_EPOCH=${toString src.lastModified}
    export HOME=$TMPDIR

    # *base-directory* is captured when jscl.lisp is loaded, so build in the
    # final location.
    mkdir -p $out/share/jscl $out/bin $out/lib/jscl
    cp -R . $out/share/jscl
    chmod -R u+w $out/share/jscl
    cd $out/share/jscl
    sbcl --non-interactive \
      --eval '(load "jscl.lisp")' \
      --eval '(jscl-xc::%with-compilation-unit () (jscl-xc:bootstrap "dist/" "jscl") (jscl-xc:build-node-repl "dist/"))' \
      --eval '(sb-ext:save-lisp-and-die "'$out'/lib/jscl/jscl-xc.core" :executable nil)'
    runHook postBuild
  '';
  installPhase = ''
    runHook preInstall
    makeWrapper ${pkgs.nodejs}/bin/node $out/bin/jscl \
      --add-flags $out/share/jscl/dist/jscl-node.js
    makeWrapper ${pkgs.sbcl}/bin/sbcl $out/bin/jscl-xc \
      --add-flags "--core $out/lib/jscl/jscl-xc.core"
    runHook postInstall
  '';
  meta.description = "JSCL ${src.rev} with an SBCL-hosted cross compiler image";
}
