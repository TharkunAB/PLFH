{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  name = "plfh-dev";

  buildInputs = with pkgs; [
    # Bootstrap toolchain for building Tritlo/ghc (dependent-haskell)
    # and for building the PLFH Hakyll static site.
    haskell.compiler.ghc912
    cabal-install
    haskellPackages.alex
    haskellPackages.happy

    # Build dependencies required by GHC's ./boot, ./configure, and Hadrian
    autoconf
    automake
    gnumake
    gcc
    binutils
    pkg-config
    python3
    git
    gmp
    gmp.dev
    ncurses
    ncurses.dev
    libffi
    libffi.dev
    zlib
    zlib.dev
  ];

  shellHook = ''
    echo "PLFH development shell ready."
    echo "  Stock GHC: $(ghc --version)"
    echo "  Cabal:     $(cabal --version | head -n 1)"
    echo ""
    echo "Quick commands:"
    echo "  1. Build Dependent Haskell GHC fork:"
    echo "       git clone --recursive -b dependent-haskell https://github.com/Tritlo/ghc.git"
    echo "       cd ghc && ./boot && ./configure && hadrian/build -j --flavour=quick --docs=none"
    echo "  2. Extract & verify PLFH chapters:"
    echo "       python3 scripts/extract_and_sync.py"
    echo "       PLFH_GHC=/path/to/ghc/_build/stage1/bin/ghc PLFH_GHC_REPO=/path/to/ghc PLFH_NO_PUEUE=1 bash scripts/check_plfh.sh"
    echo "  3. Build & preview the Hakyll book locally:"
    echo "       cabal run plfh-site -- watch"
  '';
}
