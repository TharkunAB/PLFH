---
title: "Setup: Building Dependent Haskell GHC"
prev: /Preface/
next: /Naturals/
src: content/Setup.md
---

PLFH requires the experimental Dependent Haskell fork of GHC
([`Tritlo/ghc`](https://github.com/Tritlo/ghc/tree/dependent-haskell),
branch `dependent-haskell`, compiler version `10.1.20261115.1` and up),
which adds the `-XExperimentalDependentTypes` language extension and
native dependent Core support.

## Quick start with Nix (`shell.nix`)

If you use Nix, the repository includes a [`shell.nix`](https://github.com/Tritlo/PLFH/blob/main/shell.nix)
that provides all bootstrap tools required both to build the GHC fork
(GHC, Cabal, Alex, Happy, Autoconf, GCC, GMP, libffi, ncurses, Python 3)
and to build this book with Hakyll:

```bash
git clone https://github.com/Tritlo/PLFH.git
cd PLFH
nix-shell
```

Without Nix, install:

- A bootstrap GHC (`>= 9.12`, e.g., `9.14.1` via `ghcup`), `cabal-install` (`>= 3.14`),
  `alex`, and `happy`
- Standard GHC build dependencies: `autoconf`, `automake`, `make`, `gcc`, `gmp`, `libffi`, `ncurses`, `python3`, `git`

## Compiling the Dependent Haskell GHC fork

Clone the `dependent-haskell` branch **with its Git submodules**, then
configure and build with Hadrian:

```bash
git clone --recursive -b dependent-haskell https://github.com/Tritlo/ghc.git
cd ghc
./boot
./configure
hadrian/build -j --flavour=quick --docs=none
```

When Hadrian finishes:

- The stage-1 compiler lives at `_build/stage0/bin/ghc`.
- The self-hosted stage-2 compiler lives at `_build/stage1/bin/ghc`
  (with its matching libraries in `_build/stage1/lib`).

Verify the build and record its Git commit ID:

```bash
_build/stage1/bin/ghc --version
_build/stage1/bin/ghc --info | grep 'Project Git commit id'
```

You can also run the fork's built-in showcase to confirm native execution
and GHCi work end to end:

```bash
bash docs/dependent-haskell/check-showcase.sh _build/stage1/bin/ghc _build/stage1/lib --ghci
```

## Essential flags for `-XExperimentalDependentTypes`

Every Dependent Haskell proof module in PLFH enables:

```haskell
{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
```

When compiling modules containing native retained functions (`foreach`)
to object code or bytecode on this fork, pass:

```bash
ghc -O0 -fomit-interface-pragmas -fno-write-if-simplified-core \
    -dcore-lint -dstg-lint
```

- **`-XExperimentalDependentTypes`** enables `foreach (x :: T) -> ...`
  retained dependent binders, open/closed evaluation of ordinary Haskell
  functions in types, type-level `let`/`case`/lambdas, and `exists`/`some`
  syntax. (It implies `RequiredTypeArguments`.)
- **`-fwrite-source-equations`** (optional when compiling an ordinary
  non-dependent module) records a function's defining equations in its
  interface so downstream Dependent Haskell modules can reduce calls to it
  on unknown inputs.
- **`-O0 -fomit-interface-pragmas -fno-write-if-simplified-core`** selects
  the checked native dependent Core pipeline.

## Trying Dependent Haskell in GHCi

You can experiment interactively with the stage-2 compiler:

```bash
_build/stage1/bin/ghc --interactive \
  -fbyte-code -O0 -fomit-interface-pragmas -fno-write-if-simplified-core \
  -package-env - -i \
  -idocs/dependent-haskell/hasklib \
  -idocs/dependent-haskell/examples/open-evaluation \
  -i/path/to/PLFH/hs
```

At the prompt:

```text
ghci> :seti -XExperimentalDependentTypes -XDataKinds -XTypeOperators
ghci> :load PLFH.Part1.Induction
ghci> :t plusAssoc
```

## Extracting and verifying PLFH locally

From the root of the `PLFH` repository:

```bash
# 1. Extract standalone .hs modules and negative controls from content/**/*.md
python3 scripts/extract_and_sync.py

# 2. Check all modules, negative controls, and tracked reproducers
PLFH_GHC=/path/to/ghc/_build/stage1/bin/ghc \
PLFH_GHC_REPO=/path/to/ghc \
PLFH_NO_PUEUE=1 \
bash scripts/check_plfh.sh
```

Every checked chapter is compiled with `-dcore-lint -dstg-lint`, every
negative control must fail with its expected GHC diagnostic code, and the
script audits `hs/PLFH/` to reject `undefined`, `unsafeCoerce`, or
`-fdefer-type-errors`.

## Building this book locally with Hakyll

The book website is built with [Hakyll](https://jaspervdj.be/hakyll/) using
stock GHC (e.g., GHC `9.12.2` from `shell.nix` or `ghcup`):

```bash
cabal build plfh-site
cabal run plfh-site -- build
cabal run plfh-site -- watch   # local live preview at http://localhost:8000
```

To test the exact GitHub Pages project-site URLs (`/PLFH/...`):

```bash
PLFH_BASEURL=/PLFH cabal run plfh-site -- rebuild
```

## Note on in-browser compilation (WebAssembly)

<div class="wip-notice">
<strong>[WIP NOTICE — In-browser compilation]</strong>
Being able to edit and typecheck PLFH exercises directly in the browser is a
long-term stretch goal, not yet implemented. Two technical details matter on
the current GHC fork:
<ol>
  <li>GHC's JavaScript backend (<code>ArchJavaScript</code>) is currently
      gated off for native dependent Core in
      <code>GHC.Driver.Main.Hsc.checkNativeDependentModule</code>, and
      compiling Haskell <em>to</em> JS does not itself put the typechecker
      in the browser.</li>
  <li>Running the GHC typechecker client-side in a browser requires
      cross-compiling this GHC fork to <strong>WebAssembly
      (<code>wasm32-wasi</code>)</strong> (browser GHCi / <code>ghc-wasm</code>
      mode). While <code>ArchWasm32</code> is not explicitly gated off like
      <code>ArchJavaScript</code>, building a wasm32 stage-2 fork has not
      yet been attempted and is tracked separately from the core book proofs.</li>
</ol>
</div>
