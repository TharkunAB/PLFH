---
title: "Setup: Building Dependent Haskell GHC"
prev: /Preface/
next: /Naturals/
src: content/Setup.md
---

PLFH requires the experimental Dependent Haskell fork of GHC
([`Tritlo/ghc`](https://github.com/Tritlo/ghc/tree/dependent-haskell),
branch `dependent-haskell`, compiler version `10.1.20261115.1` and up),
which adds the Proposal `#378` `-XDependentTypes` umbrella extension and
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

## Essential flags for `-XDependentTypes`

Every Dependent Haskell proof module in PLFH begins with a single umbrella
pragma (following GHC Proposals `#378` and `#102`):

```haskell
{-# LANGUAGE DependentTypes #-}
```

When compiling modules containing native retained functions (`foreach`)
to object code or bytecode on this fork, pass:

```bash
ghc -O0 -fomit-interface-pragmas -fno-write-if-simplified-core \
    -dcore-lint -dstg-lint
```

- **`-XDependentTypes`** enables retained dependent binders (`foreach (m n p :: T) -> ...`,
  or `∏ (m n p :: T) -> ...` with `-XUnicodeSyntax`), open and closed
  evaluation of ordinary Haskell functions in types, automatic source-equation
  publication in `.hi` interfaces, type-level `let`/`case`/lambdas, and
  multi-binder `exists`/`some` syntax. It implies `GADTs`, `DataKinds`,
  `PolyKinds`, `TypeOperators`, `RankNTypes`, `ScopedTypeVariables`,
  `TypeApplications`, `TypeAbstractions`, `StandaloneKindSignatures`,
  `EmptyCase`, `Modifiers`, `RequiredTypeArguments`, `ExplicitNamespaces`,
  and **`NoListTuplePuns`** (per Proposal `#475`, so `[]`, `:`, and `[0, 1, 0]`
  work at the type level without leading `'` ticks; modules that write `(a, b)`
  or `()` in types simply add `ListTuplePuns` after `DependentTypes`).
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
ghci> :seti -XDependentTypes
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

To test root-domain URLs (matching [`https://plfh.tharkun.se/`](https://plfh.tharkun.se/), the default) or a subpath prefix (such as `/PLFH`):

```bash
PLFH_BASEURL="" cabal run plfh-site -- rebuild
PLFH_BASEURL=/PLFH cabal run plfh-site -- rebuild
```

## Interactive in-browser GHCi (WebAssembly)

Every chapter page includes an interactive Dependent Haskell bar and per-block
**Edit** / **Check in GHCi (Wasm)** controls powered by a client-side
`wasm32-wasi` Web Worker (`wasm/plfh-ghci-worker.mjs`) using GHC's WebAssembly
dynamic linker (`dyld.mjs`) and `browser_wasi_shim.mjs`.

- **Zero page-load cost:** The browser does not start the Web Worker or fetch
  `rootfs.tar.gz` until you click **Open Chapter GHCi** or **Check in GHCi**.
- **No `SharedArrayBuffer` required:** Streaming decompression uses the standard
  `DecompressionStream("gzip")` API, so the bundle works on plain static HTTPS
  hosts without custom COOP/COEP headers.
- **Persistent browser cache:** The worker caches the content-addressed bundle
  in the browser Cache API (`plfh-wasm-rootfs-v1`) and prunes superseded
  versions, so readers download the compiler bundle once across chapters and
  automatically receive updates when a new bundle ships.
- **Precompiled chapters:** The bundle ships `libplfh_ghci.so` alongside a
  precompiled `plfh-book-0.1` package (`HaskLib` and the checked `PLFH.*`
  modules), so individual edits, exercises, `:browse`, `:t`, `:k!`, and
  negative controls check directly against the chapter module.
- **Browser Agda-mode (typed holes & valid hole fits):** Write a typed hole
  such as `_` or `_qed` in any editable code block or in the chapter scratchpad
  and press `Ctrl/Cmd+Enter`. GHC reports the normalized goal type and valid
  hole fits, and the UI renders clickable fill chips that substitute the fit
  into the editor and re-check automatically. An opt-in **Refinement fits**
  toggle in the chapter bar enables `-frefinement-level-hole-fits=1` for
  multi-step refinement.

### Staging and hosting `rootfs.tar.gz`

Do not commit `rootfs.tar.gz` to Git (`.gitignore` excludes `wasm/*.tar.gz`).
Instead:

1. **Cloudflare R2 CDN (production on `plfh.tharkun.se`):** Run `./release.sh`
   from the repository root to upload a content-hashed
   `plfh/rootfs-<sha256-12>.tar.gz` to the `tharkun-cdn` R2 bucket
   (`https://cdn.tharkun.se/`), verify HTTPS reachability and CORS headers, and
   update the `PLFH_WASM_ROOTFS_URL` repository variable:

   ```bash
   ./release.sh /path/to/plfh-browser-bundle          # upload + update PLFH_WASM_ROOTFS_URL
   ./release.sh /path/to/plfh-browser-bundle --deploy # also trigger GitHub Pages rebuild
   ```

2. **Local preview:** Stage a built `plfh-browser-bundle/` into `wasm/` and run
   Hakyll locally (or pass `?rootfs=https://...` in the page URL):

   ```bash
   bash scripts/stage_wasm_bundle.sh /path/to/plfh-browser-bundle
   cabal run plfh-site -- watch
   ```

3. **GitHub Pages fallback:** When `PLFH_WASM_ROOTFS_URL` is unset,
   `.github/workflows/pages.yml` falls back to downloading `rootfs.tar.gz` from
   the `wasm-latest` GitHub Release (`bash scripts/stage_wasm_bundle.sh --publish-release`)
   into `_site/wasm/rootfs.tar.gz`.
