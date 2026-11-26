# Programming Language Foundations in Haskell (PLFH)

*Programming Language Foundations in Haskell* (PLFH) adapts Philip Wadler, Wen
Kokke, and Jeremy G. Siek's
[*Programming Language Foundations in Agda*](https://plfa.inf.ed.ac.uk/)
([`dev` branch](https://github.com/plfa/plfa.github.io/tree/dev), commit
`c0885696578474ebcfe7bb3d7a592224567d9754`) for the Dependent Haskell fork of
GHC ([`TharkunAB/ghc`, branch `dependent-haskell`](https://github.com/TharkunAB/ghc/tree/dependent-haskell)).

- Live site: <https://plfh.tharkun.se/>
- Dependent Haskell overview & walkthrough: <https://plfh.tharkun.se/Overview/>
- Companion repositories:
  [`TharkunAB/ghc`](https://github.com/TharkunAB/ghc/tree/dependent-haskell),
  [`TharkunAB/dependent-base`](https://github.com/TharkunAB/dependent-base),
  [`TharkunAB/dependent-proof-search`](https://github.com/TharkunAB/dependent-proof-search),
  [`TharkunAB/dependent-obs-eq`](https://github.com/TharkunAB/dependent-obs-eq)
- License: &copy; 2026 Tharkun AB, [Creative Commons Attribution 4.0 International (CC BY 4.0)](LICENSE)

## Repository layout

- `content/`: Literate Haskell Markdown chapters and front matter (`Overview`, `Playground`, `Preface`, `Setup`, `DependentBase`, `Status`, `Citing`).
- `hs/`: Extracted `.hs` modules and negative controls generated from `content/` by `scripts/extract_and_sync.py`.
- `scripts/extract_and_sync.py`: Extracts `hs/` from `content/` and snapshots `reference/dependent-base/`.
- `scripts/check_plfh.sh`: Verifies all chapters (`-dcore-lint -dstg-lint`), `.hi` interface soundness, negative controls, and runtime smoke tests.
- `site.hs`, `plfh-site.cabal`, `templates/`, `css/`, `wasm/`: Hakyll static site generator and browser WebAssembly GHCi client.
- `release.sh`: Uploads content-addressed `rootfs-<sha256-12>.tar.gz` bundles to Cloudflare R2 and updates `PLFH_WASM_ROOTFS_URL`.
- `shell.nix`: Nix shell with GHC bootstrap tools and Hakyll prerequisites.

## Maintainer commands

```bash
# Enter Nix shell (optional)
nix-shell

# Extract Haskell modules from literate Markdown chapters
python3 scripts/extract_and_sync.py

# Verify proofs with the Dependent Haskell GHC fork
PLFH_GHC=/path/to/ghc/_build/stage1/bin/ghc \
PLFH_GHC_REPO=/path/to/ghc \
PLFH_NO_PUEUE=1 \
bash scripts/check_plfh.sh

# Build and preview the Hakyll site locally
cabal run plfh-site -- watch

# Upload a built wasm32-wasi bundle to R2 and update PLFH_WASM_ROOTFS_URL
./release.sh /path/to/plfh-browser-bundle
```

## Attribution

Adapted from Philip Wadler, Wen Kokke, and Jeremy G. Siek,
[*Programming Language Foundations in Agda*](https://plfa.inf.ed.ac.uk/)
(`dev` branch, commit `c0885696578474ebcfe7bb3d7a592224567d9754`),
licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
Every chapter notes changes made in translation for Dependent Haskell.
