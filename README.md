# Programming Language Foundations in Haskell (PLFH)

*Programming Language Foundations in Haskell* (PLFH) is an adaptation of
Philip Wadler, Wen Kokke, and Jeremy G. Siek's
[*Programming Language Foundations in Agda*](https://plfa.inf.ed.ac.uk/)
([`dev` branch](https://github.com/plfa/plfa.github.io/tree/dev), commit `c0885696578474ebcfe7bb3d7a592224567d9754`)
serving as both a readable textbook and a practical yardstick for the
experimental Dependent Haskell fork of GHC
([`TharkunAB/ghc`, branch `dependent-haskell`](https://github.com/TharkunAB/ghc/tree/dependent-haskell)).

- **Live book (GitHub Pages):** <https://plfh.tharkun.se/>
- **Copyright & Licence:** &copy; 2026 Tharkun AB — [Creative Commons Attribution 4.0 International (CC BY 4.0)](LICENSE)

## Repository layout

- `content/` — Literate Haskell Markdown chapters and front matter (`Preface`, `Setup`, `Status`, `Citing`).
- `hs/` — Standalone `.hs` modules and negative controls extracted from `content/` by `scripts/extract_and_sync.py`.
- `reproducers/` — Minimal standalone reproducers for Dependent Haskell compiler gaps and blockers.
- `scripts/extract_and_sync.py` — Extracts `hs/` from `content/` and optionally mirrors `hs/` and `reproducers/` into `ghc/docs/dependent-haskell/plfh/`.
- `scripts/check_plfh.sh` — Verifies all checked modules (`-dcore-lint -dstg-lint`), negative controls, and tracked reproducers.
- `site.hs`, `plfh-site.cabal`, `templates/`, `css/` — Hakyll static site generator (PLFA-inspired styling with Iosevka and no TeX).
- `shell.nix` — Nix development shell with GHC bootstrap tools and Hakyll prerequisites.

## Quick start

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

# Build and preview the Hakyll book locally
cabal run plfh-site -- watch
```

## Attribution

Adapted from Philip Wadler, Wen Kokke, and Jeremy G. Siek,
[*Programming Language Foundations in Agda*](https://plfa.inf.ed.ac.uk/)
(`dev` branch, commit `c0885696578474ebcfe7bb3d7a592224567d9754`),
licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
Every chapter notes all changes made in translation for Dependent Haskell.
