---
title: "How to Cite & Licence"
prev: /Status/
src: content/Citing.md
plfaChapter: https://plfa.inf.ed.ac.uk/22.08/Citing/
---

## Licence

*Programming Language Foundations in Haskell* (PLFH) is licensed under the
[Creative Commons Attribution 4.0 International License (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/).
See [`LICENSE`](https://github.com/Tritlo/PLFH/blob/main/LICENSE) in the
repository for the complete legal text.

## Attribution to PLFA

PLFH is adapted from **edition `22.08`** of
[*Programming Language Foundations in Agda*](https://plfa.inf.ed.ac.uk/22.08/)
by **Philip Wadler, Wen Kokke, and Jeremy G. Siek**
([tagged source `v22.08`](https://github.com/plfa/plfa.github.io/tree/v22.08),
commit `e2d545f3df0db4d4206c5448735665abde02d81f`),
which is licensed under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

All 25 adapted chapters across Parts 1, 2, and 3 carry an attribution banner
linking to the corresponding `v22.08` chapter and document the changes made in
translation to Dependent Haskell (`-XExperimentalDependentTypes` in
[`Tritlo/ghc`](https://github.com/Tritlo/ghc/tree/dependent-haskell)).

### Citing the original PLFA (`v22.08`)

#### Chicago

> Wadler, Philip, Wen Kokke, and Jeremy G. Siek.
> *Programming Language Foundations in Agda*.
> Edition 22.08.
> Available at `https://plfa.inf.ed.ac.uk/22.08/`.
> 2022.

#### BibTeX

```bibtex
@Book{plfa22.08,
  author = {Philip Wadler and Wen Kokke and Jeremy G. Siek},
  title  = {Programming Language Foundations in {A}gda},
  note   = {Edition 22.08, available at \url{https://plfa.inf.ed.ac.uk/22.08/}},
  year   = 2022,
}
```

### Citing PLFH

#### BibTeX

```bibtex
@Misc{plfh2026,
  title        = {Programming Language Foundations in {H}askell},
  howpublished = {\url{https://github.mpg.is/PLFH/}},
  note         = {Adapted from Philip Wadler, Wen Kokke, and Jeremy G. Siek,
                  \emph{Programming Language Foundations in Agda} (v22.08, CC BY 4.0),
                  for Dependent Haskell in GHC},
  year         = 2026,
}
```

## Third-party assets

- **Iosevka** monospace font (loaded via `@fontsource/iosevka`):
  SIL Open Font License 1.1 (OFL-1.1).
- **Site styling**: Adapted from PLFA `v22.08` (CC BY 4.0) and Jekyll
  `minima` (MIT), compiled with [Hakyll](https://jaspervdj.be/hakyll/) (BSD-3-Clause).
