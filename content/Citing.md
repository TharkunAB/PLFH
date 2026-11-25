---
title: "How to Cite & Licence"
prev: /Status/
src: content/Citing.md
plfaChapter: https://plfa.inf.ed.ac.uk/Citing/
---

## Licence

*Programming Language Foundations in Haskell* (PLFH) is licensed under the
[Creative Commons Attribution 4.0 International License (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/).
See [`LICENSE`](https://github.com/TharkunAB/PLFH/blob/main/LICENSE) in the
repository for the complete legal text.

## Attribution to PLFA

PLFH is adapted from the latest upstream
[*Programming Language Foundations in Agda*](https://plfa.inf.ed.ac.uk/)
by **Philip Wadler, Wen Kokke, and Jeremy G. Siek**
([`plfa/plfa.github.io`, `dev` branch](https://github.com/plfa/plfa.github.io/tree/dev),
synced against commit `c0885696578474ebcfe7bb3d7a592224567d9754`),
which is licensed under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

All 25 adapted chapters across Parts 1, 2, and 3 carry an attribution banner
linking to the corresponding upstream PLFA chapter and document the changes
made in translation to Dependent Haskell (`-XDependentTypes` in
[`TharkunAB/ghc`](https://github.com/TharkunAB/ghc/tree/dependent-haskell)).

### Citing the original PLFA

#### Chicago

> Wadler, Philip, Wen Kokke, and Jeremy G. Siek.
> *Programming Language Foundations in Agda*.
> Available at `https://plfa.inf.ed.ac.uk/`.

#### BibTeX

```bibtex
@Book{plfa,
  author = {Philip Wadler and Wen Kokke and Jeremy G. Siek},
  title  = {Programming Language Foundations in {A}gda},
  note   = {Available at \url{https://plfa.inf.ed.ac.uk/}},
}
```

### Citing PLFH

#### BibTeX

```bibtex
@Misc{plfh2026,
  title        = {Programming Language Foundations in {H}askell},
  howpublished = {\url{https://plfh.tharkun.se/}},
  note         = {Adapted from Philip Wadler, Wen Kokke, and Jeremy G. Siek,
                  \emph{Programming Language Foundations in Agda} (CC BY 4.0),
                  for Dependent Haskell in GHC},
  year         = 2026,
}
```

## Third-party assets

- **Iosevka** monospace font (loaded via `@fontsource/iosevka`):
  SIL Open Font License 1.1 (OFL-1.1).
- **Site styling**: Adapted from PLFA (CC BY 4.0) and Jekyll
  `minima` (MIT), compiled with [Hakyll](https://jaspervdj.be/hakyll/) (BSD-3-Clause).
