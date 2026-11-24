---
title: "How to Cite & Licence"
prev: /Status/
src: content/Citing.md
plfaChapter: https://plfa.inf.ed.ac.uk/19.08/Citing/
---

## Licence

*Programming Language Foundations in Haskell* (PLFH) is licensed under the
[Creative Commons Attribution 4.0 International License (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/).
See [`LICENSE`](https://github.com/Tritlo/PLFH/blob/main/LICENSE) in the
repository for the complete legal text.

## Attribution to PLFA

PLFH is adapted from **edition `19.08`** of
[*Programming Language Foundations in Agda*](https://plfa.inf.ed.ac.uk/19.08/)
by Philip Wadler and Wen Kokke
([tagged source `v19.08`](https://github.com/plfa/plfa.github.io/tree/v19.08),
commit `63fcbbe25ec3686ff4c6df2c5b58a96b3a2054f3`),
which is licensed under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

All chapters adapted from PLFA carry an attribution banner linking to the
corresponding `v19.08` chapter and document the changes made in translation
to Dependent Haskell (`-XExperimentalDependentTypes` in
[`Tritlo/ghc`](https://github.com/Tritlo/ghc/tree/dependent-haskell)).

### Citing the original PLFA (`v19.08`)

#### Chicago

> Wadler, Philip and Wen Kokke.
> *Programming Language Foundations in Agda*.
> Edition 19.08.
> Available at `https://plfa.inf.ed.ac.uk/19.08/`.
> 2019.

#### BibTeX

```bibtex
@Book{plfa2019,
  author = {Philip Wadler and Wen Kokke},
  title  = {Programming Language Foundations in {A}gda},
  note   = {Edition 19.08, available at \url{https://plfa.inf.ed.ac.uk/19.08/}},
  year   = 2019,
}
```

### Citing PLFH

#### BibTeX

```bibtex
@Misc{plfh2026,
  title        = {Programming Language Foundations in {H}askell},
  howpublished = {\url{https://tritlo.github.io/PLFH/}},
  note         = {Adapted from Philip Wadler and Wen Kokke,
                  \emph{Programming Language Foundations in Agda} (v19.08, CC BY 4.0),
                  for Dependent Haskell in GHC},
  year         = 2026,
}
```

## Third-party assets

- **Iosevka** monospace font (loaded via `@fontsource/iosevka`):
  SIL Open Font License 1.1 (OFL-1.1).
- **Site styling**: Adapted from PLFA `v19.08` (CC BY 4.0) and Jekyll
  `minima` (MIT), compiled with [Hakyll](https://jaspervdj.be/hakyll/) (BSD-3-Clause).
