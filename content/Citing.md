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

PLFH is adapted from [*Programming Language Foundations in Agda*](https://plfa.inf.ed.ac.uk/)
under the [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) licence:

- **Parts 1 and core Part 2** (all 10 Part 1 chapters and the 7 published Part 2
  chapters `Lambda`, `Properties`, `DeBruijn`, `More`, `Bisimulation`,
  `Inference`, `Untyped`): adapted from **edition `19.08`**
  ([`plfa.inf.ed.ac.uk/19.08/`](https://plfa.inf.ed.ac.uk/19.08/),
  tagged source [`v19.08`](https://github.com/plfa/plfa.github.io/tree/v19.08),
  commit `63fcbbe25ec3686ff4c6df2c5b58a96b3a2054f3`) by **Philip Wadler and
  Wen Kokke**.
- **Extended Part 2 & Part 3** (`Confluence`, `BigStep`, `Substitution`, and
  Part 3 *Denotational Semantics* chapters `Denotational`, `Compositional`,
  `Soundness`, `Adequacy`, `ContextualEquivalence`): adapted from
  **edition `22.08`**
  ([`plfa.inf.ed.ac.uk/22.08/`](https://plfa.inf.ed.ac.uk/22.08/),
  tagged source [`v22.08`](https://github.com/plfa/plfa.github.io/tree/v22.08),
  commit `e2d545f3df0db4d4206c5448735665abde02d81f`) by **Philip Wadler,
  Wen Kokke, and Jeremy G. Siek** (note that draft versions of `BigStep`,
  `Substitution`, and `Confluence` already appeared in the `v19.08` repository
  tree before being published in the later table of contents).

All chapters adapted from PLFA carry an attribution banner linking to the
matching PLFA edition and chapter, and document the changes made in translation
to Dependent Haskell (`-XExperimentalDependentTypes` in
[`Tritlo/ghc`](https://github.com/Tritlo/ghc/tree/dependent-haskell)).

### Citing the original PLFA (`v19.08` & `v22.08`)

#### Chicago

> Wadler, Philip and Wen Kokke.
> *Programming Language Foundations in Agda*.
> Edition 19.08.
> Available at `https://plfa.inf.ed.ac.uk/19.08/`.
> 2019.
>
> Wadler, Philip, Wen Kokke, and Jeremy G. Siek.
> *Programming Language Foundations in Agda*.
> Edition 22.08.
> Available at `https://plfa.inf.ed.ac.uk/22.08/`.
> 2022.

#### BibTeX

```bibtex
@Book{plfa19.08,
  author = {Philip Wadler and Wen Kokke},
  title  = {Programming Language Foundations in {A}gda},
  note   = {Edition 19.08, available at \url{https://plfa.inf.ed.ac.uk/19.08/}},
  year   = 2019,
}

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
                  \emph{Programming Language Foundations in Agda} (v19.08 and v22.08, CC BY 4.0),
                  for Dependent Haskell in GHC},
  year         = 2026,
}
```

## Third-party assets

- **Iosevka** monospace font (loaded via `@fontsource/iosevka`):
  SIL Open Font License 1.1 (OFL-1.1).
- **Site styling**: Adapted from PLFA `v19.08` (CC BY 4.0) and Jekyll
  `minima` (MIT), compiled with [Hakyll](https://jaspervdj.be/hakyll/) (BSD-3-Clause).
