---
title: "Table of Contents"
src: content/index.md
---

This book is an introduction to programming language theory using
**Dependent Haskell** (`-XExperimentalDependentTypes` in
[`Tritlo/ghc`, branch `dependent-haskell`](https://github.com/Tritlo/ghc/tree/dependent-haskell)),
adapted from Philip Wadler, Wen Kokke, and Jeremy G. Siek's
[*Programming Language Foundations in Agda*](https://plfa.inf.ed.ac.uk/)
([`dev` branch](https://github.com/plfa/plfa.github.io/tree/dev), commit `c088569657`,
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)).

Every plain Haskell code block in this book is extracted into a standalone
`.hs` module and checked with GHC's Core Lint and STG Lint. Where Dependent
Haskell cannot yet express a PLFA theorem directly without workarounds,
we mark it with a **[WIP NOTICE]** and publish a minimal reproducer for the
compiler team.

Comments, bug reports, and pull requests are welcome on
[GitHub](https://github.com/Tritlo/PLFH).

## Front matter

- [Preface](/Preface/): Propositions as Types, totality discipline, and yardstick goals
- [Setup](/Setup/): Compiling `Tritlo/ghc`, `shell.nix`, flags, GHCi, and Hakyll preview

## Part 1: Logical Foundations

- [Naturals](/Naturals/): Natural numbers, `times`, `pow`, `monus`, `Bin` <span class="badge badge-partial">Partial · R13/R16</span>
- [Induction](/Induction/): Proof by induction (`+-assoc`, `HaskLib.rewrite`, `+-comm`, `cong`/`+-rearrange`, `+-swap`, `*-comm`, **`0∸n≡0`**, **`∸-+-assoc`**, `Bin-laws`) <span class="badge badge-partial">Partial · pow WIP</span>
- [Relations](/Relations/): Inductive relations (`_≤_`, `_<_`, trichotomy, `DiffWitness`, `Even`/`Odd`, canonical `One`/`Can` bijection) <span class="badge badge-pass">Checked</span>
- [Equality](/Equality/): Equality, `RequiredTypeArguments` chains, `substP @Even`, and Leibniz equality with `%U` and inline type lambdas <span class="badge badge-pass">Checked</span>
- [Isomorphism](/Isomorphism/): Logical equivalence (`_⇔_`), monomorphic `IsoSize` (`isoSizeRefl`/`isoSizeSym`), and polymorphic `_≃_` boundary <span class="badge badge-partial">Iff/IsoSize ✓ · Poly Iso WIP</span>
- [Connectives](/Connectives/): Conjunction, disjunction, truth, falsehood, currying, distributivity, exponential laws <span class="badge badge-pass">Checked</span>
- [Negation](/Negation/): Intuitionistic negation, De Morgan, order-negation laws, and classical equivalences (EM ⇔ DNE ⇔ Peirce) <span class="badge badge-pass">Checked</span>
- [Quantifiers](/Quantifiers/): Erased `Exists`, retained `Sigma` (`some`), and `Even`/`Odd` existential witnesses <span class="badge badge-pass">Checked</span>
- [Decidable](/Decidable/): Negation, decidable equality/ordering/parity/`Bin`, `Reflects`, and inline `Sigma` (`plusExists`) <span class="badge badge-pass">Checked</span>
- [Lists](/Lists/): Prelude `(++)`, `map`, `HaskLib` length laws, `shunt`, `downFrom`, `All`/`Any`/`In`, `decAll`/`decAny` <span class="badge badge-partial">Partial · R03/R13</span>

## Part 2: Programming Language Foundations

- [Lambda](/Lambda/): Simply-typed lambda calculus syntax, values, same-module `substTerm`, reduction (`Step`/`Steps`), and typing <span class="badge badge-pass">Checked</span>
- [Properties](/Properties/): Canonical forms, **Progress**, context lemmas, **Substitution Lemma**, and **8-constructor Preservation** <span class="badge badge-pass">Checked</span>
- [DeBruijn](/DeBruijn/): Intrinsically-typed terms, renaming, substitution, promoted `Value`, functional `Step`/`progress` (`[WIP]`) <span class="badge badge-partial">Syntax/Subst ✓ · Step/Progress WIP</span>
- [Inference](/Inference/): **Certified STLC type inference & checking** (`infer`, `check`) with inline GADT refinement returning `Term g a` <span class="badge badge-pass">Checked</span>
- [Untyped](/Untyped/): Well-scoped untyped lambda calculus, sound relational `SubstAtU`, promoted `Neutral`/`Normal`/`BetaStep` <span class="badge badge-partial">Syntax/Beta ✓ · Eval WIP</span>
- [More](/More/): Extended STLC (`let`, `Unit`, `Prod`, `Sum`, `Void`, `List`), `substSingle`/`substDouble`, promoted `Value` <span class="badge badge-partial">Syntax/Subst ✓ · Step WIP</span>
- [Bisimulation](/Bisimulation/): Relating reduction systems (`SimRel`, `Leg`, full checked **`simValue`**) <span class="badge badge-partial">simValue ✓ · sim WIP</span>
- [BigStep](/BigStep/): Call-by-name big-step semantics (`Env`, `Clos`, `EvalBig`, **`evalDeterm`**, `(λx y. x) Ω`) <span class="badge badge-partial">Determ ✓ · R13 lookupEnv</span>
- [Substitution](/Substitution/): σ-calculus simultaneous renaming & substitution combinators <span class="badge badge-partial">Algebra ✓ · Eqs WIP</span>
- [Confluence](/Confluence/): Parallel reduction, `parToBetas`, **Strip Lemma**, **Par Confluence**, and **Church-Rosser** <span class="badge badge-partial">CR ✓ · Diamond WIP</span>

## Part 3: Denotational Semantics

- [Denotational](/Denotational/): Filter model (GADT `Value`, `Sub`, `dom`/`cod`, nested `subInvDist`, **`subInv`**, **`arrSubArrInv`**, `Denotes`, `envSubMono`) <span class="badge badge-pass">Checked</span>
- [Compositional](/Compositional/): Semantic curry & application (**`lamEquiv`/`lamCong`**, **`appEquiv`/`appCong`**), `UCtx`/`plug` <span class="badge badge-partial">Lam &amp; App ✓ · Plug WIP</span>
- [Soundness](/Soundness/): Forward preservation (**`denotPreserve`**) & backward expansion (**`denotReflect`**, **`denotEquivSteps`**) <span class="badge badge-partial">Pres/Refl ✓ · Subst WIP</span>
- [Adequacy](/Adequacy/): **`decAboveFun`**, `LogVLam`/`LogE`, full **`subLogVLam`**, full **`fundamental`**, and **unconditional `adequacyBigStep`** <span class="badge badge-pass">Big-Step ✓</span>
- [ContextualEquivalence](/ContextualEquivalence/): Deriving contextual equivalence (`Terminates`, `denotEqualCtxEquivFromSoundness`) <span class="badge badge-partial">Reduction ✓ · Premises WIP</span>

## Yardstick & Backmatter

- [Yardstick Status](/Status/): Full theorem-by-theorem ledger, HaskLib reuse, negative controls, and minimal compiler reproducers
- [How to Cite & Licence](/Citing/): CC BY 4.0 licence and attribution to upstream PLFA
