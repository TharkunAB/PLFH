---
title: "Table of Contents"
src: content/index.md
---

This book is an introduction to programming language theory using
**Dependent Haskell** (`-XExperimentalDependentTypes` in
[`Tritlo/ghc`, branch `dependent-haskell`](https://github.com/Tritlo/ghc/tree/dependent-haskell)),
adapted from Philip Wadler and Wen Kokke's
[*Programming Language Foundations in Agda*](https://plfa.inf.ed.ac.uk/19.08/)
(edition `19.08`, [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)).

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
- [Induction](/Induction/): Proof by induction (`+-assoc`, `+-comm`, `*-comm`, `Bin-laws`) <span class="badge badge-partial">Partial · R03/R13</span>
- [Relations](/Relations/): Inductive relations (`_≤_`, `_<_`, trichotomy, `Even`/`Odd`) <span class="badge badge-pass">Checked</span>
- [Equality](/Equality/): Equality, substitution, and Leibniz equality with `%U` and inline type lambdas <span class="badge badge-pass">Checked</span>
- [Isomorphism](/Isomorphism/): Logical equivalence (`_⇔_`) and dependent isomorphism (`_≃_`) boundaries <span class="badge badge-partial">Iff ✓ · Iso WIP</span>
- [Connectives](/Connectives/): Conjunction, disjunction, truth, falsehood, currying, distributivity <span class="badge badge-pass">Checked</span>
- [Negation](/Negation/): Intuitionistic negation, De Morgan, and classical equivalences (EM ⇔ DNE ⇔ Peirce) <span class="badge badge-pass">Checked</span>
- [Quantifiers](/Quantifiers/): Erased `Exists`, retained `Sigma` (`some`), and `Even` existential witness <span class="badge badge-pass">Checked</span>
- [Decidable](/Decidable/): Negation, decidable equality/ordering, and `Sigma` pairs <span class="badge badge-pass">Checked</span>
- [Lists](/Lists/): Prelude `(++)`, `map`, `HaskLib` length laws, `All`/`Any`/`In` <span class="badge badge-partial">Partial · R03/R13</span>

## Part 2: Programming Language Foundations

- [Lambda](/Lambda/): Simply-typed lambda calculus syntax, values, reduction, and typing <span class="badge badge-partial">Partial · R13/R16</span>
- [Properties](/Properties/): Canonical forms, **Progress** (checked!), context lemmas, **Preservation** (`[WIP]`) <span class="badge badge-partial">Progress ✓ · Preserve WIP</span>
- [DeBruijn](/DeBruijn/): Intrinsically-typed terms, renaming, substitution, promoted `Value`/`Step`, `progress` (`[WIP]`) <span class="badge badge-partial">Syntax/Promoted ✓ · Progress WIP</span>
- [Inference](/Inference/): **Certified STLC type inference & checking** (`infer`, `check`) returning `Term g a` <span class="badge badge-pass">Checked</span>
- [Untyped](/Untyped/): Well-scoped untyped lambda calculus, promoted `Neutral`/`Normal`/`BetaStep` <span class="badge badge-partial">Syntax/Promoted ✓ · Eval WIP</span>
- [More](/More/): Extended STLC (`let`, `Unit`, `Prod`, `Sum`, `Void`, `List`), promoted `Value`/`Step` <span class="badge badge-pass">Checked</span>
- [Bisimulation](/Bisimulation/): Relating reduction systems (`SimRel`, `Leg`, **R11 Core Lint bug** on `simValue`) <span class="badge badge-partial">Rel ✓ · R11 Core Lint</span>
- [BigStep](/BigStep/): Closure-based big-step semantics (`Env`, `Clos`, `EvalBig`) <span class="badge badge-partial">Relational ✓ · R13 lookupEnv</span>
- [Substitution](/Substitution/): σ-calculus simultaneous renaming & substitution combinators <span class="badge badge-partial">Algebra ✓ · Eqs WIP</span>
- [Confluence](/Confluence/): Parallel reduction, `parToBetas`, **Strip Lemma**, and **Confluence from Diamond**! <span class="badge badge-partial">Strip/Conf ✓ · Diamond WIP</span>

## Yardstick & Backmatter

- [Yardstick Status](/Status/): Full theorem-by-theorem ledger, HaskLib reuse, negative controls, and minimal compiler reproducers
- [How to Cite & Licence](/Citing/): CC BY 4.0 licence and attribution to PLFA `v19.08`
