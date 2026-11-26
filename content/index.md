---
title: "Table of Contents"
src: content/index.md
---

This book is an introduction to programming language theory using
**Dependent Haskell** (`-XDependentTypes` in
[`TharkunAB/ghc`, branch `dependent-haskell`](https://github.com/TharkunAB/ghc/tree/dependent-haskell)),
adapted from Philip Wadler, Wen Kokke, and Jeremy G. Siek's
[*Programming Language Foundations in Agda*](https://plfa.inf.ed.ac.uk/)
([`dev` branch](https://github.com/plfa/plfa.github.io/tree/dev), commit `c088569657`,
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)).

Every plain Haskell code block in this book is extracted into a standalone
`.hs` module and verified with GHC's Core Lint and STG Lint; see
[Verification & Coverage](/Status/) for the module ledger and negative controls.

Comments, bug reports, and pull requests are welcome on
[GitHub](https://github.com/TharkunAB/PLFH).

## Front matter

- [Dependent Haskell Overview](/Overview/): Core concepts, GHC proposals (`#378`, `#281`, `#242`, ...), foundational papers, and the Serokell roadmap
- [Roadmap Showcase](/Showcase/): Self-contained runnable cards for Dependent Haskell features (live WebAssembly GHC)
- [Interactive Playground](/Playground/): Try Dependent Haskell, typed-hole refinement, and GHCi directly in your browser (WebAssembly)
- [Preface](/Preface/): Propositions as Types, totality discipline, and differences from PLFA
- [Setup](/Setup/): Compiling `TharkunAB/ghc`, `shell.nix`, flags, GHCi, and Hakyll preview

## Part 1: Logical Foundations

- [Naturals](/Naturals/): Natural numbers, arithmetic (`times`, `monus`, `pow`), and binary representation (`Bin`)
- [Induction](/Induction/): Proof by induction (`+-assoc`, `+-comm`, `cong`, `*-comm`, truncated subtraction, exponentiation, and `Bin` laws)
- [Relations](/Relations/): Inductive relations (`_≤_`, `_<_`, trichotomy, `Even`/`Odd`, and the canonical binary bijection `Nat ≃ Can Bin`)
- [Equality](/Equality/): Propositional equality, equational reasoning chains, substitution (`substP`), and Leibniz equality
- [Isomorphism](/Isomorphism/): Isomorphism (`_≃_`), embedding (`_≲_`), and bi-implication (`_⇔_`)
- [Connectives](/Connectives/): Conjunction, disjunction, truth, falsehood, commutative semiring isomorphisms, currying, distributivity, and exponential laws
- [Negation](/Negation/): Intuitionistic negation, De Morgan laws, order negation, and classical equivalences (EM ⇔ DNE ⇔ Peirce ⇔ ImpOr ⇔ DeMorganNot)
- [Quantifiers](/Quantifiers/): Universal and existential quantification (`Exists`, retained `Sigma` / `some`, and parity witnesses)
- [Decidable](/Decidable/): Constructive decidability (`Dec`), `Reflects`, and decision procedures for equality, ordering, parity, and `Bin`
- [Lists](/Lists/): Lists (`List a`), `(++)`, `map`, `foldr`, reversal (`shunt`/`rev`), `All`, `Any`, membership (`In`), and decidable list predicates

## Part 2: Programming Language Foundations

- [Lambda](/Lambda/): Simply-typed lambda calculus syntax, values, substitution, reduction (`Step`/`Steps`), and typing
- [Properties](/Properties/): Canonical forms, progress, determinism, preservation, verified evaluation, and well-typed terms do not get stuck
- [DeBruijn](/DeBruijn/): Intrinsically-typed terms, renaming, substitution, operational semantics, progress, and evaluation
- [Inference](/Inference/): Sound and complete bidirectional type synthesis and checking (`Dec`) for STLC
- [Untyped](/Untyped/): Well-scoped untyped lambda calculus, substitution, normal forms, Church numerals, and normal-order evaluation
- [More](/More/): Extended STLC (`let`, `Unit`, products, sums, `Void`, lists), reduction rules, and progress
- [Bisimulation](/Bisimulation/): Relating `let` to `(λx. n) m` via lock-step simulation, substitution preservation, and multi-step bisimulation
- [BigStep](/BigStep/): Call-by-name big-step semantics, environments and closures, determinism, divergence of `Ω`, and the bridge to small-step reduction
- [Substitution](/Substitution/): Constructive σ-calculus, pointwise σ-algebra laws, commutation, and Barendregt's substitution lemma
- [Confluence](/Confluence/): Parallel reduction, the diamond property, the Strip Lemma, Church–Rosser confluence, and uniqueness of normal forms

## Part 3: Denotational Semantics

- [Denotational](/Denotational/): Filter model (`Value`, subtyping `Sub`, environments, and denotations)
- [Compositional](/Compositional/): Semantic lambda abstraction and application, contexts (`UCtx`/`plug`), and compositionality
- [Soundness](/Soundness/): Weakening, strengthening, substitution, forward preservation, subject expansion, and soundness of β-reduction
- [Adequacy](/Adequacy/): Logical relation (`logVLam`/`LogE`), the Fundamental Lemma, big-step and small-step adequacy, and divergence of `Ω`
- [ContextualEquivalence](/ContextualEquivalence/): Open-term contextual equivalence (`CtxEquiv`) and soundness of denotational equivalence

## Reference & Backmatter

- [`dependent-base` Reference](/DependentBase/): Exported API (`Prelude.Dependent`, `Data.*.Dependent`), GHCi tips, and module sources
- [Source Browser](/Source/): Syntax-highlighted `.hs` source for all chapters, library modules, negative controls, and runtime tests
- [Verification & Coverage](/Status/): Chapter-by-chapter theorem ledger and negative controls
- [How to Cite & Licence](/Citing/): CC BY 4.0 licence and attribution to upstream PLFA
