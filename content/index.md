---
title: "Table of Contents"
description: "Programming Language Foundations in Haskell (PLFH): a 25-chapter interactive textbook for Dependent Haskell in GHC, adapted from PLFA."
src: content/index.md
---

*Programming Language Foundations in Haskell* (PLFH) is an interactive
25-chapter textbook on programming language theory written in Dependent Haskell
(`-XDependentTypes` in GHC 10.1), adapted from Philip Wadler, Wen Kokke, and
Jeremy G. Siek's [*Programming Language Foundations in Agda*](https://plfa.inf.ed.ac.uk/)
([CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)). Every chapter
compiles and runs directly in your browser through WebAssembly.

- **New to Dependent Haskell?** Start with the [live feature walkthrough](/overview/).
- **Want to try code now?** Open the [Interactive Playground](/playground/).
- **Ready to read the book?** Begin with the [Preface](/preface/) or [Naturals](/naturals/).

Book feedback and pull requests are welcome on
[`TharkunAB/PLFH`](https://github.com/TharkunAB/PLFH). If you discover a
compiler bug or unexpected type-checker behavior, please
[file an issue on `TharkunAB/ghc`](https://github.com/TharkunAB/ghc/issues).

## Front matter

- [Dependent Haskell in GHC](/overview/): Live feature walkthrough (routes as values, runtime monad stacks, quantifiers, type-level expressions, plugins), GHC proposals, and papers
- [Interactive Playground](/playground/): Write, check, fill typed holes, and evaluate Dependent Haskell in your browser
- [Preface](/preface/): Propositions as Types, totality discipline, and differences from PLFA
- [Setup](/setup/): Building `TharkunAB/ghc`, companion packages, flags, and GHCi

## Part 1: Logical Foundations

- [Naturals](/naturals/): Natural numbers, arithmetic (`times`, `monus`, `pow`), and binary representation (`Bin`)
- [Induction](/induction/): Proof by induction (`+-assoc`, `+-identityʳ`, `+-suc`, `+-comm`, `cong`, `*-comm`, truncated subtraction, exponentiation, and `Bin` laws)
- [Relations](/relations/): Inductive relations (`_≤_`, `_<_`, trichotomy, `Even`/`Odd`, and the canonical binary bijection `Nat ≃ Can Bin`)
- [Equality](/equality/): Propositional equality, equational reasoning chains, substitution (`substP`), and Leibniz equality
- [Isomorphism](/isomorphism/): Isomorphism (`_≃_`), embedding (`_≲_`), and bi-implication (`_⇔_`)
- [Connectives](/connectives/): Conjunction, disjunction, truth, falsehood, commutative semiring isomorphisms, currying, distributivity, and exponential laws
- [Negation](/negation/): Intuitionistic negation, De Morgan laws, order negation, and classical equivalences (EM ⇔ DNE ⇔ Peirce ⇔ ImpOr ⇔ DeMorganNot)
- [Quantifiers](/quantifiers/): Universal and existential quantification (`Exists`, retained `Sigma` / `some`, and parity witnesses)
- [Decidable](/decidable/): Constructive decidability (`Dec`), `Reflects`, and decision procedures for equality, ordering, parity, and `Bin`
- [Lists](/lists/): Lists (`List a`), `(++)`, `map`, `foldr`, reversal (`shunt`/`rev`), `All`, `Any`, membership (`In`), and decidable list predicates

## Part 2: Programming Language Foundations

- [Lambda](/lambda/): Simply-typed lambda calculus syntax, values, substitution, reduction (`Step`/`Steps`), and typing
- [Properties](/properties/): Canonical forms, progress, determinism, preservation, verified evaluation, and well-typed terms do not get stuck
- [DeBruijn](/debruijn/): Intrinsically-typed terms, renaming, substitution, operational semantics, progress, and evaluation
- [Inference](/inference/): Sound and complete bidirectional type synthesis and checking (`Dec`) for STLC
- [Untyped](/untyped/): Well-scoped untyped lambda calculus, substitution, normal forms, Church numerals, and normal-order evaluation
- [More](/more/): Extended STLC (`let`, `Unit`, products, sums, `Void`, lists), reduction rules, and progress
- [Bisimulation](/bisimulation/): Relating `let` to `(λx. n) m` via lock-step simulation, substitution preservation, and multi-step bisimulation
- [Substitution](/substitution/): Constructive σ-calculus, pointwise σ-algebra laws, commutation, and Barendregt's substitution lemma
- [BigStep](/bigstep/): Call-by-name big-step semantics, environments and closures, determinism, divergence of `Ω`, and the bridge to small-step reduction
- [Confluence](/confluence/): Parallel reduction, the diamond property, the Strip Lemma, Church-Rosser confluence, and uniqueness of normal forms

## Part 3: Denotational Semantics

- [Denotational](/denotational/): Filter model (`Value`, subtyping `Sub`, environments, and denotations)
- [Compositional](/compositional/): Semantic lambda abstraction and application, contexts (`UCtx`/`plug`), and compositionality
- [Soundness](/soundness/): Weakening, strengthening, substitution, forward preservation, subject expansion, and soundness of β-reduction
- [Adequacy](/adequacy/): Logical relation (`logVLam`/`LogE`), the Fundamental Lemma, big-step and small-step adequacy, and divergence of `Ω`
- [ContextualEquivalence](/contextualequivalence/): Open-term contextual equivalence (`CtxEquiv`) and soundness of denotational equivalence

## Reference and backmatter

- [`dependent-base` Reference](/dependent-base/): Exported API (`Prelude.Dependent`, `Data.*.Dependent`) and GHCi tips
- [Source Browser](/source/): Syntax-highlighted `.hs` source for all 25 chapters and `dependent-base` modules
- [Chapter Coverage](/status/): Chapter-by-chapter mapping from PLFA to PLFH
- [How to Cite & License](/citing/): CC BY 4.0 license and attribution to upstream PLFA
