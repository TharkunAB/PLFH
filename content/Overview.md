---
title: "Dependent Haskell: Overview, Papers & Roadmap"
prev: /
next: /Playground/
src: content/Overview.md
---

<div class="hero-actions">
  <a class="hero-btn hero-btn--primary" href="/Playground/">Try the Browser Playground</a>
  <a class="hero-btn" href="/">Read the Book (25 Chapters)</a>
  <a class="hero-btn" href="/HaskLib/">HaskLib Reference</a>
  <a class="hero-btn" href="/Source/">Browse Source</a>
  <a class="hero-btn" href="/Status/">Yardstick Status</a>
</div>

**Dependent Haskell** extends GHC with full-spectrum dependent types while
preserving Haskell's core engineering properties: type erasure by default,
type inference, separate compilation, and backward compatibility with existing
Haskell code.

This site hosts [*Programming Language Foundations in Haskell*](/) (PLFH), a
25-chapter interactive textbook and live compiler yardstick built against the
experimental [`Tritlo/ghc` (`dependent-haskell`)](https://github.com/Tritlo/ghc/tree/dependent-haskell)
fork—and compiled to `wasm32-wasi` so every proof, typed hole, and GHCi
expression runs directly in your browser.

## What Dependent Haskell adds to GHC

With `-XDependentTypes`, terms and types move toward a single unified language:

- **Ordinary Haskell functions in types:** Functions such as `plus`, `(++)`,
  `map`, `foldr`, and capture-avoiding substitution (`substSingle`) reduce in
  types without writing duplicate `type family` definitions or singleton
  boilerplate.
- **Explicit erasure vs. retention (`forall` vs. `foreach`):** Traditional
  `forall (x :: a).` remains strictly erased at runtime, while `foreach (x :: a) ->`
  (and `some (x :: a) |` for dependent pairs `Sigma`) retains a runtime value
  that can also appear in the result type.
- **Visible type arguments and Agda-style combinators:** Proposal `#281`
  (`RequiredTypeArguments`) and matchability polymorphism (`%M` / `%U`,
  Proposal `#242`) let us write `cong Succ`, `cong (plus m)`, and `cong (pow m)`
  with a single polymorphic `cong` and zero `@` sigils.
- **Type safety without forced totality:** Unlike Agda or Lean, Haskell permits
  non-termination and partiality. Dependent Haskell preserves System FC type
  soundness by checking value-carrying proofs explicitly (Weirich et al., ICFP
  2017) rather than assuming every term terminates.
- **Interactive Agda-mode via Typed Holes:** GHC's typed holes (`_`, `_qed`)
  and valid hole fits (Gissurarson, Haskell 2018) inspect goals and suggest
  proof terms directly in the [browser Playground](/Playground/) and on every
  chapter page.

```text
{-# LANGUAGE DependentTypes #-}

-- Ordinary Peano naturals + decimal literals (`FromNatural Nat`, `Num Nat`)
twoPlusThree :: plus 2 3 :~: 5
twoPlusThree = Refl

-- Structural induction via retained `foreach`
plusIdentityR :: foreach (m :: Nat) -> plus m Zero :~: m
plusIdentityR Zero     = Refl
plusIdentityR (Succ m) = cong Succ (plusIdentityR m)
```

Try editing this proof—or replacing `Refl` with a typed hole `_qed`—directly in
the [Interactive Playground](/Playground/).

## Design Authority & Roadmap

Compiler work on [`Tritlo/ghc` (`dependent-haskell`)](https://github.com/Tritlo/ghc/tree/dependent-haskell)
follows a strict four-tier specification hierarchy
([`docs/dependent-haskell/ROADMAP.md`](https://github.com/Tritlo/ghc/blob/dependent-haskell/docs/dependent-haskell/ROADMAP.md)):

1. **GHC Proposal `#378` (*Design for Dependent Types*)** takes precedence on
   syntax, extension bundling (`-XDependentTypes`), and quantifier design.
2. **Companion GHC Proposals** (`#281`, `#242`, `#370`, `#402`, `#425`, `#364`,
   `#509`, `#581`, `#765`) govern the building blocks delegated by `#378`.
3. **The Serokell Dependent Haskell Roadmap**
   ([`ghc.serokell.io/dh`](https://ghc.serokell.io/dh)) tracks the 50 feature
   cards and 67 prerequisite edges connecting stock GHC to full Dependent
   Haskell (23 cards inherited from upstream GHC, 4 additional cards completed
   on the fork, and 18 actively implemented and tested against PLFH).
4. **Agda and PLFA** inform surface ergonomics where GHC proposals are silent.

See the [Yardstick Status Ledger](/Status/) for the live chapter-by-chapter
tally, 48 fixed regression reproducers, and the remaining open compiler gaps.

## Key GHC Proposals

| Proposal | Title | Role in Dependent Haskell & PLFH |
| --- | --- | --- |
| [`#378`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html) | *Design for Dependent Types* | Overarching design blueprint: `-XDependentTypes` bundle, lexical scoping across terms & types, `foreach` / `forall` / `some` / `exists` / `∏` quantifiers |
| [`#281`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0281-visible-forall.html) | *Visible `forall` in types of terms* | `RequiredTypeArguments` (`forall a ->`), enabling visible `cong Succ`, `cong (plus m)`, and equational reasoning chains |
| [`#242`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0242-unsaturated-type-families.html) | *Unsaturated Type Families* | Matchable vs. unmatchable arrows (`%M` / `%U`), partial application of type-level functions, and higher-order predicates (`All`, `Any`, `LeibnizU`) |
| [`#370`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0370-modifiers.html) | *Syntax for Modifiers* | Generalized `%` modifier syntax supporting matchability and linearity annotations |
| [`#402`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0402-gadt-syntax.html) | *GADT Constructor Syntax* | Nested quantification and free ordering of `forall` groups and constraints in prefix GADT constructors |
| [`#425`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0425-decl-invis-binders.html) | *Invisible Binders in Type Declarations* | Arity inference and invisible binder scoping in type and data declarations |
| [`#364`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0364-unify-natural.html) | *Unify `Nat` and `Natural`* | Built-in `Natural` type literals paired with `FromNatural` (`2 + 3 :~: 5`) |
| [`#509`](https://github.com/ghc-proposals/ghc-proposals/pull/509) | *Type-Level Functions / Term Promotion* (draft) | Promoting ordinary functions across module interfaces for checked open/closed type-level evaluation |
| [`#581`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0581-namespace-specified-imports.html) & [`#765`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0765-pun-warnings.html) | *Namespace-Specified Imports* & *Pun Warnings* | Disambiguating term and type namespaces (`type (+)`) and diagnosing punning cleanly |

## Research Papers & Foundational Literature

- **Adam Gundry (2013).**
  *Type Inference, Haskell and Dependent Types.*
  PhD thesis, University of Strathclyde.
  First comprehensive elaboration and unification framework combining GHC's
  System FC with dependent types.
- **Richard A. Eisenberg (2016).**
  *Dependent Types in Haskell: Theory and Practice.*
  PhD dissertation, University of Pennsylvania
  ([`arXiv:1610.07978`](https://arxiv.org/abs/1610.07978)).
  Foundational architecture of Dependent Haskell (`Pico`, erasure vs.
  retention, matchability, and syntactic unification).
- **Stephanie Weirich, Antoine Voizard, Pedro Henrique Azevedo de Amorim, and Richard A. Eisenberg (ICFP 2017).**
  *A Specification for Dependent Types in Haskell.*
  Proceedings of the ACM on Programming Languages (PACMPL), 1(ICFP):31:1–31:29
  ([DOI `10.1145/3110275`](https://doi.org/10.1145/3110275)).
  Coq-mechanized soundness of a Curry-style surface language and Church-style
  dependent System FC core with non-termination and irrelevance.
- **Stephanie Weirich, Pritam Choudhury, Antoine Voizard, and Richard A. Eisenberg (ICFP 2019).**
  *A Role for Dependent Types in Haskell.*
  PACMPL, 3(ICFP):101:1–101:29
  ([DOI `10.1145/3341705`](https://doi.org/10.1145/3341705)).
  Integrates GHC's representational roles (zero-cost `coerce`) with dependent
  types, mechanized in Coq.
- **Csongor Kiss, Tony Field, Susan Eisenbach, and Simon Peyton Jones (ICFP 2019).**
  *Higher-Order Type-Level Programming in Haskell.*
  PACMPL, 3(ICFP):102:1–102:26
  ([DOI `10.1145/3341706`](https://doi.org/10.1145/3341706)).
  Introduces matchability polymorphism (`%M` / `%U`) and unsaturated type-level
  functions.
- **Matthías Páll Gissurarson (Haskell 2018).**
  *Suggesting Valid Hole Fits for Typed-Holes in Haskell.*
  Proceedings of the 11th ACM SIGPLAN International Symposium on Haskell,
  pp. 179–185
  ([DOI `10.1145/3242744.3242760`](https://doi.org/10.1145/3242744.3242760)).
  Valid hole fits and refinement-level hole fits in GHC—powering PLFH's
  in-browser Agda-mode typed-hole experience.
- **Philip Wadler, Wen Kokke, and Jeremy G. Siek.**
  *Programming Language Foundations in Agda*
  ([`plfa.inf.ed.ac.uk`](https://plfa.inf.ed.ac.uk/), CC BY 4.0).
  The upstream textbook adapted by PLFH across Parts 1–3 (Logical Foundations,
  Programming Language Foundations, and Denotational Semantics).

## Explore the Site

- **[Interactive Playground](/Playground/):** Write, typecheck, fill typed
  holes, and evaluate Dependent Haskell directly in your browser.
- **[Table of Contents](/):** Read all 25 chapters from Peano arithmetic and
  induction to intrinsically-typed STLC, Church–Rosser confluence, and
  denotational adequacy & contextual equivalence.
- **[HaskLib Reference](/HaskLib/) & [Source Browser](/Source/):** Inspect
  the precompiled `HaskLib` definitions, every extracted chapter `.hs` file,
  negative controls, and minimal compiler reproducers.
- **[Setup](/Setup/):** Build `Tritlo/ghc` locally or host your own Wasm GHCi
  bundle.
