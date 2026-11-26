---
title: "Preface"
prev: /
next: /Setup/
src: content/Preface.md
plfaChapter: https://plfa.inf.ed.ac.uk/Preface/
---

The most profound connection between logic and computation is a pun.
The doctrine of *Propositions as Types* asserts that a certain kind of
formal structure may be read in two ways: either as a proposition in
logic or as a type in computing. Further, a related structure may be
read as either the proof of the proposition or as a program of the
corresponding type. Further still, simplification of proofs
corresponds to evaluation of programs.

Accordingly, the title of this book also has two readings. It may be
parsed as "(Programming Language) Foundations in Haskell" or "Programming
(Language Foundations) in Haskell" — the specifications we write in
Dependent Haskell both describe programming languages and are
themselves Haskell programs compiled by GHC.

This book is an adaptation of Philip Wadler, Wen Kokke, and Jeremy G. Siek's
[*Programming Language Foundations in Agda*](https://plfa.inf.ed.ac.uk/)
([`dev` branch](https://github.com/plfa/plfa.github.io/tree/dev), commit
`c0885696578474ebcfe7bb3d7a592224567d9754`,
licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)).
It serves a dual purpose:

1. **A readable introduction** to programming language theory and formal
   proofs in Dependent Haskell, following PLFA's structure and prose closely.
2. **An end-to-end test suite** for the Dependent Haskell branch of GHC
   ([`TharkunAB/ghc`, branch `dependent-haskell`](https://github.com/TharkunAB/ghc/tree/dependent-haskell)).
   Every definition and theorem in PLFA (Parts 1, 2, and 3) is stated and
   proved directly using `-XDependentTypes`.

## How this book differs from PLFA

Because Haskell is a general-purpose lazy functional programming language,
several differences from Agda are called out explicitly throughout the text:

- **Totality and partiality.** Agda enforces termination and positivity
  checks so that every well-typed term denotes a total value; without
  totality, a non-terminating loop or `undefined` could inhabit any type,
  including a false proposition. GHC does not enforce totality by default
  (though `-freport-totality` provides opt-in advisory checks). Every checked
  proof in PLFH is therefore written by structural recursion on finite
  inductive inputs, with **no** typed holes, **no** `-fdefer-type-errors`,
  **no** `undefined` or `error`, **no** circular proof bindings, and **no**
  `unsafeCoerce`. Whenever an Agda proof relies on totality or function
  extensionality, we note that explicitly.
- **Direct Dependent Haskell.** Rather than encoding dependent types with
  singletons or manual `type family` duplicates, theorems in PLFH are written
  directly over ordinary Haskell functions and datatypes with
  `-XDependentTypes`. See [Verification & Coverage](/Status/) for the
  chapter-by-chapter theorem ledger and negative controls.
- **Library reuse.** PLFH reuses standard indexed datatypes and arithmetic or
  list-length laws from the companion library rather than duplicating global
  `Nat` instances across chapters.
- **Literate Haskell Markdown.** Every chapter in PLFH is a literate
  Markdown file. Plain ```` ```haskell ```` blocks are extracted into
  standalone `.hs` modules and checked by the Dependent Haskell GHC fork
  with `-dcore-lint -dstg-lint`. Dashed blocks mark exercises or
  expected-failure negative controls.

## A word on the exercises

Following PLFA:

- Exercises labelled **(recommended)** cover the core material.
- Exercises labelled **(stretch)** provide an extra challenge.
- Exercises labelled **(practice)** give extra hands-on fluency.

## Changes from PLFA

- Replaced Agda tooling and personal-history remarks with PLFH's
  Dependent Haskell framing, totality discipline, and library reuse notes.
- Retained the opening exposition of *Propositions as Types* and exercise
  labels from Philip Wadler and Wen Kokke's original Preface
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/frontmatter/Preface.md)).
