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
2. **A live yardstick** for the experimental Dependent Haskell branch of GHC
   ([`TharkunAB/ghc`, branch `dependent-haskell`](https://github.com/TharkunAB/ghc/tree/dependent-haskell)).
   For every definition and theorem in PLFA (Parts 1, 2, and 3), we ask whether
   a Haskell programmer can state and prove it directly with the same hypotheses
   using `-XDependentTypes`.

## How this book differs from PLFA

Because Haskell is a general-purpose lazy functional programming language
and this Dependent Haskell implementation is under active development,
several differences from Agda are called out explicitly throughout the text:

- **Totality and partiality.** Agda enforces termination and positivity
  checks so that every well-typed term denotes a total value; without
  totality, a non-terminating loop or `undefined` could inhabit any type,
  including a false proposition. GHC does not have a totality checker.
  Every checked proof in PLFH is therefore written by structural recursion
  on finite inductive inputs, with **no** typed holes, **no**
  `-fdefer-type-errors`, **no** `undefined` or `error`, **no** circular
  proof bindings, and **no** `unsafeCoerce`. Whenever an Agda proof
  relies on totality, we note that explicitly.
- **Direct Dependent Haskell.** Rather than disguising compiler gaps behind
  singletons or ad-hoc type-family encodings, every theorem in PLFH is written
  directly in Dependent Haskell. Any remaining compiler follow-up is isolated
  as a minimal standalone reproducer and tracked on the
  [Yardstick Status](/Status/) page.
- **Reuse from `HaskLib`.** The GHC fork ships a companion proof library,
  `HaskLib`, containing ordinary-function arithmetic and list-length laws.
  Whenever a PLFA theorem is already provided by `HaskLib`, we reuse it
  and record it as reuse.
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
  Dependent Haskell yardstick framing, totality discipline, reproducer
  tracking, and `HaskLib` reuse notes.
- Retained the opening exposition of *Propositions as Types* and exercise
  labels from Philip Wadler and Wen Kokke's original Preface
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/frontmatter/Preface.md)).
