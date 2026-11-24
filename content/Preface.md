---
title: "Preface"
prev: /
next: /Setup/
src: content/Preface.md
plfaChapter: https://plfa.inf.ed.ac.uk/19.08/Preface/
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

This book is an adaptation of Philip Wadler and Wen Kokke's
[*Programming Language Foundations in Agda*](https://plfa.inf.ed.ac.uk/19.08/)
(edition `19.08`, commit `63fcbbe25ec3686ff4c6df2c5b58a96b3a2054f3`,
licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)).
It serves a dual purpose:

1. **A readable introduction** to programming language theory and formal
   proofs in Dependent Haskell, following PLFA's structure and prose closely.
2. **A live yardstick** for the experimental Dependent Haskell branch of GHC
   ([`Tritlo/ghc`, branch `dependent-haskell`](https://github.com/Tritlo/ghc/tree/dependent-haskell)).
   For every definition and theorem in PLFA `v19.08`, we ask whether a
   Haskell programmer can state and prove it directly with the same hypotheses
   using `-XExperimentalDependentTypes`.

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
- **No hidden workarounds (`[WIP NOTICE]`).** Rather than disguising
  current compiler gaps behind singletons or ad-hoc type-family encodings,
  whenever a theorem or programming pattern cannot yet be written directly
  in Dependent Haskell we place a prominent **[WIP NOTICE]** right in the
  chapter, link a minimal standalone reproducer for the compiler team, and
  record it on the [Yardstick Status](/Status/) page. Seeing these notices
  shrink over time measures Dependent Haskell's maturity directly.
- **Reuse from `HaskLib`.** The GHC fork ships a companion proof library,
  `HaskLib`, containing ordinary-function arithmetic and list-length laws.
  Whenever a PLFA theorem is already provided by `HaskLib`, we reuse it
  and record it as reuse.
- **Literate Haskell Markdown.** Every chapter in PLFH is a literate
  Markdown file. Plain ```` ```haskell ```` blocks are extracted into
  standalone `.hs` modules and checked by the Dependent Haskell GHC fork
  with `-dcore-lint -dstg-lint`. Dashed blocks mark exercises,
  expected-failure negative controls, or `[WIP NOTICE]` declarations not yet
  accepted by the compiler.

## A word on the exercises

Following PLFA:

- Exercises labelled **(recommended)** cover the core material.
- Exercises labelled **(stretch)** provide an extra challenge.
- Exercises labelled **(practice)** give extra hands-on fluency.

## Changes from PLFA `v19.08`

- Replaced Agda tooling and personal-history remarks with PLFH's
  Dependent Haskell yardstick framing, totality discipline, `[WIP NOTICE]`
  policy, and `HaskLib` reuse notes.
- Retained the opening exposition of *Propositions as Types* and exercise
  labels from Philip Wadler and Wen Kokke's original Preface
  ([source](https://github.com/plfa/plfa.github.io/blob/v19.08/src/plfa/preface.md)).
