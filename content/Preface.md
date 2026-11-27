---
title: "Preface"
description: "Propositions as Types, totality discipline, and how PLFH adapts Programming Language Foundations in Agda to Dependent Haskell."
prev: /
next: /setup/
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
(Language Foundations) in Haskell". The specifications we write in
Dependent Haskell both describe programming languages and are
themselves Haskell programs compiled by GHC.

This book is an adaptation of Philip Wadler, Wen Kokke, and Jeremy G. Siek's
[*Programming Language Foundations in Agda*](https://plfa.inf.ed.ac.uk/)
(licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)).
All 25 chapters across Parts 1, 2, and 3 are written and checked in Dependent
Haskell (`-XDependentTypes`) using
[`TharkunAB/ghc`](https://github.com/TharkunAB/ghc/tree/dependent-haskell).

## How this book differs from PLFA

Because Haskell is a general-purpose lazy functional language, four differences
from Agda appear throughout the text:

1. **Totality and partiality.** Agda enforces termination and positivity checks
   so every well-typed term denotes a total value. Without totality, a
   non-terminating loop or `undefined` could inhabit any type, including a false
   proposition. GHC does not enforce totality by default, though
   `-freport-totality` provides opt-in advisory checks. Every proof in PLFH is
   written by structural recursion on finite inductive inputs, without typed
   holes, `-fdefer-type-errors`, `undefined`, `error`, circular proof bindings,
   or `unsafeCoerce`. Whenever an Agda proof relies on totality or function
   extensionality, the text notes that explicitly.
2. **Direct Dependent Haskell.** Theorems in PLFH are written directly over
   ordinary Haskell functions and datatypes with `-XDependentTypes`, without
   singletons or duplicate `type family` copies. See [Chapter Coverage](/status/)
   for the chapter-by-chapter mapping.
3. **Library reuse.** PLFH reuses standard indexed datatypes and laws from
   [`dependent-base`](https://github.com/TharkunAB/dependent-base) so one
   shared `Nat` and one shared `List` type work across all 25 chapters.
4. **Interactive chapters.** Every chapter runs directly in the browser through
   WebAssembly so you can edit proofs, solve exercises, and query GHCi while
   reading.

## A word on the exercises

Following PLFA:

- Exercises labeled **(recommended)** cover the core material.
- Exercises labeled **(stretch)** provide an extra challenge.
- Exercises labeled **(practice)** give extra hands-on fluency.
