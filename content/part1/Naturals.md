---
title: "Naturals: Natural numbers"
prev: /Setup/
next: /Induction/
src: content/part1/Naturals.md
module: PLFH.Part1.Naturals
plfaChapter: https://plfa.inf.ed.ac.uk/Naturals/
---

```haskell
{-# LANGUAGE DataKinds, ExplicitNamespaces, ExperimentalDependentTypes, GADTs, TypeOperators #-}
module PLFH.Part1.Naturals
  ( Nat (..)
  , plus
  , type (+)
  , times
  , monus
  , pow
  , Bin (..)
  , inc
  , toBin
  , fromBin
  , twoPlusThree
  , twoPlusThreeInfix
  , fiveAtRuntime
  ) where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..), plus, type (+))
```

The night sky holds more stars than I can count, though fewer than five
thousand are visible to the naked eye. The observable universe contains
about seventy sextillion stars.

But the number of stars is finite, while natural numbers are infinite.
Count all the stars, and you will still have as many natural numbers
left over as you started with.

## The naturals are an inductive datatype

Everyone is familiar with the natural numbers `0, 1, 2, 3, ...`.
We can specify them with two inference rules:

<div class="inference-rule">
  <div class="premises">&nbsp;</div>
  <div class="conclusion">Zero :: Nat</div>
</div>
<div class="inference-rule">
  <div class="premises">m :: Nat</div>
  <div class="conclusion">Succ m :: Nat</div>
</div>

In PLFA, the chapter defines `data ℕ : Set where zero : ℕ; suc : ℕ → ℕ`.
In PLFH we reuse the identical inductive Peano type `Nat` from
`HaskLib.Nat` (originally defined in `PreludeMapLengthSize`):

```{.haskell .ignore}
data Nat = Zero | Succ Nat
```

Both definitions express the same two rules:

- *Base case*: `Zero` is a natural number.
- *Inductive case*: if `m` is a natural number, then `Succ m` is also a natural number.

In Dependent Haskell (with `DataKinds` and `ExperimentalDependentTypes`),
`Nat` is simultaneously an ordinary runtime algebraic datatype **and** a
type-level kind whose promoted constructors are `'Zero` and `'Succ`.

<div class="note-box">
<strong>Totality note (Haskell vs. Agda):</strong>
In Agda, <code>ℕ</code> contains only finite inductive terms. In Haskell,
every lifted datatype also admits non-terminating expressions such as
<code>undefined</code> or infinite values like <code>let inf = Succ inf in inf</code>.
Our theorems in PLFH establish properties for all <em>finite</em>
inductive inputs; every proof is written by structural recursion without
bottoms, holes, or circular bindings.
</div>

#### Exercise `seven` (practice) {#seven}

Write out `7` in longhand using `Zero` and `Succ`.

```{.haskell .exercise}
-- Your code goes here
```

## Addition (reused from `HaskLib`) {#plus}

In PLFA, addition is defined by recursion on its first argument:

```{.haskell .ignore}
_+_ : ℕ → ℕ → ℕ
zero    + n = n
(suc m) + n = suc (m + n)
```

`HaskLib.Nat` already exports an ordinary Haskell function `plus` with the
exact same recursion on its first argument (defined in `PreludeAppendLengthSource`):

```{.haskell .ignore}
plus :: Nat -> Nat -> Nat
plus Zero     n = n
plus (Succ m) n = Succ (plus m n)
```

Because `plus` is compiled with `-XExperimentalDependentTypes`, GHC records
its defining equations in its interface so we can write `plus` directly in
**both** ordinary runtime code and type-level propositions—without
duplicating it as a separate `type family`!

For example, because `HaskLib.Nat` provides a `FromNatural` instance (at the
type level) and a `Num` instance (at the term level) for `Nat`, we can write
fixed natural numbers using **ordinary decimal numerals** (`0`, `1`, `2`, `3`,
`5`, ...) while continuing to use `Zero` and `Succ` constructor patterns for
inductive definitions and proofs:

```haskell
-- | Evidence that 2 + 3 = 5 using ordinary Haskell `plus` and decimal literals!
twoPlusThree :: plus 2 3 :~: 5
twoPlusThree = Refl

-- | The same proof using `HaskLib.Nat`'s infix type operator `(+)`.
twoPlusThreeInfix :: (2 + 3 :: Nat) :~: 5
twoPlusThreeInfix = Refl

-- | Ordinary runtime arithmetic using the same `Nat` and `Num` instance.
fiveAtRuntime :: Nat
fiveAtRuntime = 2 + 3
```

Here `(:~:)` from `Data.Type.Equality` is propositional equality (playing
the role of Agda's `_≡_`), and `Refl` is its sole constructor (playing the
role of Agda's `refl`). GHC converts the decimal literals to Peano naturals
via `FromNatural`, reduces `plus` using its checked source equations, and
immediately verifies that both sides normalize to `5`.

<div class="note-box">
<strong>HaskLib reuse:</strong>
<code>Nat</code>, <code>plus</code>, infix <code>type (+)</code>, and the
<code>FromNatural</code> / <code>Num</code> decimal-numeral instances are
reused directly from <code>HaskLib.Nat</code> (where <code>Size</code> remains
exported as a compatibility synonym for <code>Nat</code>).
</div>

#### Exercise `+-example` (practice) {#plus-example}

State and check `3 + 4 = 7` using `plus`, `(:~:)`, and `Refl`.

```{.haskell .exercise}
-- Your code goes here
```

## Multiplication

Once we have addition, we define multiplication as repeated addition by
recursion on its first argument:

```haskell
-- | Multiply two sizes by recursion on the first argument.
times :: Nat -> Nat -> Nat
times Zero     n = Zero
times (Succ m) n = plus n (times m n)
```

<div class="wip-notice">
<strong>[WIP NOTICE — Wildcard patterns break open source equations (R13/R16)]</strong>
Notice that we wrote <code>times Zero n = Zero</code> with a <em>named</em>
variable <code>n</code> rather than <code>times Zero _ = Zero</code>.
On GHC commit <code>db2586fdc2</code>, writing a wildcard <code>_</code> in
the base case silently prevents GHC from registering open source equations
for <code>times</code>, causing downstream proofs over unknown variables to
fail with <code>GHC-70565</code> (<em>Cannot evaluate 'times' in a type</em>).
See minimal reproducer
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_WildcardBreaksOpenEq.hs"><code>reproducers/R13_WildcardBreaksOpenEq.hs</code></a>.
</div>

#### Exercise `*-example` (practice) {#times-example}

Check that `3 * 4 = 12` using `times` in a client module that imports
`PLFH.Part1.Naturals`.

```{.haskell .exercise}
-- Your code goes here
```

## Exponentiation {#power}

PLFA defines exponentiation as an exercise by recursion on the **second**
argument:

```haskell
-- | Exponentiation by recursion on the second argument.
pow :: Nat -> Nat -> Nat
pow m Zero     = Succ Zero
pow m (Succ n) = times m (pow m n)
```

<div class="wip-notice">
<strong>[WIP NOTICE — Recursion on the second argument in open types (R13/R16)]</strong>
<code>pow</code> compiles as an ordinary Haskell function, but on GHC
<code>db2586fdc2</code> GHC does not yet publish open source equations for
functions that recurse on their <em>second</em> argument. Using
<code>pow m 'Zero</code> with an unknown <code>m</code> in a type fails with
<code>GHC-70565</code>. See
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_PowOpenEq.hs"><code>reproducers/R13_PowOpenEq.hs</code></a>.
</div>

## Monus

Truncated subtraction on natural numbers (*monus*, written `∸` in PLFA)
returns zero whenever the second argument is larger than the first:

```haskell
-- | Truncated subtraction (monus), matching PLFA's exact clause order.
monus :: Nat -> Nat -> Nat
monus m        Zero     = m
monus Zero     (Succ n) = Zero
monus (Succ m) (Succ n) = monus m n
```

<div class="note-box">
<strong>Fixed compiler gap (<code>63e2f0974b</code> / <code>76e67f4fdb</code>):</strong>
On earlier GHC baselines (<code>db2586fdc2</code>–<code>9cc4065fab</code>),
<code>monus</code> failed open type-level evaluation with <code>GHC-70565</code>.
Checked right-first structural equations for ordinary <code>monus</code> are now
published on <code>dependent-haskell</code>
(<a href="https://github.com/Tritlo/ghc/commit/63e2f0974b174dc86bef79c3a84d1d76fea3dadf"><code>63e2f0974b</code></a>),
tracked as regression check
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/fixed/R13_MonusOpenEq.hs"><code>reproducers/fixed/R13_MonusOpenEq.hs</code></a>,
and used directly to prove <code>zeroMonus</code> and <code>monusPlusAssoc</code>
in <a href="/Induction/">Induction</a>!
</div>

## Binary natural numbers (`Bin`, stretch exercise) {#Bin}

PLFA's stretch exercise introduces a binary representation of natural
numbers as least-significant-bit-first bitstrings:

```haskell
-- | Least-significant-bit-first binary natural numbers.
data Bin
  = Nil
  | X0 Bin
  | X1 Bin
  deriving (Show)

-- | Increment a binary bitstring by one.
inc :: Bin -> Bin
inc Nil    = X1 Nil
inc (X0 b) = X1 b
inc (X1 b) = X0 (inc b)

-- | Convert unary `Nat` to `Bin`.
toBin :: Nat -> Bin
toBin Zero     = X0 Nil
toBin (Succ n) = inc (toBin n)

-- | Convert `Bin` back to unary `Nat`.
fromBin :: Bin -> Nat
fromBin Nil    = Zero
fromBin (X0 b) = plus (fromBin b) (fromBin b)
fromBin (X1 b) = Succ (plus (fromBin b) (fromBin b))
```

Remarkably, all three ordinary Haskell functions (`inc`, `toBin`, and
`fromBin`) automatically get checked open source equations on this fork—so
in [Induction](/Induction/) we will prove `fromBin (inc b) :~: 'Succ (fromBin b)`
and `fromBin (toBin n) :~: n` directly by induction!

## Changes from PLFA

- Adapted from [Naturals](https://plfa.inf.ed.ac.uk/Naturals/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part1/Naturals.lagda.md)).
- Reused `Nat` (`Zero`/`Succ`) and `plus` from `HaskLib.Nat` instead of
  redefining `ℕ` and `_+_`.
- Replaced Agda's `≡-Reasoning` chains on concrete examples with direct
  `(:~:)` / `Refl` checks (see [Induction](/Induction/) and [Equality](/Equality/)
  for equational reasoning in Dependent Haskell).
- Implemented `times`, `pow`, `monus`, and `Bin`/`inc`/`toBin`/`fromBin` as
  ordinary Haskell functions, documenting the `R13`/`R16` open-equation
  boundaries with `[WIP NOTICE]` callouts.
- Omitted Agda's Emacs `agda-mode` keybinding tutorial and `BUILTIN` pragmas,
  adding a Haskell totality note instead.
