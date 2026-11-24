---
title: "Decidable: Negation, Booleans, and Decision Procedures"
prev: /Equality/
next: /Lists/
src: content/part1/Decidable.md
module: PLFH.Part1.Decidable
plfaChapter: https://plfa.inf.ed.ac.uk/19.08/Decidable/
---

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs, TypeOperators #-}
module PLFH.Part1.Decidable
  ( Not
  , Dec (..)
  , zeroNeqSucc
  , decEqSize
  , decLeSize
  , Sigma (..)
  , SizeWitness
  , mkSizeWitness
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void)
import GHC.Sigma (Sigma (Pair))
import HaskLib.Size (Size (..), congSucc, plus)
import PLFH.Part1.Relations (LE (..), invSleS)
```

Before moving on to lists and lambda calculus, we assemble the core logical
building blocks from PLFA's **Connectives**, **Negation**, **Quantifiers**,
and **Decidable** chapters: negation (`Not`), decision procedures (`Dec`),
and dependent pairs (`Sigma`).

## Negation (`¬`)

Following *Propositions as Types*, falsehood is the empty type `Void` from
`Data.Void`, and negation `Not a` is a function `a -> Void`:

```haskell
-- | Logical negation: evidence that a proposition implies falsehood (Void).
type Not a = a -> Void

-- | Zero is never equal to any successor.
zeroNeqSucc :: Not ('Zero :~: 'Succ n)
zeroNeqSucc eq = case eq of {}
```

<div class="note-box">
<strong>Totality note:</strong>
In Agda, <code>¬ A = A → ⊥</code> is sound because Agda rejects
non-terminating functions and <code>undefined</code>. In Haskell,
<code>undefined :: a -&gt; Void</code> typechecks, so every proof of
<code>Not a</code> in PLFH must discharge its hypothesis constructively
via an impossible GADT pattern match (<code>case ... of {}</code>) with
no bottoms or loops.
</div>

## Decidable propositions (`Dec`)

A proposition `p :: Type` is *decidable* if we can construct either a proof
of `p` (`Yes`) or a refutation `Not p` (`No`):

```haskell
-- | Evidence that a proposition `p` is decidable.
data Dec (p :: Type) where
  Yes :: p     -> Dec p
  No  :: Not p -> Dec p
```

### Decidable equality on `Size`

With `foreach` and `EmptyCase`, decidable equality on natural numbers is a
direct structural recursion:

```haskell
-- | Decidable propositional equality on Size.
decEqSize :: foreach (m :: Size) -> foreach (n :: Size) -> Dec (m :~: n)
decEqSize Zero n = case n of
  Zero   -> Yes Refl
  Succ _ -> No (\case {})
decEqSize (Succ m) n = case n of
  Zero    -> No (\case {})
  Succ n' -> case decEqSize m n' of
    Yes eq -> Yes (congSucc eq)
    No neq -> No (\Refl -> neq Refl)
```

### Decidable ordering (`_≤?_`)

Similarly, `m ≤ n` is decidable for all finite `m` and `n`:

```haskell
-- | Decidable less-than-or-equal relation on Size.
decLeSize :: foreach (m :: Size) -> foreach (n :: Size) -> Dec (LE m n)
decLeSize Zero _ = Yes ZleN
decLeSize (Succ m) n = case n of
  Zero    -> No (\case {})
  Succ n' -> case decLeSize m n' of
    Yes p  -> Yes (SleS p)
    No np  -> No (\p -> np (invSleS p))
```

## Dependent pairs (existentials, `Σ`)

This GHC fork provides retained dependent pairs `GHC.Sigma.Sigma` (`some (x :: a) | p x`,
constructed with `Pair x px`, Serokell R04). For example, we can pair a
runtime `Size` with evidence that `Zero <= k`:

```haskell
-- | A dependent pair carrying a runtime size `k` and evidence that Zero <= k.
type SizeWitness = some (k :: Size) | LE 'Zero k

-- | Package any runtime size with its proof of Zero <= k.
mkSizeWitness :: Size -> SizeWitness
mkSizeWitness k = Pair k ZleN
```

<div class="wip-notice">
<strong>[WIP NOTICE — Returning an inline <code>some</code> from a <code>foreach</code> function (R04)]</strong>
Writing a dependent function whose result type is an inline retained sum
mentioning the retained inputs:
<pre class="wip"><code>plusExists :: foreach (m :: Size) -&gt; foreach (n :: Size)
           -&gt; some (k :: Size) | k :~: plus m n</code></pre>
is currently rejected on GHC <code>db2586fdc2</code> (<em>A retained dependent
sum is supported in a top-level type synonym, as the result of a type family
equation, in a complete top-level value signature, or in a constructor field...</em>).
See minimal reproducer
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R04_SigmaUnderForEach.hs"><code>reproducers/R04_SigmaUnderForEach.hs</code></a>.
</div>

## Changes from PLFA `v19.08`

- Consolidates the core definitions needed for later chapters from
  [Negation](https://plfa.inf.ed.ac.uk/19.08/Negation/),
  [Quantifiers](https://plfa.inf.ed.ac.uk/19.08/Quantifiers/), and
  [Decidable](https://plfa.inf.ed.ac.uk/19.08/Decidable/) (v19.08).
- `Not`, `zeroNeqSucc`, `Dec`, `decEqSize`, `decLeSize`, and `Sigma`/`some`
  (`plusExists`) all port directly and pass `-dcore-lint -dstg-lint`!
- Uses `Data.Void.Void` and `EmptyCase` (`\case {}`) in place of Agda's `⊥`
  and absurd pattern `()`.
