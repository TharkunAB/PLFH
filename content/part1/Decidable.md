---
title: "Decidable: Booleans and decision procedures"
prev: /Quantifiers/
next: /Lists/
src: content/part1/Decidable.md
module: PLFH.Part1.Decidable
plfaChapter: https://plfa.inf.ed.ac.uk/Decidable/
---

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs, TypeOperators #-}
module PLFH.Part1.Decidable
  ( Not
  , Dec (..)
  , decNot
  , decAnd
  , decOr
  , decImp
  , decIff
  , zeroNeqSucc
  , decEqSize
  , decLeSize
  , decLtSize
  , decEven
  , decOdd
  , decEqBin
  , decOne
  , decCan
  , Reflects (..)
  , reflectsToDec
  , Sigma (..)
  , SizeWitness
  , mkSizeWitness
  , plusExists
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void, absurd)
import GHC.Sigma (Sigma (Pair))
import HaskLib.Nat (Nat (..), congSucc, plus)
import PLFH.Part1.Isomorphism (Iff (..))
import PLFH.Part1.Naturals (Bin (..))
import PLFH.Part1.Relations (Can (..), Even (..), LE (..), LT' (..), Odd (..), One (..), invSleS)
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

-- | Decidable propositions are closed under negation, conjunction, disjunction,
-- implication, and bi-implication.
decNot :: Dec p -> Dec (Not p)
decNot (Yes p)  = No (\np -> np p)
decNot (No  np) = Yes np

decAnd :: Dec p -> Dec q -> Dec (p, q)
decAnd (Yes p) (Yes q) = Yes (p, q)
decAnd (No np) _       = No (\(p, _) -> np p)
decAnd _       (No nq) = No (\(_, q) -> nq q)

decOr :: Dec p -> Dec q -> Dec (Either p q)
decOr (Yes p) _       = Yes (Left p)
decOr _       (Yes q) = Yes (Right q)
decOr (No np) (No nq) = No (either np nq)

decImp :: Dec p -> Dec q -> Dec (p -> q)
decImp (No np) _       = Yes (\p -> absurd (np p))
decImp _       (Yes q) = Yes (const q)
decImp (Yes p) (No nq) = No (\f -> nq (f p))

decIff :: Dec p -> Dec q -> Dec (Iff p q)
decIff dp dq = case decAnd (decImp dp dq) (decImp dq dp) of
  Yes (f, g) -> Yes (Iff f g)
  No nfg     -> No (\(Iff f g) -> nfg (f, g))
```

### Decidable equality on `Nat`

With `foreach` and `EmptyCase`, decidable equality on natural numbers is a
direct structural recursion:

```haskell
-- | Decidable propositional equality on Nat.
decEqSize :: foreach (m :: Nat) -> foreach (n :: Nat) -> Dec (m :~: n)
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
-- | Decidable less-than-or-equal relation on Nat.
decLeSize :: foreach (m :: Nat) -> foreach (n :: Nat) -> Dec (LE m n)
decLeSize Zero _ = Yes ZleN
decLeSize (Succ m) n = case n of
  Zero    -> No (\case {})
  Succ n' -> case decLeSize m n' of
    Yes p  -> Yes (SleS p)
    No np  -> No (\p -> np (invSleS p))

-- | Decidable strict less-than relation on Nat (`_<?_`).
decLtSize :: foreach (m :: Nat) -> foreach (n :: Nat) -> Dec (LT' m n)
decLtSize Zero n = case n of
  Zero   -> No (\case {})
  Succ _ -> Yes ZltS
decLtSize (Succ m) n = case n of
  Zero    -> No (\case {})
  Succ n' -> case decLtSize m n' of
    Yes p  -> Yes (SltS p)
    No  np -> No (\case SltS q -> np q)
```

### Decidable parity (`decEven`, `decOdd`) and Boolean reflection (`Reflects`)

Parity is also decidable by two-step structural recursion on `Nat`. Notice
that GHC's R03 pattern-matching rules currently reject nested constructor
patterns like `decEven (Succ Zero)` directly in a retained column, so we match
the inner `n` in a `case` expression on the right-hand side:

```haskell
-- | Decidable evenness predicate on Nat.
decEven :: foreach (n :: Nat) -> Dec (Even n)
decEven Zero     = Yes EvenZ
decEven (Succ n) = case n of
  Zero    -> No (\case EvenS o -> case o of {})
  Succ n' -> case decEven n' of
    Yes ev  -> Yes (EvenS (OddS ev))
    No  nev -> No (\case EvenS (OddS ev) -> nev ev)

-- | Decidable oddness predicate on Nat.
decOdd :: foreach (n :: Nat) -> Dec (Odd n)
decOdd Zero     = No (\case {})
decOdd (Succ n) = case n of
  Zero    -> Yes (OddS EvenZ)
  Succ n' -> case decOdd n' of
    Yes od  -> Yes (OddS (EvenS od))
    No  nod -> No (\case OddS (EvenS od) -> nod od)

-- | Boolean reflection: ties a proposition `p` to a promoted `Bool` `b`.
data Reflects (p :: Type) (b :: Bool) where
  OfTrue  :: p -> Reflects p 'True
  OfFalse :: Not p -> Reflects p 'False

-- | Reflecting a Boolean yields a decision procedure.
reflectsToDec :: foreach (b :: Bool) -> Reflects p b -> Dec p
reflectsToDec True  (OfTrue p)   = Yes p
reflectsToDec False (OfFalse np) = No np

-- | Decidable equality and canonical-form predicates on binary numbers (`Bin`).
decEqBin :: foreach (a :: Bin) -> foreach (b :: Bin) -> Dec (a :~: b)
decEqBin Nil b = case b of
  Nil  -> Yes Refl
  X0 _ -> No (\case {})
  X1 _ -> No (\case {})
decEqBin (X0 a) b = case b of
  Nil   -> No (\case {})
  X1 _  -> No (\case {})
  X0 b' -> case decEqBin a b' of
    Yes Refl -> Yes Refl
    No  neq  -> No (\Refl -> neq Refl)
decEqBin (X1 a) b = case b of
  Nil   -> No (\case {})
  X0 _  -> No (\case {})
  X1 b' -> case decEqBin a b' of
    Yes Refl -> Yes Refl
    No  neq  -> No (\Refl -> neq Refl)

decOne :: foreach (b :: Bin) -> Dec (One b)
decOne Nil    = No (\case {})
decOne (X0 b) = case decOne b of
  Yes o  -> Yes (OneX0 o)
  No  no -> No (\case OneX0 o -> no o)
decOne (X1 b) = case b of
  Nil   -> Yes OneX1
  X0 b' -> case decOne (X0 b') of
    Yes o  -> Yes (OneX1' o)
    No  no -> No (\case OneX1' o -> no o)
  X1 b' -> case decOne (X1 b') of
    Yes o  -> Yes (OneX1' o)
    No  no -> No (\case OneX1' o -> no o)

decCan :: foreach (b :: Bin) -> Dec (Can b)
decCan Nil    = No (\case CanOne o -> case o of {})
decCan (X0 b) = case b of
  Nil   -> Yes CanZ
  X0 b' -> case decOne (X0 b') of
    Yes o  -> Yes (CanOne (OneX0 o))
    No  no -> No (\case CanOne (OneX0 o) -> no o)
  X1 b' -> case decOne (X1 b') of
    Yes o  -> Yes (CanOne (OneX0 o))
    No  no -> No (\case CanOne (OneX0 o) -> no o)
decCan (X1 b) = case decOne (X1 b) of
  Yes o  -> Yes (CanOne o)
  No  no -> No (\case CanOne o -> no o)
```

## Dependent pairs (existentials, `Σ`)

This GHC fork provides retained dependent pairs `GHC.Sigma.Sigma` (`some (x :: a) | p x`,
constructed with `Pair x px`, Serokell R04). For example, we can pair a
runtime `Nat` with evidence that `Zero <= k`:

```haskell
-- | A dependent pair carrying a runtime size `k` and evidence that Zero <= k.
type SizeWitness = some (k :: Nat) | LE 'Zero k

-- | Package any runtime size with its proof of Zero <= k.
mkSizeWitness :: Nat -> SizeWitness
mkSizeWitness k = Pair k ZleN

-- | Inline retained dependent sum returned directly from a `foreach` function!
plusExists :: foreach (m :: Nat) -> foreach (n :: Nat)
           -> some (k :: Nat) | k :~: plus m n
plusExists m n = Pair (plus m n) Refl
```

## Changes from PLFA

- Consolidates the core definitions needed for later chapters from
  [Negation](https://plfa.inf.ed.ac.uk/Negation/),
  [Quantifiers](https://plfa.inf.ed.ac.uk/Quantifiers/), and
  [Decidable](https://plfa.inf.ed.ac.uk/Decidable/).
- `Not`, `zeroNeqSucc`, `Dec`, `decNot`/`And`/`Or`/`Imp`/`Iff`, `decEqSize`,
  `decLeSize`, `decLtSize`, `decEven`, `decOdd`, `decEqBin`/`decOne`/`decCan`,
  `Reflects`, `reflectsToDec`, and `Sigma`/`some` (`SizeWitness`,
  `mkSizeWitness`, and inline `plusExists`) all port directly and pass
  `-dcore-lint -dstg-lint`!
- Uses `Data.Void.Void` and `EmptyCase` (`\case {}`) in place of Agda's `⊥`
  and absurd pattern `()`.
