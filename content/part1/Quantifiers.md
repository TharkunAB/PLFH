---
title: "Quantifiers: Universals and existentials"
prev: /Negation/
next: /Decidable/
src: content/part1/Quantifiers.md
module: PLFH.Part1.Quantifiers
plfaChapter: https://plfa.inf.ed.ac.uk/22.08/Quantifiers/
---

```haskell
{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, PolyKinds #-}
{-# LANGUAGE RankNTypes, TypeOperators, UndecidableInstances #-}
module PLFH.Part1.Quantifiers
  ( Exists (..)
  , existsDistribSum
  , notExistsToForallNot
  , forallNotToNotExists
  , EvenSigma
  , evenZeroSigma
  , evenTwoSigma
  , EvenWitness (..)
  , evenWitnessZero
  , evenWitnessSuc2
  , evenToWitness
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import GHC.Sigma (Sigma (Pair))
import HaskLib.Nat (Nat (..), congSucc, plus, plusSucc)
import PLFH.Part1.Decidable (Not)
import PLFH.Part1.Isomorphism (Iff (..))
import PLFH.Part1.Relations (Even (..), Odd (..))
```

In Dependent Haskell we encounter two complementary styles of existential
quantification:

1. **Erased existentials** (`Exists p`, a GADT hiding a type-level witness `x :: a`
   that is erased at runtime), and
2. **Retained dependent pairs** (`GHC.Sigma.Sigma` written `some (x :: a) | ...`,
   or a GADT constructor with a `foreach (x :: a) -> ...` field), where the
   witness is kept at runtime and can also appear in types!

## Erased existential quantification (`∃`)

```haskell
-- | Erased existential: there exists some type-level `x :: a` satisfying `p x`.
data Exists (p :: a -> Type) where
  Witness :: p x -> Exists p

-- | Existentials distribute over disjunction:
-- (∃ x. P x ∨ Q x) ⇔ (∃ x. P x) ∨ (∃ x. Q x).
data SumPred (p :: a -> Type) (q :: a -> Type) (x :: a) where
  InL :: p x -> SumPred p q x
  InR :: q x -> SumPred p q x

existsDistribSum :: Iff (Exists (SumPred p q)) (Either (Exists p) (Exists q))
existsDistribSum = Iff toF fromF
  where
    toF (Witness (InL px)) = Left (Witness px)
    toF (Witness (InR qx)) = Right (Witness qx)

    fromF (Left (Witness px))  = Witness (InL px)
    fromF (Right (Witness qx)) = Witness (InR qx)

-- | De Morgan for quantifiers: ¬(∃ x. P x) ⇔ ∀ x. ¬(P x).
notExistsToForallNot :: Not (Exists p) -> (forall x. Not (p x))
notExistsToForallNot ne px = ne (Witness px)

forallNotToNotExists :: (forall x. Not (p x)) -> Not (Exists p)
forallNotToNotExists fn (Witness px) = fn px
```

## Retained dependent pairs (`Σ`): `Even` as `∃ k. k + k = n`

PLFA shows that the inductive predicate `even n` is equivalent to the
existential statement `∃ (k : ℕ), k + k ≡ n`.

With GHC's retained dependent sum (`some (k :: Nat) | plus k k :~: n`,
Serokell R04) and `UndecidableInstances` (needed because the desugared
type-lambda family calls `plus k k`), we can state `EvenSigma` directly:

```haskell
-- | Retained dependent sum: there exists a runtime `k` with `k + k = n`.
type EvenSigma (n :: Nat) = some (k :: Nat) | plus k k :~: n

evenZeroSigma :: EvenSigma 0
evenZeroSigma = Pair Zero Refl

evenTwoSigma :: EvenSigma 2
evenTwoSigma = Pair 1 Refl
```

We can also package the same retained witness as a GADT `EvenWitness n` and
convert *every* inductive `Even n` proof into a constructive runtime witness
`k` such that `plus k k :~: n`!

```haskell
-- | Retained existential witness that `n` is double some runtime `k`.
data EvenWitness (n :: Nat) where
  MkEvenWitness :: foreach (k :: Nat) -> plus k k :~: n -> EvenWitness n

evenWitnessZero :: EvenWitness 'Zero
evenWitnessZero = MkEvenWitness Zero Refl

evenWitnessSuc2 :: EvenWitness n -> EvenWitness ('Succ ('Succ n))
evenWitnessSuc2 (MkEvenWitness k Refl) =
  MkEvenWitness (Succ k) (congSucc (plusSucc k k))

-- | Every inductive `Even n` derivation yields a runtime half `k` with `k + k = n`.
evenToWitness :: Even n -> EvenWitness n
evenToWitness EvenZ              = evenWitnessZero
evenToWitness (EvenS (OddS evn)) = evenWitnessSuc2 (evenToWitness evn)
```

Notice how `evenToWitness` works for **arbitrary unknown `n`**: pattern
matching on `Even n` refines `n` and builds the exact runtime half `k`
alongside its checked proof `plus k k :~: n`!

## Changes from PLFA `v22.08`

- Adapted from [Quantifiers (v22.08)](https://plfa.inf.ed.ac.uk/22.08/Quantifiers/)
  ([source](https://github.com/plfa/plfa.github.io/blob/e2d545f3df0db4d4206c5448735665abde02d81f/src/plfa/part1/Quantifiers.lagda.md)).
- Contrasts erased `Exists` GADTs with retained `GHC.Sigma` (`some ... | ...`)
  and `foreach`-carrying GADT witnesses (`EvenWitness`).
- Checked direct ports of `existsDistribSum`, quantifier De Morgan
  (`notExistsToForallNot`, `forallNotToNotExists`), `EvenSigma`, and
  `evenToWitness :: Even n -> EvenWitness n`.
