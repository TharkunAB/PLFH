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
  , SumPred (..)
  , existsDistribSum
  , existsCurryTo
  , existsCurryFrom
  , Forall (..)
  , ProdPred (..)
  , forallDistribProd
  , notExistsToForallNot
  , forallNotToNotExists
  , EvenSigma
  , evenZeroSigma
  , evenTwoSigma
  , EvenWitness (..)
  , evenWitnessZero
  , evenWitnessSuc2
  , evenDouble
  , evenToWitness
  , witnessToEven
  , evenIffWitness
  , OddWitness (..)
  , oddToWitness
  , witnessToOdd
  , oddIffWitness
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import GHC.Sigma (Sigma (Pair))
import HaskLib (rewrite)
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

## Erased existential and universal quantification (`∃`, `∀`)

```haskell
-- | Erased existential: there exists some type-level `x :: a` satisfying `p x`.
data Exists (p :: a -> Type) where
  Witness :: p x -> Exists p

-- | Pointwise disjunction of predicates.
data SumPred (p :: a -> Type) (q :: a -> Type) (x :: a) where
  InL :: p x -> SumPred p q x
  InR :: q x -> SumPred p q x

-- | Existentials distribute over disjunction:
-- (∃ x. P x ∨ Q x) ⇔ (∃ x. P x) ∨ (∃ x. Q x).
existsDistribSum :: Iff (Exists (SumPred p q)) (Either (Exists p) (Exists q))
existsDistribSum = Iff toF fromF
  where
    toF (Witness (InL px)) = Left (Witness px)
    toF (Witness (InR qx)) = Right (Witness qx)

    fromF (Left (Witness px))  = Witness (InL px)
    fromF (Right (Witness qx)) = Witness (InR qx)

-- | Currying for existentials (`Σ-curry`): (∃ x. P x -> C) ⇔ (∀ x. P x -> C).
existsCurryTo :: (Exists p -> c) -> (forall x. p x -> c)
existsCurryTo f px = f (Witness px)

existsCurryFrom :: (forall x. p x -> c) -> (Exists p -> c)
existsCurryFrom g (Witness px) = g px

-- | First-class wrapper for universal quantification and pointwise conjunction.
newtype Forall (p :: a -> Type) = MkForall { unForall :: forall x. p x }
newtype ProdPred (p :: a -> Type) (q :: a -> Type) (x :: a) =
  MkProdPred { unProdPred :: (p x, q x) }

-- | Universals distribute over conjunction (`∀-×`):
-- (∀ x. P x ∧ Q x) ⇔ (∀ x. P x) ∧ (∀ x. Q x).
forallDistribProd :: Iff (Forall (ProdPred p q)) (Forall p, Forall q)
forallDistribProd =
  Iff (\f -> ( MkForall (fst (unProdPred (unForall f)))
             , MkForall (snd (unProdPred (unForall f))) ))
      (\(fp, fq) -> MkForall (MkProdPred (unForall fp, unForall fq)))

-- | De Morgan for quantifiers: ¬(∃ x. P x) ⇔ ∀ x. ¬(P x).
notExistsToForallNot :: Not (Exists p) -> (forall x. Not (p x))
notExistsToForallNot ne px = ne (Witness px)

forallNotToNotExists :: (forall x. Not (p x)) -> Not (Exists p)
forallNotToNotExists fn (Witness px) = fn px
```

## Retained dependent pairs (`Σ`): `Even` and `Odd` as existential doubles

PLFA shows that the inductive predicates `even n` and `odd n` are equivalent
to the existential statements `∃ (k : ℕ), k + k ≡ n` and
`∃ (k : ℕ), suc (k + k) ≡ n`.

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

Packaging the same retained witness as `EvenWitness n` and `OddWitness n`, we
prove **both directions** of the equivalence (`evenIffWitness` and
`oddIffWitness`), using `HaskLib.rewrite (plusSucc k k)` in `evenDouble`:

```haskell
-- | Retained existential witness that `n` is double some runtime `k`.
data EvenWitness (n :: Nat) where
  MkEvenWitness :: foreach (k :: Nat) -> plus k k :~: n -> EvenWitness n

evenWitnessZero :: EvenWitness 'Zero
evenWitnessZero = MkEvenWitness Zero Refl

evenWitnessSuc2 :: EvenWitness n -> EvenWitness ('Succ ('Succ n))
evenWitnessSuc2 (MkEvenWitness k Refl) =
  MkEvenWitness (Succ k) (congSucc (plusSucc k k))

-- | Every double `k + k` is even (proved directly using `HaskLib.rewrite`).
evenDouble :: foreach (k :: Nat) -> Even (plus k k)
evenDouble Zero     = EvenZ
evenDouble (Succ k) = rewrite (plusSucc k k) (EvenS (OddS (evenDouble k)))

-- | Every inductive `Even n` derivation yields a runtime half `k` with `k + k = n`.
evenToWitness :: Even n -> EvenWitness n
evenToWitness EvenZ              = evenWitnessZero
evenToWitness (EvenS (OddS evn)) = evenWitnessSuc2 (evenToWitness evn)

-- | Converse: a runtime witness `k + k = n` reconstructs `Even n`.
witnessToEven :: EvenWitness n -> Even n
witnessToEven (MkEvenWitness k Refl) = evenDouble k

-- | Full bi-implication: `Even n ⇔ (∃ k. k + k = n)`.
evenIffWitness :: Iff (Even n) (EvenWitness n)
evenIffWitness = Iff evenToWitness witnessToEven

-- | Retained existential witness that `n = suc (k + k)` for some runtime `k`.
data OddWitness (n :: Nat) where
  MkOddWitness :: foreach (k :: Nat) -> 'Succ (plus k k) :~: n -> OddWitness n

oddToWitness :: Odd n -> OddWitness n
oddToWitness (OddS ev) = case evenToWitness ev of
  MkEvenWitness k Refl -> MkOddWitness k Refl

witnessToOdd :: OddWitness n -> Odd n
witnessToOdd (MkOddWitness k Refl) = OddS (evenDouble k)

-- | Full bi-implication: `Odd n ⇔ (∃ k. suc (k + k) = n)`.
oddIffWitness :: Iff (Odd n) (OddWitness n)
oddIffWitness = Iff oddToWitness witnessToOdd
```

## Changes from PLFA `v22.08`

- Adapted from [Quantifiers (v22.08)](https://plfa.inf.ed.ac.uk/22.08/Quantifiers/)
  ([source](https://github.com/plfa/plfa.github.io/blob/e2d545f3df0db4d4206c5448735665abde02d81f/src/plfa/part1/Quantifiers.lagda.md)).
- Contrasts erased `Exists` GADTs with retained `GHC.Sigma` (`some ... | ...`)
  and `foreach`-carrying GADT witnesses (`EvenWitness`, `OddWitness`).
- Checked direct ports of `existsDistribSum`, `existsCurryTo`/`From`,
  `forallDistribProd`, quantifier De Morgan (`notExistsToForallNot`,
  `forallNotToNotExists`), `EvenSigma`, and **both directions** of the parity
  witness equivalences (`evenIffWitness`, `oddIffWitness`).
