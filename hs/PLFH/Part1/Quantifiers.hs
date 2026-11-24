-- Generated from content/part1/Quantifiers.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, PolyKinds #-}
{-# LANGUAGE RankNTypes, TypeOperators, UndecidableInstances #-}
{-# LINE 13 "content/part1/Quantifiers.md" #-}
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
import HaskLib.Size (Size (..), congSucc, plus, plusSucc)
import PLFH.Part1.Decidable (Not)
import PLFH.Part1.Isomorphism (Iff (..))
import PLFH.Part1.Relations (Even (..), Odd (..))

{-# LINE 48 "content/part1/Quantifiers.md" #-}
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

{-# LINE 85 "content/part1/Quantifiers.md" #-}
-- | Retained dependent sum: there exists a runtime `k` with `k + k = n`.
type EvenSigma (n :: Size) = some (k :: Size) | plus k k :~: n

evenZeroSigma :: EvenSigma 'Zero
evenZeroSigma = Pair Zero Refl

evenTwoSigma :: EvenSigma ('Succ ('Succ 'Zero))
evenTwoSigma = Pair (Succ Zero) Refl

{-# LINE 100 "content/part1/Quantifiers.md" #-}
-- | Retained existential witness that `n` is double some runtime `k`.
data EvenWitness (n :: Size) where
  MkEvenWitness :: foreach (k :: Size) -> plus k k :~: n -> EvenWitness n

evenWitnessZero :: EvenWitness 'Zero
evenWitnessZero = MkEvenWitness Zero Refl

evenWitnessSuc2 :: EvenWitness n -> EvenWitness ('Succ ('Succ n))
evenWitnessSuc2 (MkEvenWitness k Refl) =
  MkEvenWitness (Succ k) (congSucc (plusSucc k k))

-- | Every inductive `Even n` derivation yields a runtime half `k` with `k + k = n`.
evenToWitness :: Even n -> EvenWitness n
evenToWitness EvenZ              = evenWitnessZero
evenToWitness (EvenS (OddS evn)) = evenWitnessSuc2 (evenToWitness evn)
