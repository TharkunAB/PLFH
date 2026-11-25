{-# LANGUAGE DependentTypes #-}
-- | Cross-module checked-equation proofs for `PLFH.Part1.Lists.witnessToAny`.
-- Verifies that decoding an `AnyWitness` preserves both the selected list
-- position and the original predicate proof, even when the membership tail
-- is symbolic, with zero promoted-constructor ticks.
module PLFH.Part1.ListsProof
  ( witnessToAnyHere
  , witnessToAnyThere
  , witnessToAnyEvenThere
  , decodeHeadEven
  , decodeSecondEven
  , sampleTailMem
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import GHC.Types (List)
import HaskLib (Matchability)
import HaskLib.Nat (Nat (..))
import PLFH.Part1.Lists (Any (..), AnyWitness (..), In, witnessToAny)
import PLFH.Part1.Relations (Even (..))

-- | Decoding a head witness produces `Here px` directly for any predicate `p`.
witnessToAnyHere
  :: forall {a} {m :: Matchability} (p :: a %m -> Type) (x :: a) (xs :: List a) (px :: p x).
     witnessToAny (MkAnyWitness (Here Refl) px :: AnyWitness p (x : xs))
     :~: Here px
witnessToAnyHere = Refl

-- | Decoding a tail witness preserves both the symbolic membership tail `r`
-- and the original predicate proof `px` for any predicate `p`.
witnessToAnyThere
  :: forall {a} {m :: Matchability} (p :: a %m -> Type) (x :: a) (y :: a) (xs :: List a).
     forall (r :: In x xs) (px :: p x) ->
     witnessToAny (MkAnyWitness (There r) px :: AnyWitness p (y : xs))
     :~: There (witnessToAny (MkAnyWitness r px :: AnyWitness p xs) :: Any p xs)
witnessToAnyThere _ _ = Refl

-- | Retained-`foreach` tail preservation for `Even` over symbolic `In x xs`.
witnessToAnyEvenThere
  :: forall (x :: Nat) (y :: Nat) (xs :: List Nat).
     foreach (r :: In x xs) -> foreach (ev :: Even x) ->
     witnessToAny (MkAnyWitness (There r) ev :: AnyWitness Even (y : xs))
     :~: There (witnessToAny (MkAnyWitness r ev :: AnyWitness Even xs) :: Any Even xs)
witnessToAnyEvenThere _ _ = Refl

-- | Concrete head-occurrence decoding on `[0]`.
decodeHeadEven
  :: witnessToAny (MkAnyWitness (Here Refl) EvenZ :: AnyWitness Even [0 :: Nat])
     :~: Here EvenZ
decodeHeadEven = witnessToAnyHere @Even @0 @[] @EvenZ

-- | Concrete second-occurrence witness on `[1, 2, 1, 2]`: decoding selects
-- the 4th position (the second `2`), preserving the exact `Even 2` proof!
decodeSecondEven
  :: forall (ev :: Even 2).
     witnessToAny
       (MkAnyWitness (There (There (There (Here Refl)))) ev
          :: AnyWitness Even [1 :: Nat, 2 :: Nat, 1 :: Nat, 2 :: Nat])
     :~: There (There (There (Here ev)))
decodeSecondEven = Refl

-- | Concrete tail membership witness `2 ∈ [2, 1, 2]` selecting the second `2`.
sampleTailMem :: In (2 :: Nat) [2 :: Nat, 1 :: Nat, 2 :: Nat]
sampleTailMem = There (There (Here Refl))
