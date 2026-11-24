-- Generated from content/part1/Isomorphism.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
{-# LINE 12 "content/part1/Isomorphism.md" #-}
module PLFH.Part1.Isomorphism
  ( Iff (..)
  , iffRefl
  , iffSym
  , iffTrans
  , IsoSize (..)
  , idSize
  , idSizeId
  , isoSizeRefl
  , isoSizeSym
  ) where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..))

{-# LINE 44 "content/part1/Isomorphism.md" #-}
-- | Logical equivalence (bi-implication) between propositions `a` and `b`.
data Iff a b = Iff
  { toIff   :: a -> b
  , fromIff :: b -> a
  }

-- | Reflexivity of logical equivalence.
iffRefl :: Iff a a
iffRefl = Iff id id

-- | Symmetry of logical equivalence.
iffSym :: Iff a b -> Iff b a
iffSym (Iff f g) = Iff g f

-- | Transitivity of logical equivalence.
iffTrans :: Iff a b -> Iff b c -> Iff a c
iffTrans (Iff f1 g1) (Iff f2 g2) = Iff (f2 . f1) (g1 . g2)

{-# LINE 80 "content/part1/Isomorphism.md" #-}
-- | Identity function on Nat with explicit structural equations.
idSize :: Nat -> Nat
idSize Zero     = Zero
idSize (Succ n) = Succ n

-- | Round-trip identity proof for `idSize`.
idSizeId :: foreach (x :: Nat) -> idSize (idSize x) :~: x
idSizeId Zero     = Refl
idSizeId (Succ _) = Refl

-- | Monomorphic isomorphism witness on Nat.
data IsoSize where
  MkIsoSize :: foreach (to :: Nat -> Nat) -> foreach (from :: Nat -> Nat)
            -> (foreach (x :: Nat) -> from (to x) :~: x)
            -> (foreach (y :: Nat) -> to (from y) :~: y)
            -> IsoSize

-- | Reflexivity of `IsoSize` (constructing higher-rank `foreach` proof fields!).
isoSizeRefl :: IsoSize
isoSizeRefl = MkIsoSize idSize idSize idSizeId idSizeId

-- | Symmetry of `IsoSize`: swap `to`/`from` and their round-trip proofs.
isoSizeSym :: IsoSize -> IsoSize
isoSizeSym (MkIsoSize to from fromTo toFrom) = MkIsoSize from to toFrom fromTo
