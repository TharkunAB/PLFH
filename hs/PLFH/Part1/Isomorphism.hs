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
  ) where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Size (Size (..))

{-# LINE 42 "content/part1/Isomorphism.md" #-}
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

{-# LINE 78 "content/part1/Isomorphism.md" #-}
-- | Identity function on Size with explicit structural equations.
idSize :: Size -> Size
idSize Zero     = Zero
idSize (Succ n) = Succ n

-- | Round-trip identity proof for `idSize`.
idSizeId :: foreach (x :: Size) -> idSize (idSize x) :~: x
idSizeId Zero     = Refl
idSizeId (Succ _) = Refl

-- | Monomorphic isomorphism witness on Size (declaration checks!).
data IsoSize where
  MkIsoSize :: foreach (to :: Size -> Size) -> foreach (from :: Size -> Size)
            -> (foreach (x :: Size) -> from (to x) :~: x)
            -> (foreach (y :: Size) -> to (from y) :~: y)
            -> IsoSize
