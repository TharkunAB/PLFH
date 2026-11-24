{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (Serokell R03/R04):
-- `data IsoSize` with monomorphic retained function fields and higher-rank
-- `foreach` proof fields compiles, but constructing `MkIsoSize idSize idSize idSizeId idSizeId`
-- fails with GHC-83865 reporting identical expected and actual types:
--   Expected: foreach (x :: Nat) -> idSize (idSize x) :~: x
--   Actual:   foreach (x :: Nat) -> idSize (idSize x) :~: x
module R04_HigherRankForEachField where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..))

idSize :: Nat -> Nat
idSize Zero     = Zero
idSize (Succ n) = Succ n

data IsoSize where
  MkIsoSize :: foreach (to :: Nat -> Nat) -> foreach (from :: Nat -> Nat)
            -> (foreach (x :: Nat) -> from (to x) :~: x)
            -> (foreach (y :: Nat) -> to (from y) :~: y)
            -> IsoSize

idSizeId :: foreach (x :: Nat) -> idSize (idSize x) :~: x
idSizeId Zero     = Refl
idSizeId (Succ _) = Refl

isoRefl :: IsoSize
isoRefl = MkIsoSize idSize idSize idSizeId idSizeId
