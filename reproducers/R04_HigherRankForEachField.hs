{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (Serokell R03/R04):
-- `data IsoSize` with monomorphic retained function fields and higher-rank
-- `foreach` proof fields compiles, but constructing `MkIsoSize idSize idSize idSizeId idSizeId`
-- fails with GHC-83865 reporting identical expected and actual types:
--   Expected: foreach (x :: Size) -> idSize (idSize x) :~: x
--   Actual:   foreach (x :: Size) -> idSize (idSize x) :~: x
module R04_HigherRankForEachField where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Size (Size (..))

idSize :: Size -> Size
idSize Zero     = Zero
idSize (Succ n) = Succ n

data IsoSize where
  MkIsoSize :: foreach (to :: Size -> Size) -> foreach (from :: Size -> Size)
            -> (foreach (x :: Size) -> from (to x) :~: x)
            -> (foreach (y :: Size) -> to (from y) :~: y)
            -> IsoSize

idSizeId :: foreach (x :: Size) -> idSize (idSize x) :~: x
idSizeId Zero     = Refl
idSizeId (Succ _) = Refl

isoRefl :: IsoSize
isoRefl = MkIsoSize idSize idSize idSizeId idSizeId
