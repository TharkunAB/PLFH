{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (Serokell R13/R16):
-- Structural equality `eqSize` (imported from ReproOps, unguarded tail recursion
-- returning Bool) fails open evaluation in types with GHC-70565.
module R13_EqSizeOpenEq where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Size (Size (..))
import ReproOps (eqSize)

eqRefl :: foreach (n :: Size) -> eqSize n n :~: 'True
eqRefl Zero     = Refl
eqRefl (Succ n) = eqRefl n
