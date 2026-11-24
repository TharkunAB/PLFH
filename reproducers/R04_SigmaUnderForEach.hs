{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (Serokell R04):
-- Returning an inline retained dependent sum (`some (k :: Size) | ...`)
-- directly from a `foreach`-quantified function is rejected.
module R04_SigmaUnderForEach where

import Data.Type.Equality ((:~:) (Refl))
import GHC.Sigma (Sigma (Pair))
import HaskLib.Size (Size (..), plus)

plusExists :: foreach (m :: Size) -> foreach (n :: Size)
           -> some (k :: Size) | k :~: plus m n
plusExists m n = Pair (plus m n) Refl
