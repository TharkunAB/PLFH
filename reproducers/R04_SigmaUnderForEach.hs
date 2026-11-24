{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (Serokell R04):
-- Returning an inline retained dependent sum (`some (k :: Nat) | ...`)
-- directly from a `foreach`-quantified function is rejected.
module R04_SigmaUnderForEach where

import Data.Type.Equality ((:~:) (Refl))
import GHC.Sigma (Sigma (Pair))
import HaskLib.Nat (Nat (..), plus)

plusExists :: foreach (m :: Nat) -> foreach (n :: Nat)
           -> some (k :: Nat) | k :~: plus m n
plusExists m n = Pair (plus m n) Refl
