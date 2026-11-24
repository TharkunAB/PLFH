{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (Serokell R13/R16):
-- PLFA's `pow` (recursion on second argument, imported from ReproOps) fails
-- open evaluation in types with GHC-70565. Blocks PLFA Induction `+*^`.
module R13_PowOpenEq where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..))
import ReproOps (pow)

powZero :: foreach (m :: Nat) -> pow m 'Zero :~: 'Succ 'Zero
powZero _ = Refl
