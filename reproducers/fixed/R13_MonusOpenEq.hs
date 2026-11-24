{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (Serokell R13/R16):
-- PLFA's `monus` (imported from ReproOps) fails open evaluation in types
-- with GHC-70565. Blocks PLFA Induction exercises `0∸n≡0` and `∸-+-assoc`.
module R13_MonusOpenEq where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..))
import ReproOps (monus)

zeroMonus :: foreach (n :: Nat) -> monus 'Zero n :~: 'Zero
zeroMonus Zero     = Refl
zeroMonus (Succ _) = Refl
