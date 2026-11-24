{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (Serokell R13/R16):
-- `timesWild Zero _ = Zero` (imported from ReproOps) fails open evaluation
-- with GHC-70565, while `timesNamed Zero n = Zero` succeeds.
module R13_WildcardBreaksOpenEq where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Size (Size (..))
import ReproOps (timesWild)

timesZeroL :: foreach (n :: Size) -> timesWild 'Zero n :~: 'Zero
timesZeroL _ = Refl
