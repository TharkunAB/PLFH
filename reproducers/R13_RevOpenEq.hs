{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, PolyKinds, TypeOperators #-}
-- | Minimal reproducer (Serokell R13/R16):
-- Naive quadratic `rev` (`rev (x:xs) = app (rev xs) [x]`, imported from ReproOps)
-- fails open evaluation in types with GHC-70565. Blocks PLFA Lists `shunt-reverse`.
module R13_RevOpenEq where

import Data.Type.Equality ((:~:) (Refl))
import ReproOps (rev)

revNil :: forall a. rev ('[] :: [a]) :~: '[]
revNil = Refl
