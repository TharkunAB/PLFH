{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, PolyKinds, TypeOperators #-}
-- | Minimal reproducer (Serokell R13/R16 / -O2 list rewrite-rule guard):
-- Passes `-O0` and `-O2 -fno-enable-rewrite-rules` (`rev`/`revAppend`/
-- `revInvolutive`/`shuntRev`/`reverses` are all checked in `PLFH.Part1.Lists`),
-- but fails at default `-O2` with `GHC-70565` due to list rewrite rules on `[x]`.
module R13_RevOpenEq where

import Data.Type.Equality ((:~:) (Refl))
import ReproOps (rev)

revNil :: forall a. rev ('[] :: [a]) :~: '[]
revNil = Refl
