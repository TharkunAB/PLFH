{-# LANGUAGE DependentTypes #-}
-- EXPECT-ERROR: GHC-83865
module NegBigStepBadLookup (badLookup) where

import PLFH.Part2.BigStep (Clos (..), Env (..), EvalFun (..))
import PLFH.Part2.Untyped (Fin (..), IdTerm, OmegaTerm, UTerm (..))

-- Rejected: `FS FZ` looks up `IdTerm`, not `OmegaTerm`.
badLookup
  :: EvalFun ENil
             (UApp (UApp (ULam (ULam (UVar (FS FZ)))) IdTerm) OmegaTerm)
             (MkClos OmegaTerm ENil)
badLookup = EFApp (EFApp EFLam EFLam) (EFVar EFLam)
