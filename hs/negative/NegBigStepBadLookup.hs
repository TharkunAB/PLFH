{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs #-}
-- EXPECT-ERROR: GHC-83865
module NegBigStepBadLookup (badLookup) where

import qualified PLFH.Part2.BigStep as B
import PLFH.Part2.BigStepFunctional (Eval (..))
import PLFH.Part2.Untyped (Fin (..), IdTerm, OmegaTerm, UTerm (..))

-- MUST FAIL: `FS FZ` looks up `IdTerm`, NOT `OmegaTerm`!
badLookup
  :: Eval B.ENil
          (UApp (UApp (ULam (ULam (UVar (FS FZ)))) IdTerm) OmegaTerm)
          (B.MkClos OmegaTerm B.ENil)
badLookup = App (App Lam Lam) (Var Lam)
