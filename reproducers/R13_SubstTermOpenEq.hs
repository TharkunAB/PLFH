{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (Serokell R13/R16):
-- Capture-avoiding substitution `substTerm` (branching on `case eqSize x y of`,
-- imported from ReproOps) fails open evaluation in types with GHC-70565.
-- Blocks PLFA Properties `subst` typing lemma and `preserve` (β-reduction cases).
module R13_SubstTermOpenEq where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..))
import ReproOps (Term (..), substTerm)

substSuc :: foreach (m :: Term) -> foreach (y :: Nat) -> foreach (v :: Term)
         -> substTerm ('TSuc m) y v :~: 'TSuc (substTerm m y v)
substSuc _ _ _ = Refl
