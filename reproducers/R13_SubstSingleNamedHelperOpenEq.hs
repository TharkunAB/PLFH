{-# LANGUAGE DependentTypes #-}
-- | Minimal reproducer (Serokell R13 / R16, Proposal #378):
-- Blocks discharging `PLFH.Part2.Bisimulation.SubstCompat` unconditionally
-- (the final step separating `Bisimulation` from `Checked`, 24/25 chapters!).
--
-- Two halves of the same `GHC.Tc.Gen.SourceClosure` split:
--   1. When `substSingle n w = subst (\case { Z -> w; S x -> Var x }) n`,
--      `SourceClosure` publishes `M.substSingle` via private `allocateFamilies`
--      closure constructors rather than reducing `M.substSingle n w` to
--      `M.subst (singleSubst w) n` — so `Bisimulation`'s 20-constructor
--      `simSubst :: Compatible p q -> SimRel m n -> SimRel (M.subst p m) (M.subst q n)`
--      cannot be instantiated to prove `SimRel (M.substSingle n v) (M.substSingle n' v')`.
--   2. Factoring out the named helper `singleSubst` and writing
--      `substSingle n w = subst (singleSubst w) n` (in `ReproOpsSubstHelper`)
--      suppresses open-equation publication for `M.substSingle` altogether,
--      failing below with `GHC-70565` ("Cannot evaluate M.substSingle in a type.
--      This argument is a type variable. Closed evaluation requires a known value.").
module R13_SubstSingleNamedHelperOpenEq where

import Data.Kind (Type)
import qualified ReproOpsSubstHelper as M

type Step :: forall (g :: M.Ctx) (a :: M.Ty). M.Term g a -> M.Term g a -> Type
data Step m n where
  BetaLam :: forall g a b (body :: M.Term (M.CExt g a) b) (v :: M.Term g a).
             Step (M.App (M.Lam body) v) (M.substSingle body v)
