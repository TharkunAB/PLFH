{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeApplications #-}
-- EXPECT-ERROR: GHC-83865
module NegBisimBadTarget where

import qualified PLFH.Part2.More as M
import qualified PLFH.Part2.MoreProgress as MP
import PLFH.Part2.Bisimulation (Leg (..), SimRel (..))

-- MUST FAIL: `(λx. suc x) 0` reduces to `Suc Zero`, NOT `Zero`!
badLetDesugar :: Leg @M.CEmpty @M.TNat MP.Step (M.App (M.Lam (M.Suc (M.Var M.Z))) M.Zero) M.Zero
badLetDesugar = MkLeg (MP.BetaLam M.VZero) SimZero
