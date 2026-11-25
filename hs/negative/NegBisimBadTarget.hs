{-# LANGUAGE DependentTypes #-}
-- EXPECT-ERROR: GHC-83865
module NegBisimBadTarget where

import qualified PLFH.Part2.More as M
import PLFH.Part2.Bisimulation (Leg (..), SimRel (..))

-- MUST FAIL: `(λx. suc x) 0` reduces to `Suc Zero`, NOT `Zero`!
badLetDesugar :: Leg @M.CEmpty @M.TNat M.Step (M.App (M.Lam (M.Suc (M.Var M.Z))) M.Zero) M.Zero
badLetDesugar = MkLeg (M.BetaLam M.VZero) SimZero
