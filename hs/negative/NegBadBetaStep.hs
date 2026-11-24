{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs #-}
-- EXPECT-ERROR: GHC-83865
module NegBadBetaStep (badBeta) where

import PLFH.Part2.Untyped (BetaStep (..), IdTerm, OmegaTerm, SubstAtU (..), UTerm (..))

badBeta :: BetaStep (UApp IdTerm IdTerm) OmegaTerm
badBeta = Beta SUEq
