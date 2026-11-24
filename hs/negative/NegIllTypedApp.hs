{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs #-}
-- EXPECT-ERROR: GHC-83865
module NegIllTypedApp (badApp) where

import PLFH.Part2.Lambda (Ctx (..), HasType (..), Term (..), Ty (..))

badApp :: HasType 'CEmpty ('App 'TZero 'TZero) 'TNat
badApp = TApp TZeroT TZeroT
