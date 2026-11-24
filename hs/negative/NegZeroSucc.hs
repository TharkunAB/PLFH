{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- EXPECT-ERROR: GHC-83865
module NegZeroSucc (zeroEqualsOne) where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..))

zeroEqualsOne :: (0 :: Nat) :~: 1
zeroEqualsOne = Refl
