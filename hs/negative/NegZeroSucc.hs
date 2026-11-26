{-# LANGUAGE DependentTypes #-}
-- EXPECT-ERROR: GHC-83865
module NegZeroSucc (zeroEqualsOne) where

import Data.Nat.Dependent (Nat (..))
import Data.Type.Equality ((:~:) (Refl))

zeroEqualsOne :: (0 :: Nat) :~: 1
zeroEqualsOne = Refl
