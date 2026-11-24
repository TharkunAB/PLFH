{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- EXPECT-ERROR: GHC-83865
module NegZeroSucc (zeroEqualsOne) where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Size (Size (..))

zeroEqualsOne :: 'Zero :~: 'Succ 'Zero
zeroEqualsOne = Refl
