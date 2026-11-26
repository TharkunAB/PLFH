{-# LANGUAGE DependentTypes #-}
-- EXPECT-ERROR: GHC-83865
module NegOneLeZero (oneLeZero) where

import Data.Nat.Dependent (Nat (..))
import PLFH.Part1.Relations (LE (..))

oneLeZero :: LE 1 0
oneLeZero = ZleN
