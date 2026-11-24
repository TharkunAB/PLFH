{-# LANGUAGE DependentTypes #-}
-- EXPECT-ERROR: GHC-83865
module NegBinReverseRoundTrip where

import Data.Type.Equality ((:~:) (Refl))
import PLFH.Part1.Naturals (Bin (..), fromBin, toBin)

reverseRoundTrip :: toBin (fromBin Nil) :~: Nil
reverseRoundTrip = Refl
