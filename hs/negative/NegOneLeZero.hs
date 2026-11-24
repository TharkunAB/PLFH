{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs #-}
-- EXPECT-ERROR: GHC-83865
module NegOneLeZero (oneLeZero) where

import HaskLib.Size (Size (..))
import PLFH.Part1.Relations (LE (..))

oneLeZero :: LE ('Succ 'Zero) 'Zero
oneLeZero = ZleN
