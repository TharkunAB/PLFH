{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Client module importing `plusAssoc` from PLFH.Part1.Induction
-- and exercising it at unknown runtime inputs (per PROMPT.md step 2).
module PLFH.Part1.InductionClient
  ( usePlusAssoc
  , checkPlusAssoc
  , useTimesComm
  ) where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Size (Size (..), plus)
import PLFH.Part1.Induction (plusAssoc, timesComm)
import PLFH.Part1.Naturals (times)

-- | Dependent client using `plusAssoc` at unknown runtime inputs.
usePlusAssoc :: foreach (a :: Size) -> foreach (b :: Size) -> foreach (c :: Size)
             -> plus (plus a b) c :~: plus a (plus b c)
usePlusAssoc a b c = plusAssoc a b c

-- | Ordinary Haskell client consuming the equality proof at unknown inputs.
checkPlusAssoc :: Size -> Size -> Size -> Bool
checkPlusAssoc a b c = case plusAssoc a b c of
  Refl -> True

-- | Dependent client using `timesComm` at unknown inputs.
useTimesComm :: foreach (a :: Size) -> foreach (b :: Size)
             -> times a b :~: times b a
useTimesComm a b = timesComm a b
