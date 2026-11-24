{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Client module importing `plusAssoc` from PLFH.Part1.Induction
-- and exercising it at unknown runtime inputs and retained decimal literals.
module PLFH.Part1.InductionClient
  ( usePlusAssoc
  , checkPlusAssoc
  , useTimesComm
  , plusZeroAtThree
  ) where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..), plus, plusZero)
import PLFH.Part1.Induction (plusAssoc, timesComm)
import PLFH.Part1.Naturals (times)

-- | Dependent client using `plusAssoc` at unknown runtime inputs.
usePlusAssoc :: foreach (a :: Nat) -> foreach (b :: Nat) -> foreach (c :: Nat)
             -> plus (plus a b) c :~: plus a (plus b c)
usePlusAssoc a b c = plusAssoc a b c

-- | Ordinary Haskell client consuming the equality proof at unknown inputs.
checkPlusAssoc :: Nat -> Nat -> Nat -> Bool
checkPlusAssoc a b c = case plusAssoc a b c of
  Refl -> True

-- | Dependent client using `timesComm` at unknown inputs.
useTimesComm :: foreach (a :: Nat) -> foreach (b :: Nat)
             -> times a b :~: times b a
useTimesComm a b = timesComm a b

-- | Retained call site using a decimal Nat literal directly (`plusZero 3`).
plusZeroAtThree :: plus 3 0 :~: 3
plusZeroAtThree = plusZero 3
