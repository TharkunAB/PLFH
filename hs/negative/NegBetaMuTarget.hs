{-# LANGUAGE DataKinds, GADTs #-}
-- EXPECT-ERROR: GHC-83865
module NegBetaMuTarget (wrong) where

import HaskLib.Nat (Nat (Zero))
import PLFH.Part2.Lambda (Step (..), Term (..))

wrong :: Step (TMu Zero TZero)
              (TCase TZero TZero Zero (TMu Zero TZero))
wrong = BetaMu
