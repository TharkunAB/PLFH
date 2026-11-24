{-# LANGUAGE AllowAmbiguousTypes, DataKinds, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, Modifiers, PolyKinds, RequiredTypeArguments, TypeOperators #-}
-- | Minimal reproducer (R23 / RequiredTypeArguments partial application of
-- right-first open-equation functions):
-- With published 35916907b9, Agda-style `cong (plus m) eq` and
-- `cong (timesNamed m) eq` both compile cleanly with RequiredTypeArguments.
-- However, passing a right-first recursive function `pow m` (imported from
-- ReproOps, whose checked equations split the 2nd argument) to visible `cong`
-- fails with GHC-70565 ("Expected 2 value arguments, but got 1. Closed calls
-- must be fully applied."), even though `pow` has checked open equations and
-- invisible `cong @(pow m) eq` previously worked!
--
-- Expected: `cong (pow m) eq` compiles just like `cong (plus m) eq` and
-- `cong (timesNamed m) eq`.
-- Actual (published 35916907b9): GHC-70565 on `pow m` in `badPow`.
module R23_CongRightFirstPartialApp where

import Data.Type.Equality ((:~:) (Refl))
import GHC.Types (Matchability)
import HaskLib.Nat (Nat (..), plus)
import ReproOps (pow, timesNamed)

cong :: forall {a} {b} {m :: Matchability}.
        forall (f :: a %m -> b) -> forall (x :: a) (y :: a).
        x :~: y -> f x :~: f y
cong _ Refl = Refl

-- Controls (left-first functions — PASS!):
okPlus :: foreach (m :: Nat) -> foreach (x :: Nat) -> foreach (y :: Nat)
       -> x :~: y -> plus m x :~: plus m y
okPlus m _ _ eq = cong (plus m) eq

okTimes :: foreach (m :: Nat) -> foreach (x :: Nat) -> foreach (y :: Nat)
        -> x :~: y -> timesNamed m x :~: timesNamed m y
okTimes m _ _ eq = cong (timesNamed m) eq

-- Fails with GHC-70565 because `pow` is right-first:
badPow :: foreach (m :: Nat) -> foreach (x :: Nat) -> foreach (y :: Nat)
       -> x :~: y -> pow m x :~: pow m y
badPow m _ _ eq = cong (pow m) eq
