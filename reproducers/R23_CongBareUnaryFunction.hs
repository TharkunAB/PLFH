{-# LANGUAGE AllowAmbiguousTypes, DataKinds, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, Modifiers, PolyKinds, RequiredTypeArguments, TypeOperators #-}
-- | Minimal reproducer (R23 / RequiredTypeArguments bare unary function):
-- With published 35916907b9, Agda-style `cong Succ eq` (constructor) and
-- `cong (plus m) eq` (partially applied 2-arg function) both compile cleanly
-- under RequiredTypeArguments. However, passing a bare 1-arg ordinary function
-- `inc :: Bin -> Bin` (`cong inc eq`) fails with GHC-68947 ("No checked
-- equations are available for 'inc' in a type"), even though `inc` has checked
-- equations (it reduces `inc Nil :~: X1 Nil` cleanly) and invisible `cong @inc`
-- previously worked!
--
-- Hit while converting `PLFH.Part1.Relations.toFromOne` from `cong @inc` to
-- visible `cong inc`.
--
-- Expected: `cong inc eq` compiles just like `cong Succ eq` and `cong (plus m) eq`.
-- Actual (published 35916907b9): GHC-68947 on `inc` in `badInc`.
module R23_CongBareUnaryFunction where

import Data.Type.Equality ((:~:) (Refl))
import GHC.Types (Matchability)
import HaskLib.Nat (Nat (..), plus)

data Bin = Nil | X0 Bin | X1 Bin

inc :: Bin -> Bin
inc Nil    = X1 Nil
inc (X0 b) = X1 b
inc (X1 b) = X0 (inc b)

-- Control 1: `inc` DOES have checked equations in types!
incNil :: inc Nil :~: X1 Nil
incNil = Refl

cong :: forall {a} {b} {m :: Matchability}.
        forall (f :: a %m -> b) -> forall (x :: a) (y :: a).
        x :~: y -> f x :~: f y
cong _ Refl = Refl

-- Control 2: `cong Succ` and `cong (plus m)` PASS!
okSucc :: foreach (x :: Nat) -> foreach (y :: Nat) -> x :~: y -> Succ x :~: Succ y
okSucc _ _ eq = cong Succ eq

okPlus :: foreach (m :: Nat) -> foreach (x :: Nat) -> foreach (y :: Nat)
       -> x :~: y -> plus m x :~: plus m y
okPlus m _ _ eq = cong (plus m) eq

-- Fails with GHC-68947 on bare unary function `inc`:
badInc :: foreach (x :: Bin) -> foreach (y :: Bin) -> x :~: y -> inc x :~: inc y
badInc _ _ eq = cong inc eq
