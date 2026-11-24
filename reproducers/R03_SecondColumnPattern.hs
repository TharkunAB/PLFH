{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (Serokell R03):
-- Splitting directly on the second retained argument in function equations
-- (as in PLFA's `+-comm m zero` / `+-comm m (suc n)`) is rejected with
-- GHC-83605; only the leading retained column admits constructor equations.
module R03_SecondColumnPattern where

import Data.Type.Equality ((:~:) (Refl), trans)
import HaskLib.Size (Size (..), congSucc, plus, plusSucc, plusZero)

plusCommEq :: foreach (m :: Size) -> foreach (n :: Size) -> plus m n :~: plus n m
plusCommEq m Zero     = plusZero m
plusCommEq m (Succ n) = plusSucc m n `trans` congSucc (plusCommEq m n)
