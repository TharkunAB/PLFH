{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (Serokell R03/R04):
-- Declaring a polymorphic isomorphism GADT `Iso a b` with retained function
-- fields `foreach (to :: a -> b)` fails with GHC-83605 (unsupported function domain).
-- Monomorphic `Size -> Size` is accepted at the datatype declaration.
module R04_PolyFunctionFieldInIso where

import Data.Type.Equality ((:~:))

data Iso a b where
  MkIso :: foreach (to :: a -> b) -> foreach (from :: b -> a)
        -> (foreach (x :: a) -> from (to x) :~: x)
        -> (foreach (y :: b) -> to (from y) :~: y)
        -> Iso a b
