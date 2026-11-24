{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, Modifiers #-}
{-# LANGUAGE PolyKinds, RankNTypes, ScopedTypeVariables, TypeApplications #-}
-- | Minimal reproducer (Serokell R23):
-- Matchable constructor `EqP x :: a -> Type` cannot directly instantiate
-- an unmatchable predicate `p :: a %U -> Type` in Leibniz equality.
module R23_MatchabilityInLeibniz where

import Data.Kind (Type)
import GHC.Exts (U)

data EqP (x :: a) (y :: a) where
  ReflP :: EqP x x

type LeibnizU (x :: a) (y :: a) = forall (p :: a %U -> Type). p x -> p y

leibnizUToEqDirect :: forall {a} (x :: a) (y :: a). LeibnizU x y -> EqP x y
leibnizUToEqDirect f = f @(EqP x) ReflP
