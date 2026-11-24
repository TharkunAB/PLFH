{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
-- | Minimal reproducer (GHC CORE LINT FAILURE — Serokell R11!):
-- Matching two GADTs (`SimRel m m'` and `Value m`) indexed by the same
-- promoted indexed GADT (`m :: Term g a`) typechecks, but FAILS Core Lint
-- immediately after Desugar with:
--   R11 mixed-kind coercion binder: 'Pair m n ~# ('Pair (v |> ...) (w |> ...) |> ...)
-- Discovered in PLFA Part 2 Bisimulation (`simValue`).
module R11_MixedKindCoercionCoreLint where

import Data.Kind (Type)

data Ty = TNat | TProd Ty Ty
data Ctx = CEmpty

data Term (g :: Ctx) (a :: Ty) where
  Zero :: Term g 'TNat
  Pair :: Term g a -> Term g b -> Term g ('TProd a b)

type Value :: forall (g :: Ctx) (a :: Ty). Term g a -> Type
data Value m where
  VZero :: Value 'Zero
  VPair :: Value v -> Value w -> Value ('Pair v w)

type SimRel :: forall (g :: Ctx) (a :: Ty). Term g a -> Term g a -> Type
data SimRel m m' where
  SimRefl :: SimRel m m
  SimPair :: SimRel m m' -> SimRel n n' -> SimRel ('Pair m n) ('Pair m' n')

simValue :: SimRel m m' -> Value m -> Value m'
simValue SimRefl         v           = v
simValue (SimPair s1 s2) (VPair v w) = VPair (simValue s1 v) (simValue s2 w)
