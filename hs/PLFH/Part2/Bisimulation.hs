-- Generated from content/part2/Bisimulation.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
{-# LINE 13 "content/part2/Bisimulation.md" #-}
module PLFH.Part2.Bisimulation
  ( SimRel (..)
  , Leg (..)
  , simValueLam
  , simValue
  ) where

import Data.Kind (Type)
import PLFH.Part2.More (Ctx (..), Term (..), Ty (..), Value (..))

{-# LINE 32 "content/part2/Bisimulation.md" #-}
-- | Structural simulation relation over promoted extended STLC terms.
type SimRel :: forall (g :: Ctx) (a :: Ty). Term g a -> Term g a -> Type
data SimRel m m' where
  SimRefl :: SimRel m m
  SimLam  :: SimRel n n' -> SimRel ('Lam n) ('Lam n')
  SimApp  :: SimRel l l' -> SimRel m m' -> SimRel ('App l m) ('App l' m')
  SimPair :: SimRel m m' -> SimRel n n' -> SimRel ('Pair m n) ('Pair m' n')

-- | One leg of a simulation diagram for an arbitrary reduction relation `step`:
-- m' steps to n' with n ~ n'.
type Leg :: forall (g :: Ctx) (a :: Ty). (Term g a -> Term g a -> Type) -> Term g a -> Term g a -> Type
data Leg step m' n where
  MkLeg :: step m' n' -> SimRel n n' -> Leg step m' n

-- | Simulation preserves lambda values cleanly.
simValueLam :: SimRel ('Lam n) ('Lam n') -> Value ('Lam n) -> Value ('Lam n')
simValueLam _ VLam = VLam

-- | General value preservation across promoted GADT indices (`~-val`).
simValue :: SimRel m m' -> Value m -> Value m'
simValue SimRefl         v           = v
simValue (SimLam _)      VLam        = VLam
simValue (SimPair s1 s2) (VPair v w) = VPair (simValue s1 v) (simValue s2 w)
