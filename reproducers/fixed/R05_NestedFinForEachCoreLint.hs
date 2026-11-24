{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs, PolyKinds #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications, TypeOperators #-}
-- | Minimal reproducer (Serokell R05 / R04 Desugar Core Lint bug in Wave 2 Lane 1 `03b7bb9a00`):
-- Nested `case` matches on `Fin (Succ (Succ m))` followed by passing `FS y` as a
-- retained `foreach (y :: Fin n)` argument to `CmpNeq` typechecks cleanly, but
-- fails `-dcore-lint` in Desugar ("Application error in expression"): Desugar
-- wraps `($WFS y) \`cast\` (Sub (Fin ('Succ co)_N)_N)` outside `$WFS`, mismatching
-- `'FS (y |> (Fin co)_N)` in the `RemoveFin` argument type.
module R05_NestedFinForEachCoreLint where

import Data.Kind (Type)
import HaskLib.Nat (Nat (..))

data Fin (n :: Nat) where
  FZ :: Fin (Succ n)
  FS :: Fin n -> Fin (Succ n)

type RemoveFin :: forall (n :: Nat). Fin (Succ n) -> Fin (Succ n) -> Fin n -> Type
data RemoveFin c x y where
  RemGt :: forall {n} (y :: Fin n). RemoveFin FZ (FS y) y
  RemLt :: forall {n} (c :: Fin (Succ n)). RemoveFin (FS c) FZ FZ
  RemSS :: RemoveFin c x y -> RemoveFin (FS c) (FS x) (FS y)

type CmpFin :: forall (n :: Nat). Fin (Succ n) -> Fin (Succ n) -> Type
data CmpFin c x where
  CmpEq  :: CmpFin c c
  CmpNeq :: foreach (y :: Fin n) -> RemoveFin c x y -> CmpFin c x

cmpFinFZ :: forall (m :: Nat).
            foreach (x :: Fin (Succ (Succ m))) -> CmpFin (FS (FZ @m)) x
cmpFinFZ x = case x of
  FZ    -> CmpNeq FZ (RemLt @FZ)
  FS x' -> case x' of
    FZ   -> CmpEq
    FS y -> CmpNeq (FS y) (RemSS (RemGt @y))
