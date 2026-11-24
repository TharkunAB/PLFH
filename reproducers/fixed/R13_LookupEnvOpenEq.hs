{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, StandaloneKindSignatures, TypeOperators #-}
-- | Minimal reproducer (Serokell R13/R16):
-- Calling a GADT-indexed environment lookup function `lookupEnv` inside a
-- promoted constructor type (`EvalBig e ('UVar x) (lookupEnv e x)`) fails
-- with GHC-68947: No checked equations are available for `lookupEnv` in a type.
-- Discovered in PLFA Part 2 BigStep (`EVar`).
module R13_LookupEnvOpenEq where

import Data.Kind (Type)
import HaskLib.Nat (Nat (..))

data Fin (n :: Nat) where
  FZ :: Fin ('Succ n)
  FS :: Fin n -> Fin ('Succ n)

data UTerm (n :: Nat) where
  UVar :: Fin n -> UTerm n
  ULam :: UTerm ('Succ n) -> UTerm n

data Env (n :: Nat) where
  ENil  :: Env 'Zero
  ECons :: Clos -> Env n -> Env ('Succ n)

data Clos where
  MkClos :: Env n -> UTerm ('Succ n) -> Clos

lookupEnv :: Env n -> Fin n -> Clos
lookupEnv (ECons c _) FZ     = c
lookupEnv (ECons _ e) (FS x) = lookupEnv e x

type EvalBig :: forall (n :: Nat). Env n -> UTerm n -> Clos -> Type
data EvalBig e t v where
  EVar :: EvalBig e ('UVar x) (lookupEnv e x)
