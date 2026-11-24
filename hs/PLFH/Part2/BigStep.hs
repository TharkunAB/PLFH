-- Generated from content/part2/BigStep.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
{-# LINE 13 "content/part2/BigStep.md" #-}
module PLFH.Part2.BigStep
  ( Env (..)
  , Clos (..)
  , lookupEnv
  , EvalBig (..)
  , idClos
  , evalIdApp
  ) where

import Data.Kind (Type)
import HaskLib.Size (Size (..))
import PLFH.Part2.Untyped (Fin (..), UTerm (..))

{-# LINE 38 "content/part2/BigStep.md" #-}
-- | Closure environment matching de Bruijn scope depth `n`.
data Env (n :: Size) where
  ENil  :: Env 'Zero
  ECons :: Clos -> Env n -> Env ('Succ n)

-- | A closure pairing an environment of depth `n` with a lambda body.
data Clos where
  MkClos :: Env n -> UTerm ('Succ n) -> Clos

-- | Runtime lookup of a well-scoped de Bruijn variable in a matching environment.
lookupEnv :: Env n -> Fin n -> Clos
lookupEnv (ECons c _) FZ     = c
lookupEnv (ECons _ e) (FS x) = lookupEnv e x

-- | Closure for the closed identity function λx. x.
idClos :: Clos
idClos = MkClos ENil (UVar FZ)

{-# LINE 64 "content/part2/BigStep.md" #-}
-- | Relational environment lookup: variable `x` maps to closure `c` in `e`.
type EnvLookup :: forall (n :: Size). Env n -> Fin n -> Clos -> Type
data EnvLookup e x c where
  ELZ :: EnvLookup ('ECons c e) 'FZ c
  ELS :: EnvLookup e x c -> EnvLookup ('ECons c' e) ('FS x) c

-- | Big-step evaluation: in environment `e`, term `t` evaluates to closure `v`.
type EvalBig :: forall (n :: Size). Env n -> UTerm n -> Clos -> Type
data EvalBig e t v where
  EVar :: EnvLookup e x c -> EvalBig e ('UVar x) c
  ELam :: EvalBig e ('ULam b) ('MkClos e b)
  EApp :: EvalBig e l ('MkClos e' b)
       -> EvalBig e m v
       -> EvalBig ('ECons v e') b w
       -> EvalBig e ('UApp l m) w

-- | Concrete big-step derivation: (λx. x) (λy. y) ⇓ <[], λy. y>.
evalIdApp :: EvalBig 'ENil
                     ('UApp ('ULam ('UVar 'FZ)) ('ULam ('UVar 'FZ)))
                     ('MkClos 'ENil ('UVar 'FZ))
evalIdApp = EApp ELam ELam (EVar ELZ)
