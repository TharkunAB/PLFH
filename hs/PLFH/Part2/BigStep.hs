-- Generated from content/part2/BigStep.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
{-# LINE 15 "content/part2/BigStep.md" #-}
module PLFH.Part2.BigStep
  ( Env (..)
  , Clos (..)
  , lookupEnv
  , EnvLookup (..)
  , EvalBig (..)
  , idClos
  , evalIdApp
  , evalConstOmega
  ) where

import Data.Kind (Type)
import HaskLib.Size (Size (..))
import PLFH.Part2.Untyped (Fin (..), UTerm (..))

{-# LINE 45 "content/part2/BigStep.md" #-}
-- | Closure environment matching de Bruijn scope depth `n`.
data Env (n :: Size) where
  ENil  :: Env 'Zero
  ECons :: Clos -> Env n -> Env ('Succ n)

-- | A call-by-name closure pairing a term of depth `n` with its environment.
data Clos where
  MkClos :: UTerm n -> Env n -> Clos

-- | Runtime lookup of a well-scoped de Bruijn variable in a matching environment.
lookupEnv :: Env n -> Fin n -> Clos
lookupEnv (ECons c _) FZ     = c
lookupEnv (ECons _ e) (FS x) = lookupEnv e x

-- | Closure for the closed identity function λx. x.
idClos :: Clos
idClos = MkClos (ULam (UVar FZ)) ENil

{-# LINE 79 "content/part2/BigStep.md" #-}
-- | Relational environment lookup: variable `x` maps to closure `c` in `e`.
type EnvLookup :: forall (n :: Size). Env n -> Fin n -> Clos -> Type
data EnvLookup e x c where
  ELZ :: EnvLookup ('ECons c e) 'FZ c
  ELS :: EnvLookup e x c -> EnvLookup ('ECons c' e) ('FS x) c

-- | Call-by-name big-step evaluation: in environment `e`, term `t` evaluates to closure `v`.
type EvalBig :: forall (n :: Size). Env n -> UTerm n -> Clos -> Type
data EvalBig e t v where
  EVar :: EnvLookup e x ('MkClos m d) -> EvalBig d m v -> EvalBig e ('UVar x) v
  ELam :: EvalBig e ('ULam b) ('MkClos ('ULam b) e)
  EApp :: EvalBig e l ('MkClos ('ULam b) d)
       -> EvalBig ('ECons ('MkClos m e) d) b w
       -> EvalBig e ('UApp l m) w

-- | Concrete call-by-name derivation: (λx. x) (λy. y) ⇓ <λy. y, []>.
evalIdApp :: EvalBig 'ENil
                     ('UApp ('ULam ('UVar 'FZ)) ('ULam ('UVar 'FZ)))
                     ('MkClos ('ULam ('UVar 'FZ)) 'ENil)
evalIdApp = EApp ELam (EVar ELZ ELam)

-- | PLFA BigStep exercise: (λx y. x) Ω terminates under call-by-name
-- because Ω is captured unevaluated in the closure environment!
evalConstOmega :: EvalBig 'ENil
  ('UApp ('ULam ('ULam ('UVar ('FS 'FZ))))
         ('UApp ('ULam ('UApp ('UVar 'FZ) ('UVar 'FZ)))
                ('ULam ('UApp ('UVar 'FZ) ('UVar 'FZ)))))
  ('MkClos ('ULam ('UVar ('FS 'FZ)))
           ('ECons ('MkClos ('UApp ('ULam ('UApp ('UVar 'FZ) ('UVar 'FZ)))
                                   ('ULam ('UApp ('UVar 'FZ) ('UVar 'FZ)))) 'ENil) 'ENil))
evalConstOmega = EApp ELam ELam
