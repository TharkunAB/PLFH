-- Generated from content/part2/Untyped.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
{-# LINE 13 "content/part2/Untyped.md" #-}
module PLFH.Part2.Untyped
  ( Fin (..)
  , UTerm (..)
  , extU
  , renameU
  , extsU
  , substU
  , substSingleU
  , Neutral (..)
  , Normal (..)
  , BetaStep (..)
  , BetaSteps (..)
  , idTerm
  , idIsNormal
  , omegaTerm
  ) where

import Data.Kind (Type)
import HaskLib.Nat (Nat (..))

{-# LINE 42 "content/part2/Untyped.md" #-}
-- | Finite set {0, ..., n-1}: well-scoped de Bruijn variables in depth `n`.
data Fin (n :: Nat) where
  FZ :: Fin ('Succ n)
  FS :: Fin n -> Fin ('Succ n)

-- | Well-scoped untyped lambda terms with `n` free variables in scope.
data UTerm (n :: Nat) where
  UVar :: Fin n -> UTerm n
  ULam :: UTerm ('Succ n) -> UTerm n
  UApp :: UTerm n -> UTerm n -> UTerm n

-- | Closed identity term: λx. x.
idTerm :: UTerm 'Zero
idTerm = ULam (UVar FZ)

-- | The classic diverging term Ω = (λx. x x) (λx. x x).
omegaTerm :: UTerm 'Zero
omegaTerm = UApp selfApp selfApp
  where
    selfApp :: UTerm 'Zero
    selfApp = ULam (UApp (UVar FZ) (UVar FZ))

{-# LINE 68 "content/part2/Untyped.md" #-}
-- | Lift a variable renaming under a lambda binder.
extU :: (Fin m -> Fin n) -> Fin ('Succ m) -> Fin ('Succ n)
extU _   FZ     = FZ
extU rho (FS x) = FS (rho x)

-- | Simultaneous renaming on well-scoped untyped terms.
renameU :: (Fin m -> Fin n) -> UTerm m -> UTerm n
renameU rho (UVar x)   = UVar (rho x)
renameU rho (ULam b)   = ULam (renameU (extU rho) b)
renameU rho (UApp l m) = UApp (renameU rho l) (renameU rho m)

-- | Lift a substitution under a lambda binder.
extsU :: (Fin m -> UTerm n) -> Fin ('Succ m) -> UTerm ('Succ n)
extsU _     FZ     = UVar FZ
extsU sigma (FS x) = renameU FS (sigma x)

-- | Simultaneous capture-avoiding substitution on well-scoped untyped terms.
substU :: (Fin m -> UTerm n) -> UTerm m -> UTerm n
substU sigma (UVar x)   = sigma x
substU sigma (ULam b)   = ULam (substU (extsU sigma) b)
substU sigma (UApp l m) = UApp (substU sigma l) (substU sigma m)

-- | Single-variable substitution `b [ w ]`.
substSingleU :: UTerm ('Succ n) -> UTerm n -> UTerm n
substSingleU b w = substU (\case { FZ -> w; FS x -> UVar x }) b

{-# LINE 102 "content/part2/Untyped.md" #-}
-- | Neutral terms: a variable applied to zero or more normal arguments.
type Neutral :: forall (n :: Nat). UTerm n -> Type
data Neutral t where
  NVar :: Neutral ('UVar x)
  NApp :: Neutral l -> Normal m -> Neutral ('UApp l m)

-- | Normal forms under full β-reduction (no β-redexes anywhere).
type Normal :: forall (n :: Nat). UTerm n -> Type
data Normal t where
  NNeu :: Neutral t -> Normal t
  NLam :: Normal b  -> Normal ('ULam b)

-- | Full β-reduction (including under lambdas and in neutral arguments).
type BetaStep :: forall (n :: Nat). UTerm n -> UTerm n -> Type
data BetaStep t t' where
  XiApp1 :: BetaStep l l' -> BetaStep ('UApp l m) ('UApp l' m)
  XiApp2 :: BetaStep m m' -> BetaStep ('UApp l m) ('UApp l m')
  XiLam  :: BetaStep b b' -> BetaStep ('ULam b) ('ULam b')
  Beta   :: BetaStep ('UApp ('ULam b) w) (substSingleU b w)

-- | Multi-step full β-reduction.
type BetaSteps :: forall (n :: Nat). UTerm n -> UTerm n -> Type
data BetaSteps t t' where
  BRefl :: BetaSteps t t
  BCons :: BetaStep s t -> BetaSteps t u -> BetaSteps s u

-- | Evidence that λx. x is in full normal form!
idIsNormal :: Normal ('ULam ('UVar 'FZ) :: UTerm 'Zero)
idIsNormal = NLam (NNeu NVar)
