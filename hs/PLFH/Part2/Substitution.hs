-- Generated from content/part2/Substitution.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DependentTypes #-}
{-# LINE 40 "content/part2/Substitution.md" #-}
module PLFH.Part2.Substitution
  ( Rename
  , Subst
  , ids
  , shift
  , ren
  , consSubst
  , seqSubst
  , subHead
  , subTail
  , subIdL
  , subApp
  ) where

import HaskLib.Nat (Nat (..))
import PLFH.Part2.Untyped
  ( Fin (..)
  , UTerm (..)
  , extU
  , extsU
  , renameU
  , substU
  )

{-# LINE 86 "content/part2/Substitution.md" #-}
-- | A simultaneous renaming from scope depth `m` to scope depth `n`.
type Rename (m :: Nat) (n :: Nat) = Fin m -> Fin n

-- | A simultaneous substitution mapping variables in depth `m` to terms in depth `n`.
type Subst (m :: Nat) (n :: Nat) = Fin m -> UTerm n

-- | Identity substitution: maps each variable to itself.
ids :: Subst m m
ids = UVar

-- | Shift renaming: increments every de Bruijn variable by one (`↑` / `S_`).
shift :: Rename m (Succ m)
shift = FS

-- | Lift a renaming to a substitution.
ren :: Rename m n -> Subst m n
ren rho x = UVar (rho x)

-- | Extend a substitution with a new term for variable 0 (`M • σ`).
consSubst :: UTerm n -> Subst m n -> Subst (Succ m) n
consSubst t _     FZ     = t
consSubst _ sigma (FS x) = sigma x

-- | Sequential composition of substitutions (`σ ⨟ τ`).
seqSubst :: Subst m n -> Subst n p -> Subst m p
seqSubst sigma tau x = substU tau (sigma x)

{-# LINE 121 "content/part2/Substitution.md" #-}
-- | Head lookup: `(t • σ) 0` computes to `t`.
subHead :: UTerm n -> Subst m n -> UTerm n
subHead t sigma = consSubst t sigma FZ

-- | Tail lookup: `(t • σ) (FS x)` computes to `σ x`.
subTail :: UTerm n -> Subst m n -> Fin m -> UTerm n
subTail t sigma x = consSubst t sigma (FS x)

-- | Left identity on variables: `substU sigma (UVar x)` computes to `sigma x`.
subIdL :: Subst m n -> Fin m -> UTerm n
subIdL sigma x = substU sigma (UVar x)

-- | Distributing substitution over application.
subApp :: Subst m n -> UTerm m -> UTerm m -> UTerm n
subApp sigma l m = substU sigma (UApp l m)
