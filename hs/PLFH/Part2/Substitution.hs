-- Generated from content/part2/Substitution.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
{-# LINE 15 "content/part2/Substitution.md" #-}
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
  , zShift
  , subIdL
  , subApp
  ) where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Size (Size (..))
import PLFH.Part2.Untyped
  ( Fin (..)
  , UTerm (..)
  , extU
  , extsU
  , renameU
  , substU
  )

{-# LINE 49 "content/part2/Substitution.md" #-}
-- | A simultaneous renaming from scope depth `m` to scope depth `n`.
type Rename (m :: Size) (n :: Size) = Fin m -> Fin n

-- | A simultaneous substitution mapping variables in depth `m` to terms in depth `n`.
type Subst (m :: Size) (n :: Size) = Fin m -> UTerm n

-- | Identity substitution: maps each variable to itself.
ids :: Subst m m
ids = UVar

-- | Shift renaming: increments every de Bruijn variable by one (`S_`).
shift :: Rename m ('Succ m)
shift = FS

-- | Lift a renaming to a substitution.
ren :: Rename m n -> Subst m n
ren rho x = UVar (rho x)

-- | Extend a substitution with a new term for variable 0 (`M • σ`).
consSubst :: UTerm n -> Subst m n -> Subst ('Succ m) n
consSubst t _     FZ     = t
consSubst _ sigma (FS x) = sigma x

-- | Sequential composition of substitutions (`σ ⨟ τ`).
seqSubst :: Subst m n -> Subst n p -> Subst m p
seqSubst sigma tau x = substU tau (sigma x)

{-# LINE 83 "content/part2/Substitution.md" #-}
-- | Head law: `(t • σ) 0 = t`.
subHead :: UTerm n -> Subst m n -> UTerm n
subHead t sigma = consSubst t sigma FZ

-- | Tail law: `(t • σ) (FS x) = σ x`.
subTail :: UTerm n -> Subst m n -> Fin m -> UTerm n
subTail t sigma x = consSubst t sigma (FS x)

-- | Shifting variable 0 after cons returns the original substitution on `x`.
zShift :: UTerm n -> Subst m n -> Fin m -> UTerm n
zShift t sigma x = consSubst t sigma (shift x)

-- | Left identity on variables: `substU sigma (UVar x) = sigma x`.
subIdL :: Subst m n -> Fin m -> UTerm n
subIdL sigma x = substU sigma (UVar x)

-- | Distributing substitution over application.
subApp :: Subst m n -> UTerm m -> UTerm m -> UTerm n
subApp sigma l m = substU sigma (UApp l m)
