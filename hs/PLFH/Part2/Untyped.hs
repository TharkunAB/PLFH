-- Generated from content/part2/Untyped.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
{-# LINE 36 "content/part2/Untyped.md" #-}
module PLFH.Part2.Untyped
  ( Fin (..)
  , UTerm (..)
  , extU
  , renameU
  , extsU
  , substU
  , substSingleU
  , BumpFin (..)
  , ShiftU (..)
  , RemoveFin (..)
  , SubstAtU (..)
  , Neutral (..)
  , Normal (..)
  , BetaStep (..)
  , BetaSteps (..)
  , IdTerm
  , SelfApp
  , OmegaTerm
  , idTerm
  , idIsNormal
  , omegaTerm
  , idAppStep
  , omegaStep
  ) where

import Data.Kind (Type)
import HaskLib.Nat (Nat (..))

{-# LINE 78 "content/part2/Untyped.md" #-}
-- | Finite set {0, ..., n-1}: well-scoped de Bruijn variables in depth `n`.
data Fin (n :: Nat) where
  FZ :: Fin (Succ n)
  FS :: Fin n -> Fin (Succ n)

-- | Well-scoped untyped lambda terms with `n` free variables in scope.
data UTerm (n :: Nat) where
  UVar :: Fin n -> UTerm n
  ULam :: UTerm (Succ n) -> UTerm n
  UApp :: UTerm n -> UTerm n -> UTerm n

-- | Closed identity term: λx. x.
idTerm :: UTerm Zero
idTerm = ULam (UVar FZ)

-- | The classic diverging term Ω = (λx. x x) (λx. x x).
omegaTerm :: UTerm Zero
omegaTerm = UApp selfApp selfApp
  where
    selfApp :: UTerm Zero
    selfApp = ULam (UApp (UVar FZ) (UVar FZ))

{-# LINE 115 "content/part2/Untyped.md" #-}
-- | Lift a variable renaming under a lambda binder.
extU :: (Fin m -> Fin n) -> Fin (Succ m) -> Fin (Succ n)
extU _   FZ     = FZ
extU rho (FS x) = FS (rho x)

-- | Simultaneous renaming on well-scoped untyped terms.
renameU :: (Fin m -> Fin n) -> UTerm m -> UTerm n
renameU rho (UVar x)   = UVar (rho x)
renameU rho (ULam b)   = ULam (renameU (extU rho) b)
renameU rho (UApp l m) = UApp (renameU rho l) (renameU rho m)

-- | Lift a substitution under a lambda binder.
extsU :: (Fin m -> UTerm n) -> Fin (Succ m) -> UTerm (Succ n)
extsU _     FZ     = UVar FZ
extsU sigma (FS x) = renameU FS (sigma x)

-- | Simultaneous capture-avoiding substitution on well-scoped untyped terms.
substU :: (Fin m -> UTerm n) -> UTerm m -> UTerm n
substU sigma (UVar x)   = sigma x
substU sigma (ULam b)   = ULam (substU (extsU sigma) b)
substU sigma (UApp l m) = UApp (substU sigma l) (substU sigma m)

-- | Single-variable substitution `b [ w ]`.
substSingleU :: UTerm (Succ n) -> UTerm n -> UTerm n
substSingleU b w = substU (\case { FZ -> w; FS x -> UVar x }) b

{-# LINE 172 "content/part2/Untyped.md" #-}
-- | Shift a variable `x :: Fin n` up by one slot at cutoff `c :: Fin (Succ n)`.
type BumpFin :: forall (n :: Nat). Fin (Succ n) -> Fin n -> Fin (Succ n) -> Type
data BumpFin c x y where
  BumpZ  :: BumpFin FZ x (FS x)
  BumpSZ :: BumpFin (FS c) FZ FZ
  BumpSS :: BumpFin c x y -> BumpFin (FS c) (FS x) (FS y)

-- | Capture-avoiding weakening: shift all free variables >= `c` up by one.
type ShiftU :: forall (n :: Nat). Fin (Succ n) -> UTerm n -> UTerm (Succ n) -> Type
data ShiftU c m m' where
  ShiftVar :: BumpFin c x y -> ShiftU c (UVar x) (UVar y)
  ShiftLam :: ShiftU (FS c) b b' -> ShiftU c (ULam b) (ULam b')
  ShiftApp :: ShiftU c l l' -> ShiftU c m m' -> ShiftU c (UApp l m) (UApp l' m')

-- | Remove slot `c` from any distinct variable `x /= c` in `Fin (Succ n)`.
type RemoveFin :: forall (n :: Nat). Fin (Succ n) -> Fin (Succ n) -> Fin n -> Type
data RemoveFin c x y where
  RemGt :: RemoveFin FZ (FS y) y
  RemLt :: RemoveFin (FS c) FZ FZ
  RemSS :: RemoveFin c x y -> RemoveFin (FS c) (FS x) (FS y)

-- | Deterministic relational single-variable substitution `m [ c := w ] ↦ m'`.
type SubstAtU :: forall (n :: Nat). Fin (Succ n) -> UTerm n -> UTerm (Succ n) -> UTerm n -> Type
data SubstAtU c w m m' where
  SUEq  :: SubstAtU c w (UVar c) w
  SUNeq :: RemoveFin c x y -> SubstAtU c w (UVar x) (UVar y)
  SULam :: ShiftU FZ w w' -> SubstAtU (FS c) w' b b' -> SubstAtU c w (ULam b) (ULam b')
  SUApp :: SubstAtU c w l l' -> SubstAtU c w m m' -> SubstAtU c w (UApp l m) (UApp l' m')

{-# LINE 223 "content/part2/Untyped.md" #-}
-- | Neutral terms: a variable applied to zero or more normal arguments.
type Neutral :: forall (n :: Nat). UTerm n -> Type
data Neutral t where
  NVar :: Neutral (UVar x)
  NApp :: Neutral l -> Normal m -> Neutral (UApp l m)

-- | Normal forms under full β-reduction (no β-redexes anywhere).
type Normal :: forall (n :: Nat). UTerm n -> Type
data Normal t where
  NNeu :: Neutral t -> Normal t
  NLam :: Normal b  -> Normal (ULam b)

-- | Full β-reduction (including under lambdas and in neutral arguments).
type BetaStep :: forall (n :: Nat). UTerm n -> UTerm n -> Type
data BetaStep t t' where
  XiApp1 :: BetaStep l l' -> BetaStep (UApp l m) (UApp l' m)
  XiApp2 :: BetaStep m m' -> BetaStep (UApp l m) (UApp l m')
  XiLam  :: BetaStep b b' -> BetaStep (ULam b) (ULam b')
  Beta   :: forall (n :: Nat) (w :: UTerm n) (b :: UTerm (Succ n)) (r :: UTerm n).
            SubstAtU FZ w b r -> BetaStep (UApp (ULam b) w) r

-- | Multi-step full β-reduction.
type BetaSteps :: forall (n :: Nat). UTerm n -> UTerm n -> Type
data BetaSteps t t' where
  BRefl :: BetaSteps t t
  BCons :: BetaStep s t -> BetaSteps t u -> BetaSteps s u

{-# LINE 257 "content/part2/Untyped.md" #-}
-- | Promoted closed terms: λx. x, λx. x x, and Ω = (λx. x x) (λx. x x).
type IdTerm    = (ULam (UVar FZ) :: UTerm Zero)
type SelfApp   = (ULam (UApp (UVar FZ) (UVar FZ)) :: UTerm Zero)
type OmegaTerm = (UApp SelfApp SelfApp :: UTerm Zero)

-- | Evidence that λx. x is in full normal form!
idIsNormal :: Normal IdTerm
idIsNormal = NLam (NNeu NVar)

-- | Concrete sound β-step: (λx. x) (λx. x) —→ (λx. x).
idAppStep :: BetaStep (UApp IdTerm IdTerm) IdTerm
idAppStep = Beta SUEq

-- | Concrete sound β-step: Ω —→ Ω!
omegaStep :: BetaStep OmegaTerm OmegaTerm
omegaStep = Beta (SUApp SUEq SUEq)
