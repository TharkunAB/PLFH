-- Generated from content/part2/DeBruijn.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
{-# LINE 13 "content/part2/DeBruijn.md" #-}
module PLFH.Part2.DeBruijn
  ( Ty (..)
  , Ctx (..)
  , Lookup (..)
  , Term (..)
  , ext
  , rename
  , exts
  , subst
  , substSingle
  , termTwo
  , Value (..)
  , Step (..)
  , Progress (..)
  , valZero
  ) where

import Data.Kind (Type)

{-# LINE 50 "content/part2/DeBruijn.md" #-}
-- | Simple types: natural numbers and functions.
data Ty = TNat | TArr Ty Ty
  deriving (Show)

-- | Nameless typing contexts.
data Ctx = CEmpty | CExt Ctx Ty

-- | Intrinsically typed de Bruijn indices (Γ ∋ A).
data Lookup (g :: Ctx) (a :: Ty) where
  Z :: Lookup ('CExt g a) a
  S :: Lookup g a -> Lookup ('CExt g b) a

{-# LINE 66 "content/part2/DeBruijn.md" #-}
-- | Intrinsically typed STLC terms with naturals, case, and μ-recursion.
data Term (g :: Ctx) (a :: Ty) where
  Var  :: Lookup g a -> Term g a
  Lam  :: Term ('CExt g a) b -> Term g ('TArr a b)
  App  :: Term g ('TArr a b) -> Term g a -> Term g b
  Zero :: Term g 'TNat
  Suc  :: Term g 'TNat -> Term g 'TNat
  Case :: Term g 'TNat -> Term g a -> Term ('CExt g 'TNat) a -> Term g a
  Mu   :: Term ('CExt g a) a -> Term g a

-- | Closed intrinsically-typed numeral 2.
termTwo :: Term g 'TNat
termTwo = Suc (Suc Zero)

{-# LINE 88 "content/part2/DeBruijn.md" #-}
-- | Extend a variable renaming under a binder.
ext :: (forall a. Lookup g a -> Lookup d a)
    -> (forall a. Lookup ('CExt g b) a -> Lookup ('CExt d b) a)
ext _   Z     = Z
ext rho (S x) = S (rho x)

-- | Simultaneous renaming on intrinsically typed terms.
rename :: (forall a. Lookup g a -> Lookup d a) -> Term g b -> Term d b
rename rho (Var x)      = Var (rho x)
rename rho (Lam n)      = Lam (rename (ext rho) n)
rename rho (App l m)    = App (rename rho l) (rename rho m)
rename _   Zero         = Zero
rename rho (Suc m)      = Suc (rename rho m)
rename rho (Case l m n) = Case (rename rho l) (rename rho m) (rename (ext rho) n)
rename rho (Mu n)       = Mu (rename (ext rho) n)

-- | Extend a simultaneous substitution under a binder.
exts :: (forall a. Lookup g a -> Term d a)
     -> (forall a. Lookup ('CExt g b) a -> Term ('CExt d b) a)
exts _     Z     = Var Z
exts sigma (S x) = rename S (sigma x)

-- | Simultaneous substitution on intrinsically typed terms.
subst :: (forall a. Lookup g a -> Term d a) -> Term g b -> Term d b
subst sigma (Var x)      = sigma x
subst sigma (Lam n)      = Lam (subst (exts sigma) n)
subst sigma (App l m)    = App (subst sigma l) (subst sigma m)
subst _     Zero         = Zero
subst sigma (Suc m)      = Suc (subst sigma m)
subst sigma (Case l m n) = Case (subst sigma l) (subst sigma m) (subst (exts sigma) n)
subst sigma (Mu n)       = Mu (subst (exts sigma) n)

-- | Substitute a single closed/open term `w` for variable `Z` in `n` (N [ W ]).
substSingle :: Term ('CExt g a) b -> Term g a -> Term g b
substSingle n w = subst (\case { Z -> w; S x -> Var x }) n

{-# LINE 133 "content/part2/DeBruijn.md" #-}
-- | Values indexed by promoted intrinsically-typed terms!
type Value :: forall (g :: Ctx) (a :: Ty). Term g a -> Type
data Value m where
  VLam  :: Value ('Lam n)
  VZero :: Value 'Zero
  VSuc  :: Value v -> Value ('Suc v)

-- | Type-preserving one-step reduction indexed by promoted `Term g a`.
type Step :: forall (g :: Ctx) (a :: Ty). Term g a -> Term g a -> Type
data Step m n where
  XiApp1   :: Step l l' -> Step ('App l m) ('App l' m)
  XiApp2   :: Value v -> Step m m' -> Step ('App v m) ('App v m')
  BetaLam  :: Value w -> Step ('App ('Lam n) w) (substSingle n w)
  XiSuc    :: Step m m' -> Step ('Suc m) ('Suc m')
  XiCase   :: Step l l' -> Step ('Case l m n) ('Case l' m n)
  BetaZero :: Step ('Case 'Zero m n) m
  BetaSuc  :: Value v -> Step ('Case ('Suc v) m n) (substSingle n v)
  BetaMu   :: Step ('Mu n) (substSingle n ('Mu n))

-- | Progress witness indexed by a closed intrinsically-typed term.
type Progress :: forall (a :: Ty). Term 'CEmpty a -> Type
data Progress m where
  PStep :: Step m n -> Progress m
  PDone :: Value m  -> Progress m

-- | Concrete witness that `Zero` is already a value.
valZero :: Progress ('Zero :: Term 'CEmpty 'TNat)
valZero = PDone VZero
