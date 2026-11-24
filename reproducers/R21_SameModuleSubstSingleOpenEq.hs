{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, PolyKinds #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, StandaloneKindSignatures, TypeApplications, TypeOperators #-}
-- | Minimal reproducer (Serokell R13 / R16 / R21; GHC Proposals #378 & #509):
-- Intrinsically-typed single-variable substitution `substSingle` publishes
-- checked equations cross-module via `-fwrite-source-equations` (used by
-- `clients/PLFH/Part2/DeBruijnProgress.hs`), but mentioning `substSingle` in a
-- type within the *same* defining module fails with `GHC-68947`, forcing
-- `DeBruijn.md` and `More.md` to split `Step` and `progress` into separate
-- client modules.
module R21_SameModuleSubstSingleOpenEq where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))

data Ty = TNat | TArr Ty Ty
data Ctx = CEmpty | CExt Ctx Ty

data Lookup (g :: Ctx) (a :: Ty) where
  Z :: Lookup (CExt g a) a
  S :: Lookup g a -> Lookup (CExt g b) a

data Term (g :: Ctx) (a :: Ty) where
  Var :: Lookup g a -> Term g a
  Lam :: Term (CExt g a) b -> Term g (TArr a b)
  App :: Term g (TArr a b) -> Term g a -> Term g b

ext :: (forall a. Lookup g a -> Lookup d a) -> Lookup (CExt g b) a -> Lookup (CExt d b) a
ext _ Z     = Z
ext r (S x) = S (r x)

rename :: (forall a. Lookup g a -> Lookup d a) -> Term g a -> Term d a
rename r (Var x)   = Var (r x)
rename r (Lam n)   = Lam (rename (ext r) n)
rename r (App l m) = App (rename r l) (rename r m)

exts :: (forall a. Lookup g a -> Term d a) -> Lookup (CExt g b) a -> Term (CExt d b) a
exts _ Z     = Var Z
exts s (S x) = rename S (s x)

subst :: (forall a. Lookup g a -> Term d a) -> Term g a -> Term d a
subst s (Var x)   = s x
subst s (Lam n)   = Lam (subst (exts s) n)
subst s (App l m) = App (subst s l) (subst s m)

substSingle :: forall g b a. Term (CExt g b) a -> Term g b -> Term g a
substSingle m v = subst go m
  where
    go :: Lookup (CExt g b) x -> Term g x
    go Z     = v
    go (S x) = Var x

type Value :: forall (g :: Ctx) (a :: Ty). Term g a -> Type
data Value m where
  VLam :: Value (Lam n)

type Step :: forall (g :: Ctx) (a :: Ty). Term g a -> Term g a -> Type
data Step m n where
  BetaLam :: forall g a b (n :: Term (CExt g a) b) (w :: Term g a).
             Value w -> Step (App (Lam n) w) (substSingle n w)

betaShift :: Step @(CExt CEmpty TNat) @(TArr TNat (TArr TNat TNat))
               (App (Lam (Lam (Var (S Z)))) (Lam (Var (S Z))))
               (Lam (Lam (Var (S (S Z)))))
betaShift = BetaLam VLam

betaId :: forall g a (v :: Term g a).
          substSingle (Var Z) v :~: v
betaId = Refl
