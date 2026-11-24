{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, LambdaCase, PolyKinds, RankNTypes #-}
{-# OPTIONS_GHC -fwrite-source-equations #-}
-- | Minimal provider for `R13_DoubleBinderSubstClosure.hs` (skipped as ReproOps*).
-- Models `PLFH.Part2.More`'s `CaseLst`, which binds two variables simultaneously
-- via `ext (ext r)` / `exts (exts s)` and contracts via `substDouble`.
module ReproOpsDoubleSubst where

data Ty = TNat | TArr Ty Ty | TList Ty
data Ctx = CEmpty | CExt Ctx Ty

data Lookup (g :: Ctx) (a :: Ty) where
  Z :: Lookup (CExt g a) a
  S :: Lookup g a -> Lookup (CExt g b) a

data Term (g :: Ctx) (a :: Ty) where
  Var     :: Lookup g a -> Term g a
  Lam     :: Term (CExt g a) b -> Term g (TArr a b)
  App     :: Term g (TArr a b) -> Term g a -> Term g b
  Zero    :: Term g TNat
  Cons    :: Term g a -> Term g (TList a) -> Term g (TList a)
  CaseLst :: Term g (TList a) -> Term g b
          -> Term (CExt (CExt g a) (TList a)) b -> Term g b

ext :: (forall a. Lookup g a -> Lookup d a)
    -> (forall a. Lookup (CExt g b) a -> Lookup (CExt d b) a)
ext _ Z     = Z
ext r (S x) = S (r x)

rename :: (forall a. Lookup g a -> Lookup d a) -> Term g b -> Term d b
rename r (Var x)          = Var (r x)
rename r (Lam n)          = Lam (rename (ext r) n)
rename r (App l m)        = App (rename r l) (rename r m)
rename _ Zero             = Zero
rename r (Cons x xs)      = Cons (rename r x) (rename r xs)
rename r (CaseLst xs n c) = CaseLst (rename r xs) (rename r n) (rename (ext (ext r)) c)

exts :: (forall a. Lookup g a -> Term d a)
     -> (forall a. Lookup (CExt g b) a -> Term (CExt d b) a)
exts _ Z     = Var Z
exts s (S x) = rename S (s x)

subst :: (forall a. Lookup g a -> Term d a) -> Term g b -> Term d b
subst s (Var x)          = s x
subst s (Lam n)          = Lam (subst (exts s) n)
subst s (App l m)        = App (subst s l) (subst s m)
subst _ Zero             = Zero
subst s (Cons x xs)      = Cons (subst s x) (subst s xs)
subst s (CaseLst xs n c) = CaseLst (subst s xs) (subst s n) (subst (exts (exts s)) c)

substSingle :: Term (CExt g a) b -> Term g a -> Term g b
substSingle n w = subst (\case { Z -> w; S x -> Var x }) n

substDouble :: Term (CExt (CExt g a) b) c -> Term g a -> Term g b -> Term g c
substDouble n v w = subst (\case { Z -> w; S Z -> v; S (S x) -> Var x }) n
