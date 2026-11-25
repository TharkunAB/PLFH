{-# LANGUAGE DependentTypes #-}
-- | Minimal provider for `R13_SubstSingleNamedHelperOpenEq.hs` (skipped as ReproOps*).
-- Factors the single-variable substitution callback out as a named helper `singleSubst`
-- so downstream modules (like `PLFH.Part2.Bisimulation.simSubstSingle`) can apply the
-- general simultaneous-substitution lemma `simSubst` directly to `M.subst (M.singleSubst w) n`.
module ReproOpsSubstHelper where

data Ty = TNat | TArr Ty Ty
data Ctx = CEmpty | CExt Ctx Ty

data Lookup (g :: Ctx) (a :: Ty) where
  Z :: Lookup (CExt g a) a
  S :: Lookup g a -> Lookup (CExt g b) a

data Term (g :: Ctx) (a :: Ty) where
  Var  :: Lookup g a -> Term g a
  Lam  :: Term (CExt g a) b -> Term g (TArr a b)
  App  :: Term g (TArr a b) -> Term g a -> Term g b
  Zero :: Term g TNat

weakenLookup :: forall d b a. Lookup d a -> Lookup (CExt d b) a
weakenLookup x = S x

ext :: (forall a. Lookup g a -> Lookup d a)
    -> (forall a. Lookup (CExt g b) a -> Lookup (CExt d b) a)
ext _ Z     = Z
ext r (S x) = S (r x)

rename :: (forall a. Lookup g a -> Lookup d a) -> Term g b -> Term d b
rename r (Var x)   = Var (r x)
rename r (Lam n)   = Lam (rename (ext r) n)
rename r (App l m) = App (rename r l) (rename r m)
rename _ Zero      = Zero

exts :: forall g d b.
        (forall a. Lookup g a -> Term d a)
     -> (forall a. Lookup (CExt g b) a -> Term (CExt d b) a)
exts _ Z     = Var Z
exts s (S x) = rename weakenLookup (s x)

subst :: (forall a. Lookup g a -> Term d a) -> Term g b -> Term d b
subst s (Var x)   = s x
subst s (Lam n)   = Lam (subst (exts s) n)
subst s (App l m) = App (subst s l) (subst s m)
subst _ Zero      = Zero

singleSubst :: forall g a. Term g a -> (forall b. Lookup (CExt g a) b -> Term g b)
singleSubst w Z     = w
singleSubst _ (S x) = Var x

substSingle :: Term (CExt g a) b -> Term g a -> Term g b
substSingle n w = subst (singleSubst w) n
