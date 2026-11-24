{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (Serokell R03):
-- Unpacking `Just (MkTyped t m)` inside a `case` alternative and then
-- refining `t` via `case t of` fails with GHC-83605:
--   Retained constructor refinement does not support this type yet: Term g t
-- (Contrast: matching `(MkTyped t m)` directly in the function head passes!)
module R03_CaseRefinementMultiIndexGadt where

data Ty = TNat | TArr Ty Ty
data Ctx = CEmpty | CExt Ctx Ty

data Term (g :: Ctx) (a :: Ty) where
  TZero :: Term g 'TNat
  App   :: Term g ('TArr a b) -> Term g a -> Term g b

data Typed (g :: Ctx) where
  MkTyped :: foreach (a :: Ty) -> Term g a -> Typed g

data ArrTerm (g :: Ctx) where
  MkArrTerm :: foreach (a :: Ty) -> foreach (b :: Ty) -> Term g ('TArr a b) -> ArrTerm g

refineNested :: foreach (g :: Ctx) -> Maybe (Typed g) -> Maybe (ArrTerm g)
refineNested _ mt = case mt of
  Nothing -> Nothing
  Just (MkTyped t m) -> case t of
    TNat     -> Nothing
    TArr a b -> Just (MkArrTerm a b m)
