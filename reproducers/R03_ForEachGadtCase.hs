{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, StandaloneKindSignatures, TypeOperators #-}
-- | Minimal reproducer (Serokell R03):
-- Matching a retained `foreach` binder over an indexed GADT (`Term 'CEmpty a`)
-- with `case m of` fails to refine the type-level index `m` to `'Lam n0`.
-- Blocks PLFA DeBruijn intrinsically-typed `progress`.
module R03_ForEachGadtCase where

import Data.Kind (Type)

data Ty = TNat | TArr Ty Ty
data Ctx = CEmpty | CExt Ctx Ty

data Lookup (g :: Ctx) (a :: Ty) where
  Z :: Lookup ('CExt g a) a
  S :: Lookup g a -> Lookup ('CExt g b) a

data Term (g :: Ctx) (a :: Ty) where
  Var  :: Lookup g a -> Term g a
  Lam  :: Term ('CExt g a) b -> Term g ('TArr a b)
  App  :: Term g ('TArr a b) -> Term g a -> Term g b
  Zero :: Term g 'TNat
  Suc  :: Term g 'TNat -> Term g 'TNat

type Value :: forall (g :: Ctx) (a :: Ty). Term g a -> Type
data Value m where
  VLam  :: Value ('Lam n)
  VZero :: Value 'Zero
  VSuc  :: Value v -> Value ('Suc v)

type IsVal :: forall (a :: Ty). Term 'CEmpty a -> Type
data IsVal m where
  YesVal :: Value m -> IsVal m
  NotVal :: IsVal m

checkCase :: forall (a :: Ty). foreach (m :: Term 'CEmpty a) -> IsVal m
checkCase m = case m of
  Var x   -> case x of {}
  Lam _   -> YesVal VLam
  App _ _ -> NotVal
  Zero    -> YesVal VZero
  Suc n   -> case checkCase n of
    YesVal v -> YesVal (VSuc v)
    NotVal   -> NotVal
