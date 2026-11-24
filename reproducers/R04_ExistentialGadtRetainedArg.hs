{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs, PolyKinds #-}
{-# LANGUAGE RankNTypes, StandaloneKindSignatures, TypeAbstractions, TypeApplications #-}
-- | Minimal reproducer (Serokell R04 / R03 follow-up to `fixed/R04_IndexedForEachCtorField.hs`;
-- GHC Proposal #378):
-- Wave 2 Lane 1 (`03b7bb9a00`) unlocked `foreach` constructor fields for indexed
-- GADTs and vanilla-return constructors (`UTerm n`, `Fin n`), unlocking
-- `Untyped.evalNormal` completely. However, passing a GADT constructor with an
-- *existential* type variable (`App :: Term g (TArr a b) -> Term g a -> Term g b`)
-- as a retained `foreach` argument still fails with `GHC-83605` ("GHC cannot use
-- this expression as a retained index"), blocking intrinsically-typed
-- `DeBruijnProgress.eval`.
module R04_ExistentialGadtRetainedArg where

import Data.Kind (Type)

data Ty = TNat | TArr Ty Ty
data Ctx = CEmpty | CExt Ctx Ty

data Term (g :: Ctx) (a :: Ty) where
  Zero :: Term g TNat
  Lam  :: Term (CExt g a) b -> Term g (TArr a b)
  App  :: Term g (TArr a b) -> Term g a -> Term g b

type Step :: forall (g :: Ctx) (a :: Ty). Term g a -> Term g a -> Type
data Step m n where
  XiApp1 :: Step l l' -> Step (App l m) (App l' m)

type Progress :: forall (a :: Ty). Term CEmpty a -> Type
data Progress m where
  PStep :: foreach (n :: Term CEmpty a) -> Step m n -> Progress m

appLeft :: forall a b.
           foreach (l :: Term CEmpty (TArr a b))
        -> foreach (l' :: Term CEmpty (TArr a b))
        -> foreach (m :: Term CEmpty a)
        -> Step l l' -> Progress (App l m)
appLeft _ l' m s = PStep (App l' m) (XiApp1 s)
