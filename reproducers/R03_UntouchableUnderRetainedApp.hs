{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (Serokell R03):
-- Constructing `MkTyped b (App lArr m)` inside a GADT equality match
-- (`Refl`) under a retained `foreach (g :: Ctx)` fails with GHC-83865:
--   `g0` / `a0` is untouchable inside the constraints: () bound by a retained application
-- Explicitly passing `App @g @a @b lArr m` compiles cleanly.
module R03_UntouchableUnderRetainedApp where

import Data.Type.Equality ((:~:) (Refl))

data Ty = TNat | TArr Ty Ty
data Ctx = CEmpty | CExt Ctx Ty

data Term (g :: Ctx) (a :: Ty) where
  App :: Term g ('TArr a b) -> Term g a -> Term g b

data Typed (g :: Ctx) where
  MkTyped :: foreach (a :: Ty) -> Term g a -> Typed g

packAppEq :: foreach (g :: Ctx) -> foreach (a :: Ty) -> foreach (a' :: Ty) -> foreach (b :: Ty)
          -> a :~: a' -> Term g ('TArr a b) -> Term g a' -> Typed g
packAppEq _ _ _ b Refl lArr m = MkTyped b (App lArr m)
