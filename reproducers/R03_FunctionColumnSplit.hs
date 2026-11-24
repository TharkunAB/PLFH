{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, PolyKinds, TypeOperators #-}
-- | Minimal reproducer (Serokell R03):
-- Multi-equation constructor splitting after a leading function-valued
-- retained binder fails with GHC-83605 (must use `case xs of` on the RHS).
module R03_FunctionColumnSplit where

import Data.Type.Equality ((:~:) (Refl), gcastWith)

mapAppendEq :: forall a b. foreach (f :: a -> b) -> foreach (xs :: [a]) -> foreach (ys :: [a])
            -> map f (xs ++ ys) :~: (map f xs ++ map f ys)
mapAppendEq _ []       _  = Refl
mapAppendEq f (_ : xs) ys = gcastWith (mapAppendEq f xs ys) Refl
