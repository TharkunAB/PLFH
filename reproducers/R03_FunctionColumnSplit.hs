{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, PolyKinds, TypeOperators #-}
-- | Minimal reproducer (Serokell R03 / -O2 list rewrite-rule guard):
-- Passes `-O0` and `-O2 -fno-enable-rewrite-rules` (checked directly in
-- `PLFH.Part1.Lists`), but fails at default `-O2` with `GHC-83605` because
-- GHC's list-fusion rewrite rules inhibit open evaluation of `map` / `(++)`.
module R03_FunctionColumnSplit where

import Data.Type.Equality ((:~:) (Refl), gcastWith)

mapAppendEq :: forall a b. foreach (f :: a -> b) -> foreach (xs :: [a]) -> foreach (ys :: [a])
            -> map f (xs ++ ys) :~: (map f xs ++ map f ys)
mapAppendEq _ []       _  = Refl
mapAppendEq f (_ : xs) ys = gcastWith (mapAppendEq f xs ys) Refl
