{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, PolyKinds, TypeOperators #-}
-- | Minimal reproducer (Serokell R03 / intentional -O2 list-fusion soundness guard):
-- Passes `-O0` and `-O2 -fno-enable-rewrite-rules` (checked directly in
-- `PLFH.Part1.Lists`), and is intentionally rejected at default `-O2` with
-- `GHC-83605`: stock `-O2` `build`/`augment`/`map` list fusion can change
-- strictness (`null (map not (build producer ++ error "ys"))` throws while
-- `null (map not (build producer) ++ map not (error "ys"))` returns `False`),
-- so GHC refuses to certify `mapAppendEq` when rewrite rules are active at `-O2`.
module R03_FunctionColumnSplit where

import Data.Type.Equality ((:~:) (Refl), gcastWith)

mapAppendEq :: forall a b. foreach (f :: a -> b) -> foreach (xs :: [a]) -> foreach (ys :: [a])
            -> map f (xs ++ ys) :~: (map f xs ++ map f ys)
mapAppendEq _ []       _  = Refl
mapAppendEq f (_ : xs) ys = gcastWith (mapAppendEq f xs ys) Refl
