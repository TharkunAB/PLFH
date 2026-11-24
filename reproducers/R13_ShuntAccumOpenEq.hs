{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (R13/R16 / -O2 list rewrite-rule guard):
-- Passes `-O0` and `-O2 -fno-enable-rewrite-rules` (checked directly in
-- `PLFH.Part1.Lists`), but fails at default `-O2` with `GHC-83605` because
-- Prelude `(++)` rewrite rules inhibit open evaluation during `shuntAppend`.
module R13_ShuntAccumOpenEq (shunt, shuntAppend) where

import Data.Type.Equality ((:~:) (Refl))

shunt :: [a] -> [a] -> [a]
shunt []     ys = ys
shunt (x:xs) ys = shunt xs (x : ys)

shuntAppend :: foreach (xs :: [a]) -> foreach (ys :: [a]) -> foreach (zs :: [a])
            -> shunt (xs ++ ys) zs :~: shunt ys (shunt xs zs)
shuntAppend []     _  _  = Refl
shuntAppend (x:xs) ys zs = shuntAppend xs ys (x : zs)
