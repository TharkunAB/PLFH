{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (R13/R16): tail-recursive accumulating helper `shunt`
-- (changing the accumulator parameter `ys` to `x : ys` in the recursive call)
-- fails GHC-68947 ("No checked equations are available for 'shunt' in a type").
--
-- Blocks PLFA Part 1 Lists `shunt-++` (`shunt (xs ++ ys) zs = shunt ys (shunt xs zs)`).
module R13_ShuntAccumOpenEq (shunt, shuntAppend) where

import Data.Type.Equality ((:~:) (Refl))

shunt :: [a] -> [a] -> [a]
shunt []     ys = ys
shunt (x:xs) ys = shunt xs (x : ys)

shuntAppend :: foreach (xs :: [a]) -> foreach (ys :: [a]) -> foreach (zs :: [a])
            -> shunt (xs ++ ys) zs :~: shunt ys (shunt xs zs)
shuntAppend []     _  _  = Refl
shuntAppend (x:xs) ys zs = shuntAppend xs ys (x : zs)
