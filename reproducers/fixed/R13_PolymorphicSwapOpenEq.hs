{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (Serokell R13 / R16):
-- Even though polymorphic `Iso a b` is now supported, upgrading PLFA Connectives
-- laws such as `sumComm :: Iso (Either a b) (Either b a)` or
-- `prodComm :: Iso (a, b) (b, a)` fails with `GHC-68947`:
-- simple non-recursive swap functions on parameterized datatypes (`Either`,
-- tuples `(,)`, or a custom 2-parameter `Pair a b`) have no checked open
-- equations in types, even when monomorphized (`Either Bool Ordering`).
module R13_PolymorphicSwapOpenEq where

import Data.Type.Equality ((:~:) (Refl))

swapSum :: Either a b -> Either b a
swapSum (Left x)  = Right x
swapSum (Right y) = Left y

swapSumInv :: foreach (s :: Either a b) -> swapSum (swapSum s) :~: s
swapSumInv (Left _)  = Refl
swapSumInv (Right _) = Refl
