{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (GHC PANIC in compiler/GHC/Core/TyCo/Subst.hs:900):
-- An eta-reduced alias `lengthReverseLaw = lengthReverse` of an imported
-- polymorphic `foreach (xs :: [a])` function panics GHC with:
--   substTy: unsupported runtime index or changed domain
--   xs := retained
-- Eta-expanding `lengthReverseLaw xs = lengthReverse xs` compiles cleanly.
module R05_SubstTyEtaAliasPanic where

import Data.Type.Equality ((:~:))
import HaskLib (lengthReverse, size)

lengthReverseLaw :: forall a. foreach (xs :: [a]) -> size (reverse xs) :~: size xs
lengthReverseLaw = lengthReverse
