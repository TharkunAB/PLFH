{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}
-- | Minimal reproducer (Serokell R04/R05):
-- On GHC 9cc4065fab, eta-reduced aliases of polymorphic `foreach (xs :: [a])`
-- functions (`lengthReverseLaw = lengthReverse`) now compile cleanly,
-- whereas an eta-reduced alias of a function with a function-valued
-- `foreach (f :: a -> b)` binder (`lengthMapLaw = lengthMap`) fails with
-- GHC-83865 printing identical expected and actual types!
--
-- Eta-expanding (`lengthMapLaw f xs = lengthMap f xs`) compiles cleanly.
module R04_EtaAliasForEachFunctionBinder where

import Data.Type.Equality ((:~:))
import HaskLib (lengthMap, lengthReverse, size)

-- Control: eta-reduced alias with list-valued `foreach` passes!
lengthReverseOk :: forall a. foreach (xs :: [a]) -> size (reverse xs) :~: size xs
lengthReverseOk = lengthReverse

-- Trigger: eta-reduced alias with function-valued `foreach (f :: a -> b)` fails GHC-83865
-- with identical expected and actual types!
lengthMapBad :: forall a b. foreach (f :: a -> b) -> foreach (xs :: [a])
             -> size (map f xs) :~: size xs
lengthMapBad = lengthMap
