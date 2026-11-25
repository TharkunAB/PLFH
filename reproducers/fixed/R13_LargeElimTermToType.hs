{-# LANGUAGE DataKinds, ExperimentalDependentTypes, ExplicitNamespaces, GADTs #-}
-- | Minimal reproducer (Serokell R06 / R13 Large Elimination;
-- GHC Proposals #378, #281, #509; Eisenberg 2016; Weirich et al. ICFP 2017):
-- Defining a term-to-`Type` function (`valPred :: Val -> Type`) as an ordinary
-- Haskell function using `type (...)` (large elimination, matching PLFA
-- Adequacy's `𝕍 : Value → Clos → Set`) is not supported, forcing
-- `PLFH.Part3.Adequacy` to use the book's sole `type family` (`LogVLam`) with
-- `UndecidableInstances`.
module R13_LargeElimTermToType where

import Data.Kind (Type)

data Val = Bot | Arr Val Val

valPred :: Val -> Type
valPred Bot       = type ()
valPred (Arr a b) = type (valPred a -> valPred b)
