{-# LANGUAGE DataKinds, ExperimentalDependentTypes, Modifiers, PolyKinds #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, TypeApplications #-}
-- | Minimal reproducer (Serokell R17 + R23; GHC Proposals #378 & #242;
-- Kiss et al. ICFP 2019; Eisenberg & Stolarek Haskell 2014):
-- Proving PLFA Equality's pure impredicative Leibniz symmetry (`sym-≐`)
-- instantiates `xy :: LeibnizU x y` with `@(\z -> p z -> p x)`.
-- Capturing the unmatchable predicate variable `p :: a %U -> Type` inside an
-- inline type-level lambda currently fails with `GHC-27185`, forcing
-- `PLFH.Part1.Equality.leibnizUSym` to detour through `EqP`.
module R17_TypeLambdaCaptureUnmatchable where

import Data.Kind (Type)
import GHC.Exts (U)

type LeibnizU (x :: a) (y :: a) = forall (p :: a %U -> Type). p x -> p y

leibnizUSymAt :: forall {a} (x :: a) (y :: a) (p :: a %U -> Type).
                 LeibnizU x y -> p y -> p x
leibnizUSymAt xy = xy @(\z -> p z -> p x) (\px -> px)

leibnizUSym :: forall {a} (x :: a) (y :: a). LeibnizU x y -> LeibnizU y x
leibnizUSym xy = leibnizUSymAt @x @y xy
