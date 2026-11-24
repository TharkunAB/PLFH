{-# LANGUAGE AllowAmbiguousTypes, DataKinds, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE Modifiers, PolyKinds, RequiredTypeArguments, TypeApplications, TypeOperators #-}
-- | Minimal reproducer (Serokell R23 / R03 / RequiredTypeArguments):
-- With invisible `TypeApplications`, a SINGLE matchability-polymorphic
-- `congApp :: forall {a} {b} {m :: Matchability} (f :: a %m -> b) (x :: a) (y :: a). x :~: y -> f x :~: f y`
-- compiles cleanly for BOTH promoted constructors (`congApp @Succ (plusAssoc m n p)`)
-- AND partially applied promoted functions (`congApp @(plus m) (plusAssoc n p q)`).
--
-- However, trying to drop the `@` using `RequiredTypeArguments` so users can
-- write Agda-style `cong Succ (plusAssoc m n p)` and `cong (plus m) (...)`
-- hits TWO bugs:
--   1. Even monomorphic `congVisM :: forall (f :: a -> b) -> ...` fails on
--      `congVisM Succ (plusAssoc m n p)` with GHC-83865 ("`y0' is untouchable
--      inside the constraints: () bound by a retained application").
--   2. Matchability-polymorphic `congVis :: forall {m :: Matchability}. forall (f :: a %m -> b) -> ...`
--      fails BOTH on `congVis Succ eq` (GHC-83865 untouchable `y0`) AND on
--      `congVis (plus m) eq` (GHC-70565 "Cannot check type-level use of partially
--      applied function `plus'").
module R23_MatchabilityPolyCong where

import Data.Type.Equality ((:~:) (Refl))
import GHC.Types (Matchability)

data Nat = Zero | Succ Nat

plus :: Nat -> Nat -> Nat
plus Zero     n = n
plus (Succ m) n = Succ (plus m n)

-- Control: invisible TypeApplications + Matchability polymorphism WORKS for BOTH!
congApp :: forall {a} {b} {m :: Matchability} (f :: a %m -> b) (x :: a) (y :: a).
           x :~: y -> f x :~: f y
congApp Refl = Refl

okAssoc :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
        -> plus (plus m n) p :~: plus m (plus n p)
okAssoc Zero     _ _ = Refl
okAssoc (Succ m) n p = congApp @Succ (okAssoc m n p)

okPlus :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat) -> foreach (q :: Nat)
       -> plus m (plus (plus n p) q) :~: plus m (plus n (plus p q))
okPlus m n p q = congApp @(plus m) (okAssoc n p q)

-- Bug 1: Monomorphic RequiredTypeArguments `congVisM Succ (...)` fails under
-- a retained recursive call with GHC-83865 (untouchable `y0`)!
congVisM :: forall {a} {b}. forall (f :: a -> b) -> forall (x :: a) (y :: a).
            x :~: y -> f x :~: f y
congVisM _ Refl = Refl

badAssocVis :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
            -> plus (plus m n) p :~: plus m (plus n p)
badAssocVis Zero     _ _ = Refl
badAssocVis (Succ m) n p = congVisM Succ (badAssocVis m n p)

-- Bug 2: Matchability-polymorphic RequiredTypeArguments `congVis` fails on
-- both `congVis Succ` (GHC-83865) and `congVis (plus m)` (GHC-70565)!
congVis :: forall {a} {b} {m :: Matchability}. forall (f :: a %m -> b) -> forall (x :: a) (y :: a).
           x :~: y -> f x :~: f y
congVis _ Refl = Refl

badVisSucc :: x :~: y -> Succ x :~: Succ y
badVisSucc eq = congVis Succ eq

badVisPlus :: foreach (m :: Nat) -> x :~: y -> plus m x :~: plus m y
badVisPlus m eq = congVis (plus m) eq
