{-# LANGUAGE AllowAmbiguousTypes, DataKinds, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, Modifiers, PolyKinds, TypeApplications, TypeOperators #-}
-- | Minimal reproducer (Serokell R03/R17/R23):
-- Applying generic unary `cong` to a partially applied ordinary function
-- `@(plus m)` (mirroring PLFA's `cong (m +_)` in `+-rearrange`) fails with
-- an untouchable meta-variable bound by a retained application.
module R03_CongPartialApp where

import Data.Type.Equality ((:~:) (Refl), sym, trans)
import GHC.Exts (U)
import HaskLib.Nat (Nat (..), congSucc, plus)

cong :: forall {a} {b} (f :: a %U -> b) (x :: a) (y :: a). x :~: y -> f x :~: f y
cong Refl = Refl

plusAssoc :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
          -> plus (plus m n) p :~: plus m (plus n p)
plusAssoc Zero     _ _ = Refl
plusAssoc (Succ m) n p = congSucc (plusAssoc m n p)

plusRearrange :: foreach (m :: Nat) -> foreach (n :: Nat)
              -> foreach (p :: Nat) -> foreach (q :: Nat)
              -> plus (plus m n) (plus p q) :~: plus (plus m (plus n p)) q
plusRearrange m n p q =
  plusAssoc m n (plus p q)
    `trans` cong @(plus m) (sym (plusAssoc n p q))
    `trans` sym (plusAssoc m (plus n p) q)
