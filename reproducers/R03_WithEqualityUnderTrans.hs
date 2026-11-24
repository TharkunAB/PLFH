{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (Serokell R03):
-- Calling `withEquality` on a retained function application inside `trans`
-- fails with an untouchable meta-variable bound by the retained application.
module R03_WithEqualityUnderTrans where

import Data.Type.Equality ((:~:) (Refl), sym, trans)
import HaskLib (withEquality)
import HaskLib.Nat (Nat (..), congSucc, plus, plusSucc, plusZero)

plusAssoc :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
          -> plus (plus m n) p :~: plus m (plus n p)
plusAssoc Zero     _ _ = Refl
plusAssoc (Succ m) n p = congSucc (plusAssoc m n p)

plusComm :: foreach (m :: Nat) -> foreach (n :: Nat) -> plus m n :~: plus n m
plusComm m n = case n of
  Zero   -> plusZero m
  Succ k -> plusSucc m k `trans` congSucc (plusComm m k)

plusSwap :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
         -> plus m (plus n p) :~: plus n (plus m p)
plusSwap m n p =
  sym (plusAssoc m n p)
    `trans` withEquality (plusComm m n) Refl
    `trans` plusAssoc n m p
