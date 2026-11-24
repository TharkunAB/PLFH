{-# LANGUAGE AllowAmbiguousTypes, DataKinds, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, PolyKinds, TypeApplications, TypeOperators #-}
-- | Minimal reproducer (GHC PANIC in compiler/GHC/Tc/Gen/App.hs:3947):
-- Calling `substP @Even (toEqP (plusComm m n)) ev` panics with:
--   tcInstFun: invalid retained instantiations
--   [('Unmatchable, x[sk:2]), ('Unmatchable, y[sk:2])]
--   [T:plus m n, T:plus n m]
module R03_TcInstFunPanic where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl), trans)
import HaskLib.Nat (Nat (..), congSucc, plus, plusSucc, plusZero)

data EqP (x :: a) (y :: a) where
  ReflP :: EqP x x

toEqP :: x :~: y -> EqP x y
toEqP Refl = ReflP

substP :: forall {a} (p :: a -> Type) (x :: a) (y :: a).
          EqP x y -> p x -> p y
substP ReflP px = px

data Even (n :: Nat) where
  EvenZ :: Even 'Zero
  EvenS :: Odd n -> Even ('Succ n)

data Odd (n :: Nat) where
  OddS :: Even n -> Odd ('Succ n)

plusComm :: foreach (m :: Nat) -> foreach (n :: Nat) -> plus m n :~: plus n m
plusComm m n = case n of
  Zero   -> plusZero m
  Succ k -> plusSucc m k `trans` congSucc (plusComm m k)

evenComm :: foreach (m :: Nat) -> foreach (n :: Nat)
         -> Even (plus m n) -> Even (plus n m)
evenComm m n ev = substP @Even (toEqP (plusComm m n)) ev
