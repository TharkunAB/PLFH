-- Generated from content/part1/Induction.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE AllowAmbiguousTypes, DataKinds, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, Modifiers, PolyKinds, TypeApplications, TypeOperators #-}
{-# LINE 13 "content/part1/Induction.md" #-}
module PLFH.Part1.Induction
  ( congSecond
  , plusAssoc
  , plusAssocRewrite
  , plusIdentityR
  , plusSuc
  , plusComm
  , plusRearrange
  , plusSwap
  , timesDistribPlus
  , timesAssoc
  , timesZeroR
  , timesSuccR
  , timesComm
  , fromInc
  , fromTo
  , twoTimesThree
  ) where

import Data.Type.Equality ((:~:) (Refl), sym, trans)
import GHC.Exts (U)
import HaskLib (rewrite)
import HaskLib.Nat (Nat (..), congFirst, congSucc, plus, plusSucc, plusZero)
import PLFH.Part1.Naturals (Bin (..), fromBin, inc, times, toBin)

{-# LINE 54 "content/part1/Induction.md" #-}
-- | Evidence that 2 * 3 = 6 using ordinary `times` imported from Naturals.
twoTimesThree :: times ('Succ ('Succ 'Zero)) ('Succ ('Succ ('Succ 'Zero)))
             :~: 'Succ ('Succ ('Succ ('Succ ('Succ ('Succ 'Zero)))))
twoTimesThree = Refl

{-# LINE 74 "content/part1/Induction.md" #-}
-- | Associativity of addition: (m + n) + p = m + (n + p).
plusAssoc :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
          -> plus (plus m n) p :~: plus m (plus n p)
plusAssoc Zero     _ _ = Refl
plusAssoc (Succ m) n p = congSucc (plusAssoc m n p)

{-# LINE 111 "content/part1/Induction.md" #-}
-- | Associativity proved via `HaskLib.rewrite` (analogous to Agda `rewrite`).
plusAssocRewrite :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
                 -> plus (plus m n) p :~: plus m (plus n p)
plusAssocRewrite Zero     _ _ = Refl
plusAssocRewrite (Succ m) n p = rewrite (plusAssocRewrite m n p) Refl

{-# LINE 145 "content/part1/Induction.md" #-}
-- | Right identity of addition (reused from HaskLib.Nat.plusZero).
plusIdentityR :: foreach (m :: Nat) -> plus m 'Zero :~: m
plusIdentityR = plusZero

-- | Move a successor from the second addend outside (reused from HaskLib.Nat.plusSucc).
plusSuc :: foreach (m :: Nat) -> foreach (n :: Nat)
        -> plus m ('Succ n) :~: 'Succ (plus m n)
plusSuc = plusSucc

{-# LINE 158 "content/part1/Induction.md" #-}
-- | Commutativity of addition: m + n = n + m.
plusComm :: foreach (m :: Nat) -> foreach (n :: Nat) -> plus m n :~: plus n m
plusComm m n = case n of
  Zero   -> plusZero m
  Succ k -> plusSucc m k `trans` congSucc (plusComm m k)

{-# LINE 187 "content/part1/Induction.md" #-}
-- | Lift an equality through the second argument of a binary size function.
congSecond :: forall (f :: Nat %U -> Nat %U -> Nat) l m n.
              m :~: n -> f l m :~: f l n
congSecond Refl = Refl

-- | Rearranging parentheses in a four-way sum.
plusRearrange :: foreach (m :: Nat) -> foreach (n :: Nat)
              -> foreach (p :: Nat) -> foreach (q :: Nat)
              -> plus (plus m n) (plus p q) :~: plus (plus m (plus n p)) q
plusRearrange m n p q =
  plusAssoc m n (plus p q)
    `trans` congSecond @plus @m (sym (plusAssoc n p q))
    `trans` sym (plusAssoc m (plus n p) q)

{-# LINE 218 "content/part1/Induction.md" #-}
-- | Swap the first two addends: m + (n + p) = n + (m + p).
plusSwap :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
         -> plus m (plus n p) :~: plus n (plus m p)
plusSwap m n p =
  sym (plusAssoc m n p)
    `trans` congFirst @plus @p (plusComm m n)
    `trans` plusAssoc n m p

{-# LINE 244 "content/part1/Induction.md" #-}
-- | Right distributivity of multiplication over addition:
-- (m + n) * p = m * p + n * p.
timesDistribPlus :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
                 -> times (plus m n) p :~: plus (times m p) (times n p)
timesDistribPlus Zero     _ _ = Refl
timesDistribPlus (Succ m) n p =
  rewrite (timesDistribPlus m n p)
    (sym (plusAssoc p (times m p) (times n p)))

-- | Associativity of multiplication: (m * n) * p = m * (n * p).
timesAssoc :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
           -> times (times m n) p :~: times m (times n p)
timesAssoc Zero     _ _ = Refl
timesAssoc (Succ m) n p =
  rewrite (timesAssoc m n p)
    (timesDistribPlus n (times m n) p)

-- | Right zero for multiplication: m * 0 = 0.
timesZeroR :: foreach (m :: Nat) -> times m 'Zero :~: 'Zero
timesZeroR Zero     = Refl
timesZeroR (Succ m) = timesZeroR m

-- | Right successor for multiplication: m * (Succ n) = m + m * n.
timesSuccR :: foreach (m :: Nat) -> foreach (n :: Nat)
           -> times m ('Succ n) :~: plus m (times m n)
timesSuccR Zero     _ = Refl
timesSuccR (Succ m) n =
  rewrite (timesSuccR m n)
    (congSucc (plusSwap n m (times m n)))

-- | Commutativity of multiplication: m * n = n * m.
timesComm :: foreach (m :: Nat) -> foreach (n :: Nat)
          -> times m n :~: times n m
timesComm Zero     n = sym (timesZeroR n)
timesComm (Succ m) n =
  rewrite (timesComm m n)
    (sym (timesSuccR n m))

{-# LINE 311 "content/part1/Induction.md" #-}
-- | Incrementing a bitstring adds one to its unary value.
fromInc :: foreach (b :: Bin) -> fromBin (inc b) :~: 'Succ (fromBin b)
fromInc Nil    = Refl
fromInc (X0 _) = Refl
fromInc (X1 b) =
  rewrite (fromInc b)
    (congSucc (plusSucc (fromBin b) (fromBin b)))

-- | Round-tripping Nat -> Bin -> Nat is the identity.
fromTo :: foreach (n :: Nat) -> fromBin (toBin n) :~: n
fromTo Zero     = Refl
fromTo (Succ n) = fromInc (toBin n) `trans` congSucc (fromTo n)
