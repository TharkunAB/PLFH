-- Generated from content/part1/Induction.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE AllowAmbiguousTypes, DependentTypes #-}
{-# LINE 12 "content/part1/Induction.md" #-}
module PLFH.Part1.Induction
  ( cong
  , assocExample
  , plusAssoc
  , plusAssoc0
  , plusAssoc1
  , plusAssoc2
  , plusAssocRewrite
  , plusIdentityR
  , plusSuc
  , plusComm
  , plusCommRewrite
  , plusRearrange
  , plusSwap
  , timesDistribPlus
  , timesAssoc
  , timesZeroR
  , timesSuccR
  , timesComm
  , timesSwap
  , timesInterchange
  , threeMonusTwo
  , twoMonusThree
  , zeroMonus
  , monusPlusAssoc
  , threePowFour
  , powPlus
  , powMul
  , powTimes
  , fromInc
  , fromTo
  , twoTimesThree
  ) where

import Data.Type.Equality ((:~:) (Refl), sym, trans)
import GHC.Types (Matchability)
import HaskLib (rewrite)
import HaskLib.Nat (Nat (..), congFirst, plus, plusSucc, plusZero, type (+))
import PLFH.Part1.Naturals (Bin (..), fromBin, inc, monus, pow, times, toBin)

{-# LINE 83 "content/part1/Induction.md" #-}
-- | Unified matchability-polymorphic congruence (`cong`): works just like Agda
-- for both constructors (`cong Succ`) and promoted functions (`cong (plus m)`).
cong :: forall {a} {b} {m :: Matchability}.
        forall (f :: a %m -> b) -> forall (x :: a) (y :: a).
        x :~: y -> f x :~: f y
cong _ Refl = Refl

-- | Evidence that 2 * 3 = 6 using ordinary `times` imported from Naturals.
twoTimesThree :: times 2 3 :~: 6
twoTimesThree = Refl

{-# LINE 150 "content/part1/Induction.md" #-}
-- | Concrete instance of associativity: (3 + 4) + 5 = 3 + (4 + 5).
assocExample :: ((3 + 4) + 5 :: Nat) :~: (3 + (4 + 5) :: Nat)
assocExample = Refl

{-# LINE 223 "content/part1/Induction.md" #-}
-- | Associativity of addition: (m + n) + p = m + (n + p).
plusAssoc :: foreach (m n p :: Nat)
          -> plus (plus m n) p :~: plus m (plus n p)
plusAssoc Zero     _ _ = Refl
plusAssoc (Succ m) n p = cong Succ (plusAssoc m n p)

{-# LINE 264 "content/part1/Induction.md" #-}
-- | Unrolling `plusAssoc` at m = 0, 1, and 2.
plusAssoc0 :: foreach (n p :: Nat)
           -> plus (plus 0 n) p :~: plus 0 (plus n p)
plusAssoc0 _ _ = Refl

plusAssoc1 :: foreach (n p :: Nat)
           -> plus (plus 1 n) p :~: plus 1 (plus n p)
plusAssoc1 n p = cong Succ (plusAssoc0 n p)

plusAssoc2 :: foreach (n p :: Nat)
           -> plus (plus 2 n) p :~: plus 2 (plus n p)
plusAssoc2 n p = cong Succ (plusAssoc1 n p)

{-# LINE 311 "content/part1/Induction.md" #-}
-- | First lemma: right identity of addition (`+-identityʳ`).
plusIdentityR :: foreach (m :: Nat) -> plus m Zero :~: m
plusIdentityR = plusZero

-- | Second lemma: move a successor from the second addend outside (`+-suc`).
plusSuc :: foreach (m n :: Nat)
        -> plus m (Succ n) :~: Succ (plus m n)
plusSuc = plusSucc

{-# LINE 325 "content/part1/Induction.md" #-}
-- | Commutativity of addition: m + n = n + m (`+-comm`).
plusComm :: foreach (m n :: Nat) -> plus m n :~: plus n m
plusComm m Zero     = plusZero m
plusComm m (Succ k) = plusSucc m k `trans` cong Succ (plusComm m k)

{-# LINE 347 "content/part1/Induction.md" #-}
-- | Rearranging parentheses in a four-way sum: (m + n) + (p + q) = (m + (n + p)) + q.
plusRearrange :: foreach (m n p q :: Nat)
              -> plus (plus m n) (plus p q) :~: plus (plus m (plus n p)) q
plusRearrange m n p q =
  plusAssoc m n (plus p q)
    `trans` cong (plus m) (sym (plusAssoc n p q))
    `trans` sym (plusAssoc m (plus n p) q)

{-# LINE 387 "content/part1/Induction.md" #-}
-- | Associativity proved via `HaskLib.rewrite` (`+-assoc′`).
plusAssocRewrite :: foreach (m n p :: Nat)
                 -> plus (plus m n) p :~: plus m (plus n p)
plusAssocRewrite Zero     _ _ = Refl
plusAssocRewrite (Succ m) n p = rewrite (plusAssocRewrite m n p) Refl

-- | Commutativity proved via nested `HaskLib.rewrite` (`+-comm′`).
plusCommRewrite :: foreach (m n :: Nat) -> plus m n :~: plus n m
plusCommRewrite m Zero     = rewrite (plusZero m) Refl
plusCommRewrite m (Succ k) = rewrite (plusSucc m k) (rewrite (plusCommRewrite m k) Refl)

{-# LINE 423 "content/part1/Induction.md" #-}
-- | Swap the first two addends: m + (n + p) = n + (m + p).
plusSwap :: foreach (m n p :: Nat)
         -> plus m (plus n p) :~: plus n (plus m p)
plusSwap m n p =
  sym (plusAssoc m n p)
    `trans` rewrite (plusComm m n) Refl
    `trans` plusAssoc n m p

{-# LINE 438 "content/part1/Induction.md" #-}
-- | Right distributivity of multiplication over addition (`*-distrib-+`):
-- (m + n) * p = m * p + n * p.
timesDistribPlus :: foreach (m n p :: Nat)
                 -> times (plus m n) p :~: plus (times m p) (times n p)
timesDistribPlus Zero     _ _ = Refl
timesDistribPlus (Succ m) n p =
  rewrite (timesDistribPlus m n p)
    (sym (plusAssoc p (times m p) (times n p)))

-- | Associativity of multiplication (`*-assoc`): (m * n) * p = m * (n * p).
timesAssoc :: foreach (m n p :: Nat)
           -> times (times m n) p :~: times m (times n p)
timesAssoc Zero     _ _ = Refl
timesAssoc (Succ m) n p =
  rewrite (timesAssoc m n p)
    (timesDistribPlus n (times m n) p)

-- | Right zero for multiplication: m * 0 = 0.
timesZeroR :: foreach (m :: Nat) -> times m Zero :~: Zero
timesZeroR Zero     = Refl
timesZeroR (Succ m) = timesZeroR m

-- | Right successor for multiplication: m * (Succ n) = m + m * n.
timesSuccR :: foreach (m n :: Nat)
           -> times m (Succ n) :~: plus m (times m n)
timesSuccR Zero     _ = Refl
timesSuccR (Succ m) n =
  rewrite (timesSuccR m n)
    (cong Succ (plusSwap n m (times m n)))

-- | Commutativity of multiplication (`*-comm`): m * n = n * m.
timesComm :: foreach (m n :: Nat)
          -> times m n :~: times n m
timesComm Zero     n = sym (timesZeroR n)
timesComm (Succ m) n =
  rewrite (timesComm m n)
    (sym (timesSuccR n m))

{-# LINE 485 "content/part1/Induction.md" #-}
-- | Concrete examples of truncated subtraction (cross-module from Naturals):
-- 3 ∸ 2 = 1 and 2 ∸ 3 = 0.
threeMonusTwo :: monus 3 2 :~: 1
threeMonusTwo = Refl

twoMonusThree :: monus 2 3 :~: 0
twoMonusThree = Refl

-- | Subtracting any natural from zero gives zero (`0∸n≡0`).
zeroMonus :: foreach (n :: Nat) -> monus Zero n :~: Zero
zeroMonus Zero     = Refl
zeroMonus (Succ _) = Refl

{-# LINE 505 "content/part1/Induction.md" #-}
-- | Two successive subtractions subtract the sum of their operands (`∸-+-assoc`).
monusPlusAssoc :: foreach (m n p :: Nat)
               -> monus (monus m n) p :~: monus m (plus n p)
monusPlusAssoc Zero     Zero     _ = Refl
monusPlusAssoc Zero     (Succ _) p = zeroMonus p
monusPlusAssoc (Succ _) Zero     _ = Refl
monusPlusAssoc (Succ m) (Succ n) p = monusPlusAssoc m n p

{-# LINE 521 "content/part1/Induction.md" #-}
-- | Swap the first two factors: m * (n * p) = n * (m * p).
timesSwap :: foreach (m n p :: Nat)
          -> times m (times n p) :~: times n (times m p)
timesSwap m n p =
  sym (timesAssoc m n p)
    `trans` congFirst @times @p (timesComm m n)
    `trans` timesAssoc n m p

-- | Interchange law for multiplication: (a * b) * (c * d) = (a * c) * (b * d).
timesInterchange :: foreach (a b c d :: Nat)
                 -> times (times a b) (times c d) :~: times (times a c) (times b d)
timesInterchange a b c d =
  timesAssoc a b (times c d)
    `trans` cong (times a) (timesSwap b c d)
    `trans` sym (timesAssoc a c (times b d))

-- | Concrete exponentiation example (cross-module from Naturals): 3 ^ 4 = 81.
threePowFour :: pow 3 4 :~: 81
threePowFour = Refl

-- | Distributivity of exponentiation over addition (`^-distribˡ-+-*`):
-- m ^ (n + p) = (m ^ n) * (m ^ p).
powPlus :: foreach (m n p :: Nat)
        -> pow m (plus n p) :~: times (pow m n) (pow m p)
powPlus m Zero     p = sym (plusZero (pow m p))
powPlus m (Succ k) p =
  rewrite (powPlus m k p)
    (sym (timesAssoc m (pow m k) (pow m p)))

-- | Distributivity of exponentiation over multiplication (`^-distribʳ-*`):
-- (m * n) ^ p = (m ^ p) * (n ^ p).
powMul :: foreach (m n p :: Nat)
       -> pow (times m n) p :~: times (pow m p) (pow n p)
powMul _ _ Zero     = Refl
powMul m n (Succ k) =
  rewrite (powMul m n k)
    (timesInterchange m n (pow m k) (pow n k))

-- | Associativity of iterated exponentiation (`^-*-assoc`):
-- (m ^ n) ^ p = m ^ (n * p).
powTimes :: foreach (m n p :: Nat)
         -> pow (pow m n) p :~: pow m (times n p)
powTimes m n Zero     = sym (cong (pow m) (timesZeroR n))
powTimes m n (Succ k) =
  rewrite (powTimes m n k)
    (rewrite (timesSuccR n k) (sym (powPlus m n (times n k))))

{-# LINE 583 "content/part1/Induction.md" #-}
-- | Incrementing a bitstring adds one to its unary value.
fromInc :: foreach (b :: Bin) -> fromBin (inc b) :~: Succ (fromBin b)
fromInc Nil    = Refl
fromInc (X0 _) = Refl
fromInc (X1 b) =
  rewrite (fromInc b)
    (cong Succ (plusSucc (fromBin b) (fromBin b)))

-- | Round-tripping Nat -> Bin -> Nat is the identity.
fromTo :: foreach (n :: Nat) -> fromBin (toBin n) :~: n
fromTo Zero     = Refl
fromTo (Succ n) = fromInc (toBin n) `trans` cong Succ (fromTo n)
