-- Generated from content/part1/Relations.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DependentTypes #-}
{-# LINE 29 "content/part1/Relations.md" #-}
module PLFH.Part1.Relations
  ( LE (..)
  , twoLeFour
  , invSleS
  , invZleN
  , leRefl
  , leTrans
  , leAntisym
  , Total (..)
  , leTotal
  , plusMonoR
  , plusMonoL
  , plusMono
  , timesMonoR
  , timesMonoL
  , timesMono
  , LT' (..)
  , ltTrans
  , Trichotomy (..)
  , ltTrichotomy
  , ltToLe
  , leToLt
  , DiffWitness (..)
  , leToDiff
  , diffToLe
  , plusMonoLtR
  , plusMonoLtL
  , plusMonoLt
  , Even (..)
  , Odd (..)
  , evenPlusEven
  , oddPlusEven
  , evenPlusOdd
  , oddPlusOdd
  , evenOrOdd
  , notBothEvenOdd
  , One (..)
  , Can (..)
  , incOne
  , incCan
  , toBinCan
  , PosNat (..)
  , onePos
  , toBinDoubleSucc
  , toFromDoubleOne
  , toFromOne
  , toFromCan
  ) where

import Data.Nat.Dependent (Nat (..), plus)
import Data.Nat.Dependent.Properties (plusSucc, plusZero)
import Data.Type.Equality ((:~:) (Refl))
import Data.Type.Equality.Dependent (rewrite)
import Data.Void (Void)
import PLFH.Part1.Induction (cong, timesComm)
import PLFH.Part1.Naturals (Bin (..), fromBin, inc, times, toBin)

{-# LINE 121 "content/part1/Relations.md" #-}
-- | Evidence that one natural number is less than or equal to another.
data LE (m :: Nat) (n :: Nat) where
  ZleN :: LE Zero n
  SleS :: LE m n -> LE (Succ m) (Succ n)

{-# LINE 140 "content/part1/Relations.md" #-}
-- | Concrete evidence that 2 <= 4 (using decimal literals for fixed numbers).
twoLeFour :: LE 2 4
twoLeFour = SleS (SleS ZleN)

{-# LINE 162 "content/part1/Relations.md" #-}
-- | Inversion on successor inequality: if Succ m <= Succ n then m <= n.
invSleS :: LE (Succ m) (Succ n) -> LE m n
invSleS (SleS p) = p

-- | Inversion on zero upper bound: if m <= Zero then m = Zero.
invZleN :: LE m Zero -> m :~: Zero
invZleN ZleN = Refl

{-# LINE 201 "content/part1/Relations.md" #-}
-- | Reflexivity: n <= n for every finite n.
leRefl :: foreach (n :: Nat) -> LE n n
leRefl Zero     = ZleN
leRefl (Succ n) = SleS (leRefl n)

{-# LINE 214 "content/part1/Relations.md" #-}
-- | Transitivity: if m <= n and n <= p then m <= p.
leTrans :: LE m n -> LE n p -> LE m p
leTrans ZleN     _        = ZleN
leTrans (SleS p) (SleS q) = SleS (leTrans p q)

{-# LINE 231 "content/part1/Relations.md" #-}
-- | Antisymmetry: if m <= n and n <= m then m = n.
leAntisym :: LE m n -> LE n m -> m :~: n
leAntisym ZleN     ZleN     = Refl
leAntisym (SleS p) (SleS q) = cong Succ (leAntisym p q)

{-# LINE 249 "content/part1/Relations.md" #-}
-- | Evidence that either m <= n or n <= m.
data Total (m :: Nat) (n :: Nat) where
  Forward :: LE m n -> Total m n
  Flipped :: LE n m -> Total m n

{-# LINE 261 "content/part1/Relations.md" #-}
-- | Ordering on naturals is total.
leTotal :: foreach (m n :: Nat) -> Total m n
leTotal Zero     _        = Forward ZleN
leTotal (Succ _) Zero     = Flipped ZleN
leTotal (Succ m) (Succ n) = case leTotal m n of
  Forward p -> Forward (SleS p)
  Flipped p -> Flipped (SleS p)

{-# LINE 286 "content/part1/Relations.md" #-}
-- | Right monotonicity: if p <= q then n + p <= n + q.
plusMonoR :: foreach (n :: Nat) -> LE p q -> LE (plus n p) (plus n q)
plusMonoR Zero     pq = pq
plusMonoR (Succ n) pq = SleS (plusMonoR n pq)

{-# LINE 297 "content/part1/Relations.md" #-}
-- | Left monotonicity: if m <= n then m + p <= n + p.
plusMonoL :: foreach (m n p :: Nat)
          -> LE m n -> LE (plus m p) (plus n p)
plusMonoL m n Zero     mn = rewrite (plusZero m) (rewrite (plusZero n) mn)
plusMonoL m n (Succ p) mn =
  rewrite (plusSucc m p)
    (rewrite (plusSucc n p) (SleS (plusMonoL m n p mn)))

{-# LINE 310 "content/part1/Relations.md" #-}
-- | Combined monotonicity: if m <= n and p <= q then m + p <= n + q.
plusMono :: foreach (m n p q :: Nat)
         -> LE m n -> LE p q -> LE (plus m p) (plus n q)
plusMono m n p q mn pq = leTrans (plusMonoL m n p mn) (plusMonoR n pq)

{-# LINE 324 "content/part1/Relations.md" #-}
-- | Right monotonicity of multiplication: if p <= q then n * p <= n * q.
timesMonoR :: foreach (n p q :: Nat)
           -> LE p q -> LE (times n p) (times n q)
timesMonoR Zero     _ _ _  = ZleN
timesMonoR (Succ n) p q pq = plusMono p q (times n p) (times n q) pq (timesMonoR n p q pq)

-- | Left monotonicity of multiplication: if m <= n then m * p <= n * p.
timesMonoL :: foreach (m n p :: Nat)
           -> LE m n -> LE (times m p) (times n p)
timesMonoL m n p mn =
  rewrite (timesComm m p)
    (rewrite (timesComm n p) (timesMonoR p m n mn))

-- | Combined monotonicity of multiplication (`*-mono-≤`):
-- if m <= n and p <= q then m * p <= n * q.
timesMono :: foreach (m n p q :: Nat)
          -> LE m n -> LE p q -> LE (times m p) (times n q)
timesMono m n p q mn pq = leTrans (timesMonoL m n p mn) (timesMonoR n p q pq)

{-# LINE 354 "content/part1/Relations.md" #-}
-- | Strict inequality on natural numbers.
data LT' (m :: Nat) (n :: Nat) where
  ZltS :: LT' Zero (Succ n)
  SltS :: LT' m n -> LT' (Succ m) (Succ n)

{-# LINE 364 "content/part1/Relations.md" #-}
-- | Strict inequality is transitive.
ltTrans :: LT' m n -> LT' n p -> LT' m p
ltTrans ZltS     (SltS _) = ZltS
ltTrans (SltS p) (SltS q) = SltS (ltTrans p q)

{-# LINE 374 "content/part1/Relations.md" #-}
-- | Trichotomy witness: m < n, m = n, or n < m.
data Trichotomy (m :: Nat) (n :: Nat) where
  TriLT :: LT' m n -> Trichotomy m n
  TriEQ :: m :~: n -> Trichotomy m n
  TriGT :: LT' n m -> Trichotomy m n

-- | Every pair of finite naturals satisfies trichotomy.
ltTrichotomy :: foreach (m n :: Nat) -> Trichotomy m n
ltTrichotomy Zero     Zero     = TriEQ Refl
ltTrichotomy Zero     (Succ _) = TriLT ZltS
ltTrichotomy (Succ _) Zero     = TriGT ZltS
ltTrichotomy (Succ m) (Succ n) = case ltTrichotomy m n of
  TriLT p  -> TriLT (SltS p)
  TriEQ eq -> TriEQ (cong Succ eq)
  TriGT p  -> TriGT (SltS p)

{-# LINE 398 "content/part1/Relations.md" #-}
-- | Strict inequality implies shifted non-strict inequality: m < n -> Succ m <= n.
ltToLe :: LT' m n -> LE (Succ m) n
ltToLe ZltS     = SleS ZleN
ltToLe (SltS p) = SleS (ltToLe p)

-- | Shifted non-strict inequality implies strict inequality: Succ m <= n -> m < n.
leToLt :: LE (Succ m) n -> LT' m n
leToLt (SleS ZleN)     = ZltS
leToLt (SleS (SleS p)) = SltS (leToLt (SleS p))

-- | Witness that m + k = n for some runtime Nat k.
data DiffWitness (m :: Nat) (n :: Nat) where
  MkDiff :: foreach (k :: Nat) -> plus m k :~: n -> DiffWitness m n

-- | From m <= n we can compute a difference witness k with m + k = n.
leToDiff :: foreach (m n :: Nat) -> LE m n -> DiffWitness m n
leToDiff Zero     n        _ = MkDiff n Refl
leToDiff (Succ _) Zero     p = case p of {}
leToDiff (Succ m) (Succ n) p = case p of
  SleS q -> case leToDiff m n q of
    MkDiff k eq -> MkDiff k (rewrite eq Refl)

-- | Conversely, m <= m + k for any finite m and k.
diffToLe :: foreach (m k :: Nat) -> LE m (plus m k)
diffToLe Zero     _ = ZleN
diffToLe (Succ m) k = SleS (diffToLe m k)

{-# LINE 432 "content/part1/Relations.md" #-}
-- | Right monotonicity of strict inequality: if p < q then n + p < n + q.
plusMonoLtR :: foreach (n :: Nat) -> LT' p q -> LT' (plus n p) (plus n q)
plusMonoLtR Zero     pq = pq
plusMonoLtR (Succ n) pq = SltS (plusMonoLtR n pq)

-- | Left monotonicity of strict inequality: if m < n then m + p < n + p.
plusMonoLtL :: foreach (m n p :: Nat)
            -> LT' m n -> LT' (plus m p) (plus n p)
plusMonoLtL m n Zero     mn = rewrite (plusZero m) (rewrite (plusZero n) mn)
plusMonoLtL m n (Succ p) mn =
  rewrite (plusSucc m p)
    (rewrite (plusSucc n p) (SltS (plusMonoLtL m n p mn)))

-- | Combined monotonicity of strict inequality (`+-mono-<`):
-- if m < n and p < q then m + p < n + q.
plusMonoLt :: foreach (m n p q :: Nat)
           -> LT' m n -> LT' p q -> LT' (plus m p) (plus n q)
plusMonoLt m n p q mn pq = ltTrans (plusMonoLtL m n p mn) (plusMonoLtR n pq)

{-# LINE 463 "content/part1/Relations.md" #-}
-- | Mutually inductive parity predicates on Nat.
data Even (n :: Nat) where
  EvenZ :: Even Zero
  EvenS :: Odd n -> Even (Succ n)

data Odd (n :: Nat) where
  OddS :: Even n -> Odd (Succ n)

{-# LINE 479 "content/part1/Relations.md" #-}
-- | Even + Even = Even (no `foreach` needed: GADT matching refines `m`).
evenPlusEven :: Even m -> Even n -> Even (plus m n)
evenPlusEven EvenZ      en = en
evenPlusEven (EvenS om) en = EvenS (oddPlusEven om en)

-- | Odd + Even = Odd.
oddPlusEven :: Odd m -> Even n -> Odd (plus m n)
oddPlusEven (OddS em) en = OddS (evenPlusEven em en)

-- | Even + Odd = Odd.
evenPlusOdd :: Even m -> Odd n -> Odd (plus m n)
evenPlusOdd EvenZ      on = on
evenPlusOdd (EvenS om) on = OddS (oddPlusOdd om on)

-- | Odd + Odd = Even.
oddPlusOdd :: Odd m -> Odd n -> Even (plus m n)
oddPlusOdd (OddS em) on = EvenS (evenPlusOdd em on)

{-# LINE 502 "content/part1/Relations.md" #-}
-- | Every natural number is either even or odd.
evenOrOdd :: foreach (n :: Nat) -> Either (Even n) (Odd n)
evenOrOdd Zero     = Left EvenZ
evenOrOdd (Succ n) = case evenOrOdd n of
  Left  ev -> Right (OddS ev)
  Right od -> Left  (EvenS od)

-- | No natural number is both even and odd.
notBothEvenOdd :: Even n -> Odd n -> Void
notBothEvenOdd (EvenS o) (OddS e) = notBothEvenOdd e o

{-# LINE 533 "content/part1/Relations.md" #-}
-- | Evidence that a binary number is positive and has no leading zero bits.
data One (b :: Bin) where
  OneX1  :: One (X1 Nil)
  OneX0  :: One b -> One (X0 b)
  OneX1' :: One b -> One (X1 b)

-- | Evidence that a binary number is in canonical form (unique per natural).
data Can (b :: Bin) where
  CanZ   :: Can (X0 Nil)
  CanOne :: One b -> Can b

{-# LINE 549 "content/part1/Relations.md" #-}
-- | Incrementing a positive canonical binary number stays positive canonical.
incOne :: foreach (b :: Bin) -> One b -> One (inc b)
incOne Nil         p          = case p of {}
incOne (X0 _)      (OneX0 o)  = OneX1' o
incOne (X1 Nil)    OneX1      = OneX0 OneX1
incOne (X1 Nil)    (OneX1' o) = case o of {}
incOne (X1 (X0 b)) (OneX1' o) = OneX0 (incOne (X0 b) o)
incOne (X1 (X1 b)) (OneX1' o) = OneX0 (incOne (X1 b) o)

-- | Incrementing any canonical binary number yields a canonical binary number.
incCan :: foreach (b :: Bin) -> Can b -> Can (inc b)
incCan Nil    p                = case p of {}
incCan (X0 _) CanZ             = CanOne OneX1
incCan (X0 _) (CanOne (OneX0 o)) = CanOne (OneX1' o)
incCan (X1 b) (CanOne o)       = CanOne (incOne (X1 b) o)

-- | Converting any natural number to binary produces a canonical bitstring (`to-Can`).
toBinCan :: foreach (n :: Nat) -> Can (toBin n)
toBinCan Zero     = CanZ
toBinCan (Succ n) = incCan (toBin n) (toBinCan n)

{-# LINE 578 "content/part1/Relations.md" #-}
-- | Witness that a natural number is strictly positive (`n = Succ k`).
data PosNat (n :: Nat) where
  MkPos :: foreach (k :: Nat) -> n :~: Succ k -> PosNat n

-- | Every `One` bitstring represents a strictly positive natural number.
onePos :: foreach (b :: Bin) -> One b -> PosNat (fromBin b)
onePos Nil         o          = case o of {}
onePos (X0 b)      (OneX0 o)  = case onePos b o of
  MkPos k eq -> rewrite eq (MkPos (plus k (Succ k)) Refl)
onePos (X1 Nil)    _          = MkPos Zero Refl
onePos (X1 (X0 b)) _          = MkPos (plus (fromBin (X0 b)) (fromBin (X0 b))) Refl
onePos (X1 (X1 b)) _          = MkPos (plus (fromBin (X1 b)) (fromBin (X1 b))) Refl

-- | Doubling a positive natural shifts its binary representation left by one zero bit.
toBinDoubleSucc :: foreach (n :: Nat) -> toBin (plus (Succ n) (Succ n)) :~: X0 (toBin (Succ n))
toBinDoubleSucc Zero     = Refl
toBinDoubleSucc (Succ k) =
  rewrite (plusSucc (Succ k) (Succ k))
    (rewrite (toBinDoubleSucc k) Refl)

toFromDoubleOne :: foreach (b :: Bin) -> One b -> toBin (plus (fromBin b) (fromBin b)) :~: X0 b
toFromDoubleOne b o =
  let ih = toFromOne b o
  in case onePos b o of
    MkPos k eq -> go (toBinDoubleSucc k) eq ih
  where
    go :: toBin (plus (Succ k) (Succ k)) :~: X0 (toBin (Succ k))
       -> fromBin b :~: Succ k
       -> toBin (fromBin b) :~: b
       -> toBin (plus (fromBin b) (fromBin b)) :~: X0 b
    go dbl Refl Refl = dbl

-- | Round-trip law for positive canonical bitstrings: `toBin (fromBin b) = b`.
toFromOne :: foreach (b :: Bin) -> One b -> toBin (fromBin b) :~: b
toFromOne Nil         o          = case o of {}
toFromOne (X0 b)      (OneX0 o)  = toFromDoubleOne b o
toFromOne (X1 Nil)    OneX1      = Refl
toFromOne (X1 Nil)    (OneX1' o) = case o of {}
toFromOne (X1 (X0 b)) (OneX1' o) = cong inc (toFromDoubleOne (X0 b) o)
toFromOne (X1 (X1 b)) (OneX1' o) = cong inc (toFromDoubleOne (X1 b) o)

-- | Full round-trip law for canonical binary numbers (`to-from`):
-- together with `Induction.fromTo`, `Nat` and canonical `Bin` are in bijection.
toFromCan :: foreach (b :: Bin) -> Can b -> toBin (fromBin b) :~: b
toFromCan Nil         (CanOne o)         = case o of {}
toFromCan (X0 Nil)    CanZ               = Refl
toFromCan (X0 Nil)    (CanOne (OneX0 o)) = case o of {}
toFromCan (X0 (X0 b)) (CanOne o)         = toFromOne (X0 (X0 b)) o
toFromCan (X0 (X1 b)) (CanOne o)         = toFromOne (X0 (X1 b)) o
toFromCan (X1 b)      (CanOne o)         = toFromOne (X1 b) o
