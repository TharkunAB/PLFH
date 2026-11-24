-- Generated from content/part1/Relations.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs, TypeOperators #-}
{-# LINE 12 "content/part1/Relations.md" #-}
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
  , LT' (..)
  , ltTrans
  , Trichotomy (..)
  , ltTrichotomy
  , Even (..)
  , Odd (..)
  , evenPlusEven
  , oddPlusEven
  , evenPlusOdd
  , oddPlusOdd
  ) where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib (withEquality)
import HaskLib.Size (Size (..), congSucc, plus, plusSucc, plusZero)

{-# LINE 66 "content/part1/Relations.md" #-}
-- | Evidence that one natural number is less than or equal to another.
data LE (m :: Size) (n :: Size) where
  ZleN :: LE 'Zero n
  SleS :: LE m n -> LE ('Succ m) ('Succ n)

-- | Concrete evidence that 2 <= 4.
twoLeFour :: LE ('Succ ('Succ 'Zero)) ('Succ ('Succ ('Succ ('Succ 'Zero))))
twoLeFour = SleS (SleS ZleN)

{-# LINE 82 "content/part1/Relations.md" #-}
-- | Inversion on successor inequality: if Succ m <= Succ n then m <= n.
invSleS :: LE ('Succ m) ('Succ n) -> LE m n
invSleS (SleS p) = p

-- | Inversion on zero upper bound: if m <= Zero then m = Zero.
invZleN :: LE m 'Zero -> m :~: 'Zero
invZleN ZleN = Refl

{-# LINE 101 "content/part1/Relations.md" #-}
-- | Reflexivity: n <= n for every finite n.
leRefl :: foreach (n :: Size) -> LE n n
leRefl Zero     = ZleN
leRefl (Succ n) = SleS (leRefl n)

-- | Transitivity: if m <= n and n <= p then m <= p.
leTrans :: LE m n -> LE n p -> LE m p
leTrans ZleN     _        = ZleN
leTrans (SleS p) (SleS q) = SleS (leTrans p q)

-- | Antisymmetry: if m <= n and n <= m then m = n.
leAntisym :: LE m n -> LE n m -> m :~: n
leAntisym ZleN     ZleN     = Refl
leAntisym (SleS p) (SleS q) = congSucc (leAntisym p q)

{-# LINE 122 "content/part1/Relations.md" #-}
-- | Evidence that either m <= n or n <= m.
data Total (m :: Size) (n :: Size) where
  Forward :: LE m n -> Total m n
  Flipped :: LE n m -> Total m n

-- | Ordering on naturals is total.
leTotal :: foreach (m :: Size) -> foreach (n :: Size) -> Total m n
leTotal Zero     _ = Forward ZleN
leTotal (Succ m) n = case n of
  Zero    -> Flipped ZleN
  Succ n' -> case leTotal m n' of
    Forward p -> Forward (SleS p)
    Flipped p -> Flipped (SleS p)

{-# LINE 144 "content/part1/Relations.md" #-}
-- | Right monotonicity: if p <= q then n + p <= n + q.
plusMonoR :: foreach (n :: Size) -> LE p q -> LE (plus n p) (plus n q)
plusMonoR Zero     pq = pq
plusMonoR (Succ n) pq = SleS (plusMonoR n pq)

-- | Left monotonicity: if m <= n then m + p <= n + p.
plusMonoL :: foreach (m :: Size) -> foreach (n :: Size) -> foreach (p :: Size)
          -> LE m n -> LE (plus m p) (plus n p)
plusMonoL m n p mn = case p of
  Zero    -> withEquality (plusZero m) (withEquality (plusZero n) mn)
  Succ p' -> withEquality (plusSucc m p')
               (withEquality (plusSucc n p') (SleS (plusMonoL m n p' mn)))

-- | Combined monotonicity: if m <= n and p <= q then m + p <= n + q.
plusMono :: foreach (m :: Size) -> foreach (n :: Size)
         -> foreach (p :: Size) -> foreach (q :: Size)
         -> LE m n -> LE p q -> LE (plus m p) (plus n q)
plusMono m n p q mn pq = leTrans (plusMonoL m n p mn) (plusMonoR n pq)

{-# LINE 170 "content/part1/Relations.md" #-}
-- | Strict inequality on natural numbers.
data LT' (m :: Size) (n :: Size) where
  ZltS :: LT' 'Zero ('Succ n)
  SltS :: LT' m n -> LT' ('Succ m) ('Succ n)

-- | Strict inequality is transitive.
ltTrans :: LT' m n -> LT' n p -> LT' m p
ltTrans ZltS     (SltS _) = ZltS
ltTrans (SltS p) (SltS q) = SltS (ltTrans p q)

-- | Trichotomy witness: m < n, m = n, or n < m.
data Trichotomy (m :: Size) (n :: Size) where
  TriLT :: LT' m n -> Trichotomy m n
  TriEQ :: m :~: n -> Trichotomy m n
  TriGT :: LT' n m -> Trichotomy m n

-- | Every pair of finite naturals satisfies trichotomy.
ltTrichotomy :: foreach (m :: Size) -> foreach (n :: Size) -> Trichotomy m n
ltTrichotomy Zero n = case n of
  Zero   -> TriEQ Refl
  Succ _ -> TriLT ZltS
ltTrichotomy (Succ m) n = case n of
  Zero    -> TriGT ZltS
  Succ n' -> case ltTrichotomy m n' of
    TriLT p  -> TriLT (SltS p)
    TriEQ eq -> TriEQ (congSucc eq)
    TriGT p  -> TriGT (SltS p)

{-# LINE 205 "content/part1/Relations.md" #-}
-- | Mutually inductive parity predicates on Size.
data Even (n :: Size) where
  EvenZ :: Even 'Zero
  EvenS :: Odd n -> Even ('Succ n)

data Odd (n :: Size) where
  OddS :: Even n -> Odd ('Succ n)

-- | Even + Even = Even (no `foreach` needed: GADT matching refines `m`!).
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
