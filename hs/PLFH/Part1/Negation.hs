-- Generated from content/part1/Negation.md by scripts/extract_and_sync.hs
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DependentTypes, ListTuplePuns #-}
{-# LINE 24 "content/part1/Negation.md" #-}
module PLFH.Part1.Negation
  ( Not
  , doubleNegIntro
  , tripleNegElim
  , doubleNegMap
  , doubleNegBind
  , contraposition
  , deMorganSum
  , deMorganProdPartial
  , irrefutableLEM
  , ExcludedMiddle
  , DoubleNegElim
  , Peirce
  , ImpliesToOr
  , DeMorganNot
  , emToDne
  , dneToPeirce
  , peirceToEm
  , emToImpOr
  , impOrToEm
  , emToDeMorganNot
  , deMorganNotToEm
  , ltIrrefl
  , ltAsym
  , notLtZero
  , ltToNotGe
  , leToNotGt
  , notLeToGt
  ) where

import Data.Void (Void, absurd)
import Data.Nat.Dependent (Nat (..))
import PLFH.Part1.Isomorphism (Iff (..))
import PLFH.Part1.Relations (LE (..), LT' (..))

{-# LINE 67 "content/part1/Negation.md" #-}
-- | Logical negation: evidence that a proposition implies falsehood (`Void`).
type Not a = a -> Void

{-# LINE 105 "content/part1/Negation.md" #-}
-- | Double negation introduction: a -> ¬(¬a).
doubleNegIntro :: a -> Not (Not a)
doubleNegIntro x k = k x

-- | Triple negation elimination: ¬(¬(¬a)) -> ¬a.
tripleNegElim :: Not (Not (Not a)) -> Not a
tripleNegElim f x = f (\k -> k x)

-- | Functorial action of double negation (`¬¬-map`).
doubleNegMap :: (a -> b) -> Not (Not a) -> Not (Not b)
doubleNegMap f nna nb = nna (\a -> nb (f a))

-- | Monadic bind for double negation (continuation monad at `Void`).
doubleNegBind :: Not (Not a) -> (a -> Not (Not b)) -> Not (Not b)
doubleNegBind nna f nb = nna (\a -> f a nb)

-- | Contraposition: (a -> b) -> (¬b -> ¬a).
contraposition :: (a -> b) -> Not b -> Not a
contraposition f nb x = nb (f x)

-- | De Morgan's law for disjunction holds constructively in both directions:
-- ¬(a ∨ b) ⇔ (¬a ∧ ¬b).
deMorganSum :: Iff (Not (Either a b)) (Not a, Not b)
deMorganSum = Iff toF fromF
  where
    toF nab        = (nab . Left, nab . Right)
    fromF (na, nb) = either na nb

-- | One direction of De Morgan for conjunction holds intuitionistically:
-- (¬a ∨ ¬b) -> ¬(a ∧ b).
deMorganProdPartial :: Either (Not a) (Not b) -> Not (a, b)
deMorganProdPartial (Left na)  (x, _) = na x
deMorganProdPartial (Right nb) (_, y) = nb y

{-# LINE 169 "content/part1/Negation.md" #-}
-- | Excluded Middle is intuitionistically irrefutable: ¬¬(a ∨ ¬a).
irrefutableLEM :: Not (Not (Either a (Not a)))
irrefutableLEM k = k (Right (\x -> k (Left x)))

{-# LINE 210 "content/part1/Negation.md" #-}
type ExcludedMiddle = forall a. Either a (Not a)
type DoubleNegElim  = forall a. Not (Not a) -> a
type Peirce         = forall a b. ((a -> b) -> a) -> a
type ImpliesToOr    = forall a b. (a -> b) -> Either (Not a) b
type DeMorganNot    = forall a b. Not (Not a, Not b) -> Either a b

-- | Excluded Middle implies Double Negation Elimination.
emToDne :: ExcludedMiddle -> DoubleNegElim
emToDne em nna = case em of
  Left a   -> a
  Right na -> absurd (nna na)

-- | Double Negation Elimination implies Peirce's Law.
dneToPeirce :: DoubleNegElim -> Peirce
dneToPeirce dne f = dne (\na -> na (f (\a -> absurd (na a))))

-- | Peirce's Law implies Excluded Middle.
peirceToEm :: Peirce -> ExcludedMiddle
peirceToEm peirce = peirce (\k -> Right (\a -> absurd (k (Left a))))

-- | Excluded Middle implies material implication: (a -> b) -> (¬a ∨ b).
emToImpOr :: ExcludedMiddle -> ImpliesToOr
emToImpOr em f = case em of
  Left a   -> Right (f a)
  Right na -> Left na

-- | Material implication implies Excluded Middle.
impOrToEm :: ImpliesToOr -> ExcludedMiddle
impOrToEm impOr = case impOr id of
  Left na -> Right na
  Right a -> Left a

-- | Excluded Middle implies classical De Morgan: ¬(¬a ∧ ¬b) -> (a ∨ b).
emToDeMorganNot :: ExcludedMiddle -> DeMorganNot
emToDeMorganNot em nn = case em of
  Left a   -> Left a
  Right na -> case em of
    Left b   -> Right b
    Right nb -> absurd (nn (na, nb))

-- | Classical De Morgan (`¬(¬a ∧ ¬b) -> a ∨ b`) implies Excluded Middle!
deMorganNotToEm :: DeMorganNot -> ExcludedMiddle
deMorganNotToEm dm = dm (\pair -> case pair of (na, nna) -> nna na)

{-# LINE 263 "content/part1/Negation.md" #-}
-- | No finite natural number is strictly less than itself: ¬(n < n).
ltIrrefl :: LT' n n -> Void
ltIrrefl (SltS p) = ltIrrefl p

-- | Strict inequality is asymmetric: m < n -> ¬(n < m).
ltAsym :: LT' m n -> Not (LT' n m)
ltAsym (SltS p) (SltS q) = ltAsym p q

-- | No natural number is strictly less than zero: ¬(n < 0).
notLtZero :: Not (LT' n Zero)
notLtZero p = case p of {}

-- | Strict inequality excludes the reverse weak inequality: m < n -> ¬(n ≤ m).
ltToNotGe :: LT' m n -> Not (LE n m)
ltToNotGe (SltS p) (SleS q) = ltToNotGe p q

-- | Weak inequality excludes the reverse strict inequality: m ≤ n -> ¬(n < m).
leToNotGt :: LE m n -> Not (LT' n m)
leToNotGt le lt = ltToNotGe lt le

-- | Negated weak inequality yields strict inequality (`¬≤-to->`): ¬(m ≤ n) -> n < m.
notLeToGt :: foreach (m n :: Nat) -> Not (LE m n) -> LT' n m
notLeToGt Zero     _        nle = absurd (nle ZleN)
notLeToGt (Succ _) Zero     _   = ZltS
notLeToGt (Succ m) (Succ n) nle = SltS (notLeToGt m n (\le -> nle (SleS le)))
