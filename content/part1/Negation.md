---
title: "Negation: Negation, with intuitionistic and classical logic"
prev: /Connectives/
next: /Quantifiers/
src: content/part1/Negation.md
module: PLFH.Part1.Negation
plfaChapter: https://plfa.inf.ed.ac.uk/Negation/
---

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE RankNTypes, TypeOperators #-}
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
  , DeMorganProd
  , emToDne
  , dneToPeirce
  , peirceToEm
  , emToImpOr
  , impOrToEm
  , emToDeMorganProd
  , ltIrrefl
  , ltAsym
  , notLtZero
  , ltToNotGe
  , leToNotGt
  , notLeToGt
  ) where

import Data.Void (Void, absurd)
import HaskLib.Nat (Nat (..))
import PLFH.Part1.Decidable (Not)
import PLFH.Part1.Isomorphism (Iff (..))
import PLFH.Part1.Relations (LE (..), LT' (..))
```

In intuitionistic logic (and therefore under *Propositions as Types* in
Dependent Haskell), negation `Not a` is defined as `a -> Void`. This chapter
develops the fundamental intuitionistic laws of negation (including the
double-negation monad), proves the classical equivalence of **Excluded Middle**,
**Double Negation Elimination**, **Peirce's Law**, **Material Implication**,
and **De Morgan's Law**, and connects negation to order relations on `Nat`.

## Intuitionistic negation laws

```haskell
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
    toF nab       = (nab . Left, nab . Right)
    fromF (na, nb) = either na nb

-- | One direction of De Morgan for conjunction holds intuitionistically:
-- (¬a ∨ ¬b) -> ¬(a ∧ b).
deMorganProdPartial :: Either (Not a) (Not b) -> Not (a, b)
deMorganProdPartial (Left na)  (x, _) = na x
deMorganProdPartial (Right nb) (_, y) = nb y
```

## Irrefutability of Excluded Middle & Classical Equivalences

While intuitionistic logic does not prove `Either a (Not a)` for arbitrary
`a`, it *does* prove that Excluded Middle can never be refuted (`¬¬(a ∨ ¬a)`):

```haskell
-- | Excluded Middle is intuitionistically irrefutable: ¬¬(a ∨ ¬a).
irrefutableLEM :: Not (Not (Either a (Not a)))
irrefutableLEM k = k (Right (\x -> k (Left x)))
```

Moreover, the classic principles of classical logic—**Excluded Middle**,
**Double Negation Elimination**, **Peirce's Law**, **Material Implication**,
and **De Morgan's Law for Conjunction**—are constructively inter-derivable:

```haskell
type ExcludedMiddle = forall a. Either a (Not a)
type DoubleNegElim  = forall a. Not (Not a) -> a
type Peirce         = forall a b. ((a -> b) -> a) -> a
type ImpliesToOr    = forall a b. (a -> b) -> Either (Not a) b
type DeMorganProd   = forall a b. Not (a, b) -> Either (Not a) (Not b)

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

-- | Excluded Middle implies classical De Morgan: ¬(a ∧ b) -> (¬a ∨ ¬b).
emToDeMorganProd :: ExcludedMiddle -> DeMorganProd
emToDeMorganProd em nab = case em of
  Left a   -> Right (\b -> nab (a, b))
  Right na -> Left na
```

## Application: negation and order relations (`<`, `≤`)

Using `LT'` and `LE` from [Relations](/Relations/), strict inequality is
irreflexive and asymmetric, and `¬(m ≤ n)` constructively implies `n < m`:

```haskell
-- | No finite natural number is strictly less than itself: ¬(n < n).
ltIrrefl :: LT' n n -> Void
ltIrrefl (SltS p) = ltIrrefl p

-- | Strict inequality is asymmetric: m < n -> ¬(n < m).
ltAsym :: LT' m n -> Not (LT' n m)
ltAsym (SltS p) (SltS q) = ltAsym p q

-- | No natural number is strictly less than zero: ¬(n < 0).
notLtZero :: Not (LT' n 'Zero)
notLtZero p = case p of {}

-- | Strict inequality excludes the reverse weak inequality: m < n -> ¬(n ≤ m).
ltToNotGe :: LT' m n -> Not (LE n m)
ltToNotGe (SltS p) (SleS q) = ltToNotGe p q

-- | Weak inequality excludes the reverse strict inequality: m ≤ n -> ¬(n < m).
leToNotGt :: LE m n -> Not (LT' n m)
leToNotGt le lt = ltToNotGe lt le

-- | Negated weak inequality yields strict inequality (`¬≤-to->`): ¬(m ≤ n) -> n < m.
notLeToGt :: foreach (m :: Nat) -> foreach (n :: Nat) -> Not (LE m n) -> LT' n m
notLeToGt Zero     _        nle = absurd (nle ZleN)
notLeToGt (Succ _) Zero     _   = ZltS
notLeToGt (Succ m) (Succ n) nle = SltS (notLeToGt m n (\le -> nle (SleS le)))
```

## Changes from PLFA

- Adapted from [Negation](https://plfa.inf.ed.ac.uk/Negation/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part1/Negation.lagda.md)).
- Every intuitionistic negation law, double-negation monad operation,
  classical equivalence (`emToDne`, `dneToPeirce`, `peirceToEm`, `emToImpOr`,
  `impOrToEm`, `emToDeMorganProd`), `irrefutableLEM`, and order-negation lemma
  (`ltIrrefl`, `ltAsym`, `notLtZero`, `ltToNotGe`, `leToNotGt`, `notLeToGt`)
  ports directly and passes `-dcore-lint -dstg-lint`!
- As throughout PLFH, soundness of `Not a = a -> Void` relies on our
  structural-recursion / no-bottom proof discipline rather than a compiler
  totality checker.
