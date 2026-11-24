---
title: "Negation: Negation, with intuitionistic and classical logic"
prev: /Connectives/
next: /Quantifiers/
src: content/part1/Negation.md
module: PLFH.Part1.Negation
plfaChapter: https://plfa.inf.ed.ac.uk/19.08/Negation/
---

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE RankNTypes, TypeOperators #-}
module PLFH.Part1.Negation
  ( Not
  , doubleNegIntro
  , tripleNegElim
  , contraposition
  , deMorganSum
  , deMorganProdPartial
  , irrefutableLEM
  , ExcludedMiddle
  , DoubleNegElim
  , Peirce
  , emToDne
  , dneToPeirce
  , peirceToEm
  , ltIrrefl
  , ltAsym
  ) where

import Data.Void (Void, absurd)
import PLFH.Part1.Decidable (Not)
import PLFH.Part1.Isomorphism (Iff (..))
import PLFH.Part1.Relations (LT' (..))
```

In intuitionistic logic (and therefore under *Propositions as Types* in
Dependent Haskell), negation `Not a` is defined as `a -> Void`. This chapter
develops the fundamental intuitionistic laws of negation and proves the
classical equivalence of **Excluded Middle**, **Double Negation Elimination**,
and **Peirce's Law**.

## Intuitionistic negation laws

```haskell
-- | Double negation introduction: a -> ¬(¬a).
doubleNegIntro :: a -> Not (Not a)
doubleNegIntro x k = k x

-- | Triple negation elimination: ¬(¬(¬a)) -> ¬a.
tripleNegElim :: Not (Not (Not a)) -> Not a
tripleNegElim f x = f (\k -> k x)

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

Moreover, the three classic principles of classical logic—**Excluded Middle**,
**Double Negation Elimination**, and **Peirce's Law**—are constructively
equivalent:

```haskell
type ExcludedMiddle = forall a. Either a (Not a)
type DoubleNegElim  = forall a. Not (Not a) -> a
type Peirce         = forall a b. ((a -> b) -> a) -> a

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
```

## Application: irreflexivity and asymmetry of strict inequality (`<`)

Using `LT'` from [Relations](/Relations/), strict inequality is irreflexive
and asymmetric:

```haskell
-- | No finite natural number is strictly less than itself: ¬(n < n).
ltIrrefl :: LT' n n -> Void
ltIrrefl (SltS p) = ltIrrefl p

-- | Strict inequality is asymmetric: m < n -> ¬(n < m).
ltAsym :: LT' m n -> Not (LT' n m)
ltAsym (SltS p) (SltS q) = ltAsym p q
```

## Changes from PLFA `v19.08`

- Adapted from [Negation (v19.08)](https://plfa.inf.ed.ac.uk/19.08/Negation/)
  ([source](https://github.com/plfa/plfa.github.io/blob/63fcbbe25ec3686ff4c6df2c5b58a96b3a2054f3/src/plfa/part1/Negation.lagda.md)).
- Every intuitionistic negation law, classical equivalence (`emToDne`,
  `dneToPeirce`, `peirceToEm`), `irrefutableLEM`, and `ltIrrefl`/`ltAsym`
  ports directly and passes `-dcore-lint -dstg-lint`!
- As throughout PLFH, soundness of `Not a = a -> Void` relies on our
  structural-recursion / no-bottom proof discipline rather than a compiler
  totality checker.
