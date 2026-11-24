---
title: "Connectives: Conjunction, disjunction, and implication"
prev: /Isomorphism/
next: /Negation/
src: content/part1/Connectives.md
module: PLFH.Part1.Connectives
plfaChapter: https://plfa.inf.ed.ac.uk/22.08/Connectives/
---

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
module PLFH.Part1.Connectives
  ( prodComm
  , prodAssoc
  , prodUnitR
  , prodUnitL
  , prodZeroR
  , prodZeroL
  , sumComm
  , sumAssoc
  , sumZeroR
  , sumZeroL
  , prodDistribSum
  , prodDistribSumL
  , currying
  , expSum
  , expProd
  , expUnit
  , expZero
  , expToUnit
  , prodCong
  , sumCong
  , arrCong
  ) where

import Data.Void (Void, absurd)
import PLFH.Part1.Isomorphism (Iff (..))
```

Under *Propositions as Types*, the logical connectives correspond directly
to standard Haskell algebraic types:

| Logic | PLFA (Agda) | PLFH (Haskell) |
| --- | --- | --- |
| Conjunction (and) | `A × B` | `(a, b)` |
| Truth | `⊤` | `()` |
| Disjunction (or) | `A ⊎ B` | `Either a b` |
| Falsehood | `⊥` | `Void` |
| Implication | `A → B` | `a -> b` |
| Bi-implication | `A ⇔ B` | `Iff a b` |

## Conjunction (`(a, b)`) and Truth (`()`)

Conjunction is commutative and associative, with `()` as its identity and
`Void` as its absorbing zero:

```haskell
-- | Commutativity of conjunction: (a, b) ⇔ (b, a).
prodComm :: Iff (a, b) (b, a)
prodComm = Iff (\(x, y) -> (y, x)) (\(y, x) -> (x, y))

-- | Associativity of conjunction: ((a, b), c) ⇔ (a, (b, c)).
prodAssoc :: Iff ((a, b), c) (a, (b, c))
prodAssoc = Iff (\((x, y), z) -> (x, (y, z))) (\(x, (y, z)) -> ((x, y), z))

-- | Right identity of conjunction: (a, ()) ⇔ a.
prodUnitR :: Iff (a, ()) a
prodUnitR = Iff fst (\x -> (x, ()))

-- | Left identity of conjunction: ((), a) ⇔ a.
prodUnitL :: Iff ((), a) a
prodUnitL = Iff snd (\x -> ((), x))

-- | Right zero of conjunction: (a, Void) ⇔ Void.
prodZeroR :: Iff (a, Void) Void
prodZeroR = Iff snd absurd

-- | Left zero of conjunction: (Void, a) ⇔ Void.
prodZeroL :: Iff (Void, a) Void
prodZeroL = Iff fst absurd
```

## Disjunction (`Either a b`) and Falsehood (`Void`)

Disjunction is commutative and associative, with `Void` as its identity:

```haskell
-- | Commutativity of disjunction: Either a b ⇔ Either b a.
sumComm :: Iff (Either a b) (Either b a)
sumComm = Iff (either Right Left) (either Right Left)

-- | Associativity of disjunction: Either (Either a b) c ⇔ Either a (Either b c).
sumAssoc :: Iff (Either (Either a b) c) (Either a (Either b c))
sumAssoc = Iff toF fromF
  where
    toF (Left (Left x))  = Left x
    toF (Left (Right y)) = Right (Left y)
    toF (Right z)        = Right (Right z)

    fromF (Left x)          = Left (Left x)
    fromF (Right (Left y))  = Left (Right y)
    fromF (Right (Right z)) = Right z

-- | Right identity of disjunction: Either a Void ⇔ a.
sumZeroR :: Iff (Either a Void) a
sumZeroR = Iff (either id absurd) Left

-- | Left identity of disjunction: Either Void a ⇔ a.
sumZeroL :: Iff (Either Void a) a
sumZeroL = Iff (either absurd id) Right
```

## Distributivity, Currying, Exponential Laws, and Congruence

Conjunction distributes over disjunction on both sides, implication satisfies
the full algebraic laws of exponentiation, and every connective respects `Iff`:

```haskell
-- | Right distributivity: (Either a b, c) ⇔ Either (a, c) (b, c).
prodDistribSum :: Iff (Either a b, c) (Either (a, c) (b, c))
prodDistribSum = Iff toF fromF
  where
    toF (Left x, z)  = Left (x, z)
    toF (Right y, z) = Right (y, z)

    fromF (Left (x, z))  = (Left x, z)
    fromF (Right (y, z)) = (Right y, z)

-- | Left distributivity: (a, Either b c) ⇔ Either (a, b) (a, c).
prodDistribSumL :: Iff (a, Either b c) (Either (a, b) (a, c))
prodDistribSumL = Iff toF fromF
  where
    toF (x, Left y)  = Left (x, y)
    toF (x, Right z) = Right (x, z)

    fromF (Left (x, y))  = (x, Left y)
    fromF (Right (x, z)) = (x, Right z)

-- | Currying: (a -> b -> c) ⇔ ((a, b) -> c).
currying :: Iff (a -> b -> c) ((a, b) -> c)
currying = Iff uncurry curry

-- | Implication from a disjunction is a pair of implications: c^(a+b) ⇔ c^a × c^b.
expSum :: Iff (Either a b -> c) (a -> c, b -> c)
expSum = Iff (\f -> (f . Left, f . Right)) (\(f, g) -> either f g)

-- | Implication into a conjunction is a pair of implications: (a×b)^c ⇔ a^c × b^c.
expProd :: Iff (c -> (a, b)) (c -> a, c -> b)
expProd = Iff (\f -> (fst . f, snd . f)) (\(f, g) x -> (f x, g x))

-- | Exponent 1: (() -> a) ⇔ a.
expUnit :: Iff (() -> a) a
expUnit = Iff (\f -> f ()) const

-- | Exponent 0: (Void -> a) ⇔ ().
expZero :: Iff (Void -> a) ()
expZero = Iff (const ()) (\() -> absurd)

-- | Base 1: (a -> ()) ⇔ ().
expToUnit :: Iff (a -> ()) ()
expToUnit = Iff (const ()) (\() _ -> ())

-- | Congruence of conjunction, disjunction, and implication under `Iff`.
prodCong :: Iff a a' -> Iff b b' -> Iff (a, b) (a', b')
prodCong (Iff fa ga) (Iff fb gb) = Iff (\(x, y) -> (fa x, fb y)) (\(x, y) -> (ga x, gb y))

sumCong :: Iff a a' -> Iff b b' -> Iff (Either a b) (Either a' b')
sumCong (Iff fa ga) (Iff fb gb) = Iff (either (Left . fa) (Right . fb)) (either (Left . ga) (Right . gb))

arrCong :: Iff a a' -> Iff b b' -> Iff (a -> b) (a' -> b')
arrCong (Iff fa ga) (Iff fb gb) = Iff (\h -> fb . h . ga) (\h -> gb . h . fa)
```

<div class="wip-notice">
<strong>[WIP NOTICE — Upgrading <code>Iff</code> to full <code>Iso</code> (R03/R04)]</strong>
In PLFA, these laws are stated as full isomorphisms <code>_≃_</code>
(including round-trip equations, and using function extensionality for
<code>currying</code>). Upgrading <code>Iff</code> to <code>Iso</code>
waits on polymorphic retained function fields and higher-rank
<code>foreach</code> fields tracked in
<a href="/Isomorphism/">Isomorphism</a>.
</div>

## Changes from PLFA `v22.08`

- Adapted from [Connectives (v22.08)](https://plfa.inf.ed.ac.uk/22.08/Connectives/)
  ([source](https://github.com/plfa/plfa.github.io/blob/e2d545f3df0db4d4206c5448735665abde02d81f/src/plfa/part1/Connectives.lagda.md)).
- Used standard Haskell `(,)`, `Either`, `()`, and `Void`.
- Proved all commutative semiring, exponential (`currying`, `expSum`, `expProd`,
  `expUnit`, `expZero`, `expToUnit`), and congruence (`prodCong`, `sumCong`,
  `arrCong`) laws as constructive `Iff` equivalences; noted the upgrade to `Iso`
  with `[WIP NOTICE]`.
