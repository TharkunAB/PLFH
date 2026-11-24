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
  , sumComm
  , sumAssoc
  , sumZeroR
  , sumZeroL
  , prodDistribSum
  , currying
  , expSum
  , expProd
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

Conjunction is commutative and associative, with `()` as its identity:

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

## Distributivity and Currying

Conjunction distributes over disjunction, and implication satisfies the laws
of exponentiation (currying, `c^(a + b) ⇔ c^a × c^b`, and `(a × b)^c ⇔ a^c × b^c`):

```haskell
-- | Conjunction distributes over disjunction: (Either a b, c) ⇔ Either (a, c) (b, c).
prodDistribSum :: Iff (Either a b, c) (Either (a, c) (b, c))
prodDistribSum = Iff toF fromF
  where
    toF (Left x, z)  = Left (x, z)
    toF (Right y, z) = Right (y, z)

    fromF (Left (x, z))  = (Left x, z)
    fromF (Right (y, z)) = (Right y, z)

-- | Currying: (a -> b -> c) ⇔ ((a, b) -> c).
currying :: Iff (a -> b -> c) ((a, b) -> c)
currying = Iff uncurry curry

-- | Implication from a disjunction is a pair of implications.
expSum :: Iff (Either a b -> c) (a -> c, b -> c)
expSum = Iff (\f -> (f . Left, f . Right)) (\(f, g) -> either f g)

-- | Implication into a conjunction is a pair of implications.
expProd :: Iff (c -> (a, b)) (c -> a, c -> b)
expProd = Iff (\f -> (fst . f, snd . f)) (\(f, g) x -> (f x, g x))
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
- Proved all algebraic laws as constructive `Iff` equivalences; noted the
  upgrade to `Iso` with `[WIP NOTICE]`.
