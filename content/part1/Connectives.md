---
title: "Connectives: Conjunction, disjunction, and implication"
prev: /Isomorphism/
next: /Negation/
src: content/part1/Connectives.md
module: PLFH.Part1.Connectives
plfaChapter: https://plfa.inf.ed.ac.uk/Connectives/
---

This chapter introduces the **propositional connectives**—conjunction,
disjunction, and implication, together with truth and falsehood—and explores
one of the deepest principles in computer science: **Propositions as Types**
(the Curry–Howard correspondence).

Under *Propositions as Types*, every logical connective corresponds to a
familiar algebraic type constructor in Haskell, and every proof corresponds
to a total Haskell program:

| Logic | PLFA (Agda) | PLFH (Haskell) | Arithmetic analogy |
| --- | --- | --- | --- |
| Conjunction (and) | `A × B` | `(a, b)` | Multiplication (`a × b`) |
| Truth | `⊤` | `()` | One (`1`) |
| Disjunction (or) | `A ⊎ B` | `Either a b` | Addition (`a + b`) |
| Falsehood | `⊥` | `Void` | Zero (`0`) |
| Implication | `A → B` | `a -> b` | Exponentiation (`bᵃ`) |
| Isomorphism | `A ≃ B` | `Iso a b` | Equality (`a = b`) |
| Bi-implication | `A ⇔ B` | `Iff a b` | Mutual inhabitedness (`a > 0 ↔ b > 0`) |

As Philip Wadler notes in *Propositions as Types* (2015), each connective is
characterized by two dual kinds of rules:

- **Introduction rules** explain how to *construct* evidence for a compound
  proposition (constructors in Haskell).
- **Elimination rules** explain how to *use* or *deconstruct* evidence for a
  compound proposition (pattern matching / eliminators in Haskell).

Moreover, if we count the number of inhabitants of finite types—say `Bool`
(2 values) and a 3-element type `Tri` (3 values)—then products multiply
sizes (`(Bool, Tri)` has `2 × 3 = 6` inhabitants), sums add sizes
(`Either Bool Tri` has `2 + 3 = 5` inhabitants), unit `()` has `1`
inhabitant, `Void` has `0` inhabitants, and function spaces exponentiate
sizes (`Bool -> Tri` has `3² = 9` functions while `Tri -> Bool` has
`2³ = 8` functions). Every algebraic law of elementary arithmetic
(`a × b = b × a`, `a × (b + c) = a × b + a × c`, `(cᵃ)ᵇ = cᵃˣᵇ`, `a⁰ = 1`, …)
is therefore a theorem of propositional logic!

## Imports

We import propositional equality `(:~:)`, `Void` and `absurd` from `Data.Void`,
and both `Iff` and polymorphic `Iso` from [Isomorphism](/Isomorphism/).

```haskell
{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
module PLFH.Part1.Connectives
  ( swapProd
  , swapProdRT
  , prodCommIso
  , prodComm
  , prodAssoc
  , prodUnitR
  , prodUnitL
  , prodZeroR
  , prodZeroL
  , swapSum
  , swapSumRT
  , sumCommIso
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

import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void, absurd)
import PLFH.Part1.Isomorphism (Iff (..), Iso (..))
```

## Conjunction (`(a, b)`) and Truth (`()`)

A proof of the conjunction `a ∧ b` is a pair `(x, y) :: (a, b)` holding a
proof `x :: a` and a proof `y :: b`:

- **Introduction:** pairing `(,) :: a -> b -> (a, b)`.
- **Elimination:** projections `fst :: (a, b) -> a` and `snd :: (a, b) -> b`
  (or pattern matching `\(x, y) -> ...`).

**Truth** (`⊤`) is the unit type `()`, which has a single canonical proof
`() :: ()` (introduction) and no non-trivial information to eliminate.

Just like multiplication on the naturals, conjunction is commutative and
associative, has truth `()` as its left and right identity (`a × 1 = a`),
and has falsehood `Void` as its left and right absorbing zero (`a × 0 = 0`):

```haskell
-- | Swap the two components of a pair.
swapProd :: (a, b) -> (b, a)
swapProd (x, y) = (y, x)

-- | Swapping a pair twice returns the original pair.
swapProdRT :: foreach (p :: (a, b)) -> swapProd (swapProd p) :~: p
swapProdRT (_, _) = Refl

-- | Commutativity of conjunction as a true isomorphism: (a, b) ≃ (b, a).
prodCommIso :: Iso (a, b) (b, a)
prodCommIso = MkIso swapProd swapProd swapProdRT swapProdRT

-- | Commutativity of conjunction: (a, b) ⇔ (b, a).
prodComm :: Iff (a, b) (b, a)
prodComm = Iff swapProd swapProd

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

A proof of the disjunction `a ∨ b` is either a proof of `a` tagged with
`Left` or a proof of `b` tagged with `Right`:

- **Introduction:** `Left :: a -> Either a b` and `Right :: b -> Either a b`.
- **Elimination:** case analysis `either :: (a -> c) -> (b -> c) -> Either a b -> c`.

**Falsehood** (`⊥`) is the empty type `Void`, which has **no** constructors
(no introduction rule). Its elimination rule is *ex falso quodlibet*
("from falsehood, anything follows"): `absurd :: Void -> a`.

As the classic anecdote about Bertrand Russell goes, after lecturing that from
a false premise (`2 + 2 = 5`) you can prove anything, a heckler challenged
him: *"Prove that you are the Pope!"* Russell replied at once: *"Subtract 3
from both sides to get `1 = 2`. The Pope and I are two; therefore the Pope
and I are one."* (PLFA illustrates the same rule with the English idiom:
*"if pigs had wings, then I'd be the Queen of Sheba."*)

Just like addition on the naturals, disjunction is commutative and
associative, with falsehood `Void` as its left and right identity
(`a + 0 = a`):

```haskell
-- | Swap the two branches of a sum.
swapSum :: Either a b -> Either b a
swapSum (Left x)  = Right x
swapSum (Right y) = Left y

-- | Swapping a sum twice returns the original sum.
swapSumRT :: foreach (s :: Either a b) -> swapSum (swapSum s) :~: s
swapSumRT (Left _)  = Refl
swapSumRT (Right _) = Refl

-- | Commutativity of disjunction as a true isomorphism: Either a b ≃ Either b a.
sumCommIso :: Iso (Either a b) (Either b a)
sumCommIso = MkIso swapSum swapSum swapSumRT swapSumRT

-- | Commutativity of disjunction: Either a b ⇔ Either b a.
sumComm :: Iff (Either a b) (Either b a)
sumComm = Iff swapSum swapSum

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

## Distributivity

Just as multiplication distributes over addition (`(a + b) × c = a × c + b × c`
and `a × (b + c) = a × b + a × c`), conjunction distributes over disjunction
on both sides:

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
```

## Implication (`a -> b`) and the laws of exponentiation

A proof of the implication `a ⇒ b` is a function `f :: a -> b` transforming
any proof of `a` into a proof of `b`:

- **Introduction:** lambda abstraction `\x -> body`.
- **Elimination:** function application `f x`—which is the logical rule of
  *modus ponens* (from `a -> b` and `a`, deduce `b`).

Under the arithmetic correspondence where `a -> b` corresponds to `bᵃ`,
currying and the standard laws of exponents become propositional theorems:

- **Currying:** `(cᵇ)ᵃ = cᵃˣᵇ` (`(a -> b -> c) ⇔ ((a, b) -> c)`).
- **Sum in the exponent:** `cᵃ⁺ᵇ = cᵃ × cᵇ` (`(Either a b -> c) ⇔ (a -> c, b -> c)`).
- **Product in the base:** `(a × b)ᶜ = aᶜ × bᶜ` (`(c -> (a, b)) ⇔ (c -> a, c -> b)`).
- **Exponent 1:** `a¹ = a` (`(() -> a) ⇔ a`).
- **Exponent 0:** `a⁰ = 1` (`(Void -> a) ⇔ ()`).
- **Base 1:** `1ᵃ = 1` (`(a -> ()) ⇔ ()`).

```haskell
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
```

## Congruence of connectives

Every connective respects logical equivalence (`Iff`): if `a ⇔ a'` and
`b ⇔ b'`, then `(a, b) ⇔ (a', b')`, `Either a b ⇔ Either a' b'`, and
`(a -> b) ⇔ (a' -> b')`. Notice the **contravariance** in the domain of
`arrCong`: to map `(a -> b)` into `(a' -> b')`, we pre-compose with `ga :: a' -> a`
and post-compose with `fb :: b -> b'`:

```haskell
-- | Congruence of conjunction under `Iff`.
prodCong :: Iff a a' -> Iff b b' -> Iff (a, b) (a', b')
prodCong (Iff fa ga) (Iff fb gb) = Iff (\(x, y) -> (fa x, fb y)) (\(x, y) -> (ga x, gb y))

-- | Congruence of disjunction under `Iff`.
sumCong :: Iff a a' -> Iff b b' -> Iff (Either a b) (Either a' b')
sumCong (Iff fa ga) (Iff fb gb) = Iff (either (Left . fa) (Right . fb)) (either (Left . ga) (Right . gb))

-- | Congruence of implication under `Iff` (contravariant in the domain).
arrCong :: Iff a a' -> Iff b b' -> Iff (a -> b) (a' -> b')
arrCong (Iff fa ga) (Iff fb gb) = Iff (\h -> fb . h . ga) (\h -> gb . h . fa)
```

## Isomorphisms vs. logical equivalences

Above we proved commutativity of both products (`prodCommIso :: Iso (a, b) (b, a)`)
and sums (`sumCommIso :: Iso (Either a b) (Either b a)`) as **full polymorphic
isomorphisms** with machine-checked round-trip proofs (`swapProdRT`,
`swapSumRT`), while stating associativity, unit/zero, distributivity, and the
exponential laws via `Iff`. Notice that the exponential laws (like `currying`)
additionally require function extensionality to upgrade from `Iff` to `Iso`—which
neither Agda nor Dependent Haskell proves internally without an axiom.

## Exercises

#### Exercise `×-distrib-⊎` and `→-distrib-⊎` (practice)

Compare `prodDistribSum`, `prodDistribSumL`, `expSum`, and `expProd` above
with the distributive laws of arithmetic from [Induction](/Induction/): why
do `Either (a, b) c` and `(Either a c, Either b c)` admit maps in **both**
directions (`Iff` and `Embed`) yet fail to form an `Iso` (try counting
inhabitants!), and why is there no general equivalence
`Iff (a -> Either b c) (Either (a -> b) (a -> c))`?

#### Exercise `implication-from-⊤-and-⊥` (practice)

Check by hand that for any finite type `a` with `n` inhabitants,
`(() -> a)` has `n¹ = n` inhabitants, `(Void -> a)` has `n⁰ = 1` inhabitant
(`absurd`), and `(a -> ())` has `1ⁿ = 1` inhabitant (`const ()`). What about
`a -> Void`? That is **negation**, the subject of the very next chapter!

## Changes from PLFA

- Adapted from [Connectives](https://plfa.inf.ed.ac.uk/Connectives/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part1/Connectives.lagda.md)),
  licensed under CC BY 4.0.
- Uses standard Haskell `(,)`, `Either`, `()`, and `Void` directly.
- Proved polymorphic product & sum commutativity as genuine isomorphisms
  (`prodCommIso :: Iso (a, b) (b, a)` and `sumCommIso :: Iso (Either a b) (Either b a)`),
  along with all commutative semiring, exponential (`currying`, `expSum`,
  `expProd`, `expUnit`, `expZero`, `expToUnit`), and congruence (`prodCong`,
  `sumCong`, `arrCong`) laws as constructive `Iff` equivalences.
