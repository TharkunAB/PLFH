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
Because `-XDependentTypes` enables `-XNoListTuplePuns` by default (so list
constructors `[]` and `[0, 1]` need no leading `'` tick in types), we also
enable `ListTuplePuns` here to keep familiar Haskell `(a, b)` and `()` tuple
notation in types.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module PLFH.Part1.Connectives
  ( swapProd
  , swapProdRT
  , prodCommIso
  , prodComm
  , prodAssocTo
  , prodAssocFrom
  , prodAssocIso
  , prodAssoc
  , prodUnitRTo
  , prodUnitRFrom
  , prodUnitRIso
  , prodUnitR
  , prodUnitLTo
  , prodUnitLFrom
  , prodUnitLIso
  , prodUnitL
  , prodZeroRTo
  , prodZeroRFrom
  , prodZeroRIso
  , prodZeroR
  , prodZeroLTo
  , prodZeroLFrom
  , prodZeroLIso
  , prodZeroL
  , swapSum
  , swapSumRT
  , sumCommIso
  , sumComm
  , sumAssocTo
  , sumAssocFrom
  , sumAssocIso
  , sumAssoc
  , sumZeroR
  , sumZeroL
  , prodDistribSumTo
  , prodDistribSumFrom
  , prodDistribSumIso
  , prodDistribSum
  , prodDistribSumLTo
  , prodDistribSumLFrom
  , prodDistribSumLIso
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
import PLFH.Part1.Isomorphism (Iff (..), Iso (..), embedImpliesIff, isoImpliesEmbed)
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
and has falsehood `Void` as its left and right absorbing zero (`a × 0 = 0`)—all
proved as **full polymorphic isomorphisms (`Iso`)** with machine-checked
round-trip proofs:

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
prodComm = embedImpliesIff (isoImpliesEmbed prodCommIso)

-- | Forward map for product associativity.
prodAssocTo :: ((a, b), c) -> (a, (b, c))
prodAssocTo ((x, y), z) = (x, (y, z))

-- | Backward map for product associativity.
prodAssocFrom :: (a, (b, c)) -> ((a, b), c)
prodAssocFrom (x, (y, z)) = ((x, y), z)

prodAssocLR :: foreach (p :: ((a, b), c)) -> prodAssocFrom (prodAssocTo p) :~: p
prodAssocLR ((_, _), _) = Refl

prodAssocRL :: foreach (p :: (a, (b, c))) -> prodAssocTo (prodAssocFrom p) :~: p
prodAssocRL (_, (_, _)) = Refl

-- | Associativity of conjunction as a true isomorphism: ((a, b), c) ≃ (a, (b, c)).
prodAssocIso :: Iso ((a, b), c) (a, (b, c))
prodAssocIso = MkIso prodAssocTo prodAssocFrom prodAssocLR prodAssocRL

-- | Associativity of conjunction: ((a, b), c) ⇔ (a, (b, c)).
prodAssoc :: Iff ((a, b), c) (a, (b, c))
prodAssoc = embedImpliesIff (isoImpliesEmbed prodAssocIso)

-- | Right-identity maps for conjunction.
prodUnitRTo :: (a, ()) -> a
prodUnitRTo (x, ()) = x

prodUnitRFrom :: a -> (a, ())
prodUnitRFrom x = (x, ())

prodUnitRLR :: foreach (p :: (a, ())) -> prodUnitRFrom (prodUnitRTo p) :~: p
prodUnitRLR (_, ()) = Refl

prodUnitRRL :: foreach (x :: a) -> prodUnitRTo (prodUnitRFrom x) :~: x
prodUnitRRL _ = Refl

-- | Right identity of conjunction as a true isomorphism: (a, ()) ≃ a.
prodUnitRIso :: Iso (a, ()) a
prodUnitRIso = MkIso prodUnitRTo prodUnitRFrom prodUnitRLR prodUnitRRL

-- | Right identity of conjunction: (a, ()) ⇔ a.
prodUnitR :: Iff (a, ()) a
prodUnitR = embedImpliesIff (isoImpliesEmbed prodUnitRIso)

-- | Left-identity maps for conjunction.
prodUnitLTo :: ((), a) -> a
prodUnitLTo ((), x) = x

prodUnitLFrom :: a -> ((), a)
prodUnitLFrom x = ((), x)

prodUnitLLR :: foreach (p :: ((), a)) -> prodUnitLFrom (prodUnitLTo p) :~: p
prodUnitLLR ((), _) = Refl

prodUnitLRL :: foreach (x :: a) -> prodUnitLTo (prodUnitLFrom x) :~: x
prodUnitLRL _ = Refl

-- | Left identity of conjunction as a true isomorphism: ((), a) ≃ a.
prodUnitLIso :: Iso ((), a) a
prodUnitLIso = MkIso prodUnitLTo prodUnitLFrom prodUnitLLR prodUnitLRL

-- | Left identity of conjunction: ((), a) ⇔ a.
prodUnitL :: Iff ((), a) a
prodUnitL = embedImpliesIff (isoImpliesEmbed prodUnitLIso)

-- | Right-zero maps for conjunction.
prodZeroRTo :: (a, Void) -> Void
prodZeroRTo (_, v) = v

prodZeroRFrom :: Void -> (a, Void)
prodZeroRFrom = absurd

-- | Right zero of conjunction as a true isomorphism: (a, Void) ≃ Void.
prodZeroRIso :: forall a. Iso (a, Void) Void
prodZeroRIso = go prodZeroRTo prodZeroRFrom
  where
    go :: foreach (t :: (a, Void) -> Void) -> foreach (f :: Void -> (a, Void))
       -> Iso (a, Void) Void
    go t f = MkIso t f lr rl
      where
        lr :: foreach (p :: (a, Void)) -> f (t p) :~: p
        lr (_, v) = case v of {}
        rl :: foreach (v :: Void) -> t (f v) :~: v
        rl v = case v of {}

-- | Right zero of conjunction: (a, Void) ⇔ Void.
prodZeroR :: Iff (a, Void) Void
prodZeroR = embedImpliesIff (isoImpliesEmbed prodZeroRIso)

-- | Left-zero maps for conjunction.
prodZeroLTo :: (Void, a) -> Void
prodZeroLTo (v, _) = v

prodZeroLFrom :: Void -> (Void, a)
prodZeroLFrom = absurd

-- | Left zero of conjunction as a true isomorphism: (Void, a) ≃ Void.
prodZeroLIso :: forall a. Iso (Void, a) Void
prodZeroLIso = go prodZeroLTo prodZeroLFrom
  where
    go :: foreach (t :: (Void, a) -> Void) -> foreach (f :: Void -> (Void, a))
       -> Iso (Void, a) Void
    go t f = MkIso t f lr rl
      where
        lr :: foreach (p :: (Void, a)) -> f (t p) :~: p
        lr (v, _) = case v of {}
        rl :: foreach (v :: Void) -> t (f v) :~: v
        rl v = case v of {}

-- | Left zero of conjunction: (Void, a) ⇔ Void.
prodZeroL :: Iff (Void, a) Void
prodZeroL = embedImpliesIff (isoImpliesEmbed prodZeroLIso)
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
(`a + 0 = a`)—again proved as full polymorphic `Iso` isomorphisms:

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
sumComm = embedImpliesIff (isoImpliesEmbed sumCommIso)

-- | Forward map for disjunction associativity.
sumAssocTo :: Either (Either a b) c -> Either a (Either b c)
sumAssocTo (Left (Left x))  = Left x
sumAssocTo (Left (Right y)) = Right (Left y)
sumAssocTo (Right z)        = Right (Right z)

-- | Backward map for disjunction associativity.
sumAssocFrom :: Either a (Either b c) -> Either (Either a b) c
sumAssocFrom (Left x)          = Left (Left x)
sumAssocFrom (Right (Left y))  = Left (Right y)
sumAssocFrom (Right (Right z)) = Right z

sumAssocLR :: foreach (s :: Either (Either a b) c) -> sumAssocFrom (sumAssocTo s) :~: s
sumAssocLR (Left (Left _))  = Refl
sumAssocLR (Left (Right _)) = Refl
sumAssocLR (Right _)        = Refl

sumAssocRL :: foreach (s :: Either a (Either b c)) -> sumAssocTo (sumAssocFrom s) :~: s
sumAssocRL (Left _)          = Refl
sumAssocRL (Right (Left _))  = Refl
sumAssocRL (Right (Right _)) = Refl

-- | Associativity of disjunction as a true isomorphism: Either (Either a b) c ≃ Either a (Either b c).
sumAssocIso :: Iso (Either (Either a b) c) (Either a (Either b c))
sumAssocIso = MkIso sumAssocTo sumAssocFrom sumAssocLR sumAssocRL

-- | Associativity of disjunction: Either (Either a b) c ⇔ Either a (Either b c).
sumAssoc :: Iff (Either (Either a b) c) (Either a (Either b c))
sumAssoc = embedImpliesIff (isoImpliesEmbed sumAssocIso)

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
on both sides as full polymorphic isomorphisms:

```haskell
-- | Forward and backward maps for right distributivity.
prodDistribSumTo :: (Either a b, c) -> Either (a, c) (b, c)
prodDistribSumTo (Left x, z)  = Left (x, z)
prodDistribSumTo (Right y, z) = Right (y, z)

prodDistribSumFrom :: Either (a, c) (b, c) -> (Either a b, c)
prodDistribSumFrom (Left (x, z))  = (Left x, z)
prodDistribSumFrom (Right (y, z)) = (Right y, z)

prodDistribSumLR :: foreach (p :: (Either a b, c)) -> prodDistribSumFrom (prodDistribSumTo p) :~: p
prodDistribSumLR (Left _, _)  = Refl
prodDistribSumLR (Right _, _) = Refl

prodDistribSumRL :: foreach (s :: Either (a, c) (b, c)) -> prodDistribSumTo (prodDistribSumFrom s) :~: s
prodDistribSumRL (Left (_, _))  = Refl
prodDistribSumRL (Right (_, _)) = Refl

-- | Right distributivity as a true isomorphism: (Either a b, c) ≃ Either (a, c) (b, c).
prodDistribSumIso :: Iso (Either a b, c) (Either (a, c) (b, c))
prodDistribSumIso = MkIso prodDistribSumTo prodDistribSumFrom prodDistribSumLR prodDistribSumRL

-- | Right distributivity: (Either a b, c) ⇔ Either (a, c) (b, c).
prodDistribSum :: Iff (Either a b, c) (Either (a, c) (b, c))
prodDistribSum = embedImpliesIff (isoImpliesEmbed prodDistribSumIso)

-- | Forward and backward maps for left distributivity.
prodDistribSumLTo :: (a, Either b c) -> Either (a, b) (a, c)
prodDistribSumLTo (x, Left y)  = Left (x, y)
prodDistribSumLTo (x, Right z) = Right (x, z)

prodDistribSumLFrom :: Either (a, b) (a, c) -> (a, Either b c)
prodDistribSumLFrom (Left (x, y))  = (x, Left y)
prodDistribSumLFrom (Right (x, z)) = (x, Right z)

prodDistribSumLLR :: foreach (p :: (a, Either b c)) -> prodDistribSumLFrom (prodDistribSumLTo p) :~: p
prodDistribSumLLR (_, Left _)  = Refl
prodDistribSumLLR (_, Right _) = Refl

prodDistribSumLRL :: foreach (s :: Either (a, b) (a, c)) -> prodDistribSumLTo (prodDistribSumLFrom s) :~: s
prodDistribSumLRL (Left (_, _))  = Refl
prodDistribSumLRL (Right (_, _)) = Refl

-- | Left distributivity as a true isomorphism: (a, Either b c) ≃ Either (a, b) (a, c).
prodDistribSumLIso :: Iso (a, Either b c) (Either (a, b) (a, c))
prodDistribSumLIso = MkIso prodDistribSumLTo prodDistribSumLFrom prodDistribSumLLR prodDistribSumLRL

-- | Left distributivity: (a, Either b c) ⇔ Either (a, b) (a, c).
prodDistribSumL :: Iff (a, Either b c) (Either (a, b) (a, c))
prodDistribSumL = embedImpliesIff (isoImpliesEmbed prodDistribSumLIso)
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

Above we proved ten of the twelve commutative semiring laws—product & sum
commutativity, associativity, product units & absorbing zeros, and left/right
distributivity—as **full polymorphic isomorphisms (`Iso`)** with
machine-checked round-trip proofs (alongside `Iff` projections). Upgrading
`sumZeroR` (`Either a Void ⇔ a`) and `sumZeroL` (`Either Void a ⇔ a`) to `Iso`
requires certifying checked equations for functions with an unreachable `Void`
branch (`Right v -> case v of {}`, tracked in
[`R13_VoidAbsurdBranchOpenEq.hs`](https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_VoidAbsurdBranchOpenEq.hs)),
whereas upgrading the exponential laws (`currying`, `expSum`, `expProd`,
`expUnit`, `expZero`, `expToUnit`) requires **function extensionality**—which
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
- Proved ten commutative semiring laws (product & sum commutativity and
  associativity, product units & zeros, and left/right distributivity) as
  genuine polymorphic isomorphisms (`prodCommIso`, `prodAssocIso`,
  `prodUnitRIso`, `prodUnitLIso`, `prodZeroRIso`, `prodZeroLIso`,
  `sumCommIso`, `sumAssocIso`, `prodDistribSumIso`, `prodDistribSumLIso`),
  along with `sumZeroR`/`sumZeroL`, exponential (`currying`, `expSum`,
  `expProd`, `expUnit`, `expZero`, `expToUnit`), and congruence (`prodCong`,
  `sumCong`, `arrCong`) laws as constructive `Iff` equivalences.
