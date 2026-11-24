---
title: "Negation: Negation, with intuitionistic and classical logic"
prev: /Connectives/
next: /Quantifiers/
src: content/part1/Negation.md
module: PLFH.Part1.Negation
plfaChapter: https://plfa.inf.ed.ac.uk/Negation/
---

This chapter introduces **negation**, explores the fundamental distinction
between **intuitionistic** and **classical** logic, proves that the Law of
the Excluded Middle is intuitionistically *irrefutable*, shows that the
classic principles of classical logic are constructively inter-derivable, and
applies negation to order relations on natural numbers.

## Imports

We import `Void` and `absurd` from `Data.Void`, `Nat` from `HaskLib.Nat`,
`Not` from [Decidable](/Decidable/), `Iff` from [Isomorphism](/Isomorphism/),
and `LE` / `LT'` from [Relations](/Relations/).

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
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
import HaskLib.Nat (Nat (..))
import PLFH.Part1.Decidable (Not)
import PLFH.Part1.Isomorphism (Iff (..))
import PLFH.Part1.Relations (LE (..), LT' (..))
```

## Negation (`¬`)

Given a proposition `a`, its negation `Not a` (written `¬ A` in PLFA) holds
when `a` cannot hold. Under *Propositions as Types*, we define negation as
implication of falsehood:

```haskell
-- From PLFH.Part1.Decidable:
-- type Not a = a -> Void
```

This is *reductio ad absurdum*: if assuming evidence of `a` lets us construct
a value of the empty type `Void` (a contradiction), then `Not a` holds.
Under the arithmetic analogy from [Connectives](/Connectives/), where
implication is exponentiation (`bᵃ`) and `Void` is `0`, negation `a -> Void`
corresponds to `0ᵃ`:

- `0⁰ = 1` (if `a` is uninhabited, `Void -> Void` has one inhabitant, `id` / `absurd`),
- `0ⁿ = 0` for `n > 0` (if `a` is inhabited, there is no total function `a -> Void`).

<div class="note-box">
<strong>Totality note:</strong>
In Agda, <code>¬ A = A → ⊥</code> is sound because Agda rejects
non-terminating functions and <code>undefined</code>. In Haskell,
<code>undefined :: a -&gt; Void</code> typechecks, so every proof of
<code>Not a</code> in PLFH must discharge its hypothesis constructively
via structural recursion and impossible GADT pattern matches
(<code>case ... of {}</code>) with zero bottoms or loops.
</div>

### Intuitionistic negation laws

In *classical* logic, `a` is equivalent to `Not (Not a)`. In *intuitionistic*
logic—and therefore in Dependent Haskell—we have only half of that
equivalence: `a` always implies `Not (Not a)` (`doubleNegIntro`), and triple
negation collapses back to single negation (`tripleNegElim`). Double negation
also forms a **monad** (`doubleNegIntro`, `doubleNegMap`, `doubleNegBind`,
the continuation monad at `Void`).

Moreover, implication supports **contraposition** (`(a -> b) -> (Not b -> Not a)`),
and **De Morgan's Law** holds constructively in both directions for
disjunction (`Not (Either a b) ⇔ (Not a, Not b)`), while only one direction
holds intuitionistically for conjunction (`Either (Not a) (Not b) -> Not (a, b)`):

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
    toF nab        = (nab . Left, nab . Right)
    fromF (na, nb) = either na nb

-- | One direction of De Morgan for conjunction holds intuitionistically:
-- (¬a ∨ ¬b) -> ¬(a ∧ b).
deMorganProdPartial :: Either (Not a) (Not b) -> Not (a, b)
deMorganProdPartial (Left na)  (x, _) = na x
deMorganProdPartial (Right nb) (_, y) = nb y
```

## Intuitionistic and classical logic

In Gilbert and Sullivan's *The Gondoliers*, Casilda is told that as an infant
she was married to the heir of the King of Batavia, but that due to a mix-up
no one knows which of two gondoliers, Marco or Giuseppe, is the heir.
Alarmed, she wails: *"Then do you mean to say that I am married to one of two
gondoliers, but it is impossible to say which?"* To which the reply is:
*"Without any doubt of any kind whatever."*

Intuitionists insist upon a constructive notion of truth: a proof of a
disjunction `Either a b` must actually exhibit *which* disjunct holds (`Left x`
or `Right y`), so they reject the claim that Casilda is married to Marco or
Giuseppe until one is identified. (Perhaps Gilbert and Sullivan anticipated
intuitionism: at the end of the operetta, the heir turns out to be a *third*
man, Luiz, with whom Casilda is conveniently already in love!)

For the same reason, intuitionistic logic rejects the **Law of the Excluded
Middle** (`Either a (Not a)` for arbitrary `a`), because it gives no clue as
to *which* of `a` or `Not a` holds. Heyting formalized intuitionistic logic,
showing that adding Excluded Middle recovers Hilbert's classical logic;
Kolmogorov showed that a double-negation translation embeds all of classical
logic faithfully inside intuitionistic logic.

## Excluded Middle is irrefutable

Although intuitionistic logic cannot prove `Either a (Not a)`, it *can* prove
that Excluded Middle can never be refuted—that is, `Not (Not (Either a (Not a)))`:

```haskell
-- | Excluded Middle is intuitionistically irrefutable: ¬¬(a ∨ ¬a).
irrefutableLEM :: Not (Not (Either a (Not a)))
irrefutableLEM k = k (Right (\x -> k (Left x)))
```

How does this astonishing one-line proof work? Given a continuation
`k :: Either a (Not a) -> Void`, we don't yet have a value of type `a`, so we
first offer `k` the right disjunct `Right (\x -> ...) :: Either a (Not a)`,
promising a proof of `Not a`. If `k` ever invokes that callback with an actual
value `x :: a`, we now *do* hold an `a`, so we invoke `k` a second time with
`Left x`!

As PLFA relates (adapting Peter Selinger's story of the king, the wizard, and
the Philosopher's Stone, from Wadler's *Call-by-Value is Dual to Call-by-Name*,
ICFP 2003):

> Once upon a time, the devil approached a man and made an offer:
> *"Either (a) I will give you one billion dollars, or (b) I will grant you
> any wish if you pay me one billion dollars. Of course, I get to choose
> whether I offer (a) or (b)."*
>
> The man accepted. The devil chose *(b)*. Years passed; the man worked hard
> (and did some questionable things) until at last he amassed a billion
> dollars and brought it in a valise to claim his wish.
>
> The devil took the valise and smiled: *"Oh, did I say (b) before? I'm so
> sorry—I meant (a). It is my great pleasure to give you one billion dollars."*
> And the devil handed back the very same valise!

In our proof, `Right (\x -> ...)` is the devil choosing *(b)*, and calling
`k (Left x)` once `x` arrives is the devil backtracking to *(a)* with the
man's own billion dollars!

## Classical equivalences

Even without assuming classical axioms, we can prove constructively that five
famous classical principles—**Excluded Middle**, **Double Negation Elimination**,
**Peirce's Law**, **Material Implication**, and **Classical De Morgan's Law**
(`¬(¬a ∧ ¬b) → a ∨ b`)—all imply one another:

```haskell
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
```

## Application: negation and order relations (`<`, `≤`)

Returning to `LT'` and `LE` from [Relations](/Relations/), negation lets us
prove that strict inequality is **irreflexive** (`ltIrrefl`) and **asymmetric**
(`ltAsym`), that no natural number is strictly less than zero (`notLtZero`),
and that `Not (LE m n)` constructively implies `LT' n m` (`notLeToGt`):

```haskell
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
```

## Exercises

#### Exercise `Stable` (stretch)

Say that a proposition `a` is *stable* if double negation elimination holds
for it: `type Stable a = Not (Not a) -> a`. Show constructively that:

1. Every negated proposition `Not a` is stable (hint: `tripleNegElim`).
2. The conjunction `(a, b)` of two stable propositions is stable.

#### Exercise `trichotomy-exclusive` (practice)

Using `ltIrrefl` and `ltAsym` above, verify that the three branches of
`Trichotomy m n` from [Relations](/Relations/) are mutually exclusive: no
pair `(m, n)` can satisfy more than one of `LT' m n`, `m :~: n`, and `LT' n m`.

## Changes from PLFA

- Adapted from [Negation](https://plfa.inf.ed.ac.uk/Negation/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part1/Negation.lagda.md)),
  licensed under CC BY 4.0.
- Every intuitionistic negation law, double-negation monad operation,
  classical equivalence (`emToDne`, `dneToPeirce`, `peirceToEm`, `emToImpOr`,
  `impOrToEm`, `emToDeMorganNot`, `deMorganNotToEm`), `irrefutableLEM`, and order-negation lemma
  (`ltIrrefl`, `ltAsym`, `notLtZero`, `ltToNotGe`, `leToNotGt`, `notLeToGt`)
  ports directly and passes `-dcore-lint -dstg-lint`.
- All promoted constructors (`Zero`) are written without leading `'` ticks.
- As throughout PLFH, soundness of `Not a = a -> Void` relies on our
  structural-recursion / no-bottom proof discipline rather than a compiler
  totality checker.
