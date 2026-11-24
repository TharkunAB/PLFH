---
title: "Induction: Proof by Induction"
prev: /Naturals/
next: /Relations/
src: content/part1/Induction.md
module: PLFH.Part1.Induction
plfaChapter: https://plfa.inf.ed.ac.uk/Induction/
---

```haskell
{-# LANGUAGE AllowAmbiguousTypes, DataKinds, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, Modifiers, PolyKinds, RequiredTypeArguments, TypeOperators #-}
module PLFH.Part1.Induction
  ( cong
  , assocExample
  , plusAssoc
  , plusAssoc0
  , plusAssoc1
  , plusAssoc2
  , plusAssocRewrite
  , plusIdentityR
  , plusSuc
  , plusComm
  , plusCommRewrite
  , plusRearrange
  , plusSwap
  , timesDistribPlus
  , timesAssoc
  , timesZeroR
  , timesSuccR
  , timesComm
  , timesSwap
  , timesInterchange
  , threeMonusTwo
  , twoMonusThree
  , zeroMonus
  , monusPlusAssoc
  , threePowFour
  , powPlus
  , powMul
  , powTimes
  , fromInc
  , fromTo
  , twoTimesThree
  ) where

import Data.Type.Equality ((:~:) (Refl), sym, trans)
import GHC.Types (Matchability)
import HaskLib (rewrite)
import HaskLib.Nat (Nat (..), congFirst, plus, plusSucc, plusZero, type (+))
import PLFH.Part1.Naturals (Bin (..), fromBin, inc, monus, pow, times, toBin)
```

> Induction makes you feel guilty for getting something out of nothing
> ... but it is one of the greatest ideas of civilization.
> — Herbert Wilf

Now that we have defined the naturals and operations upon them, our next
step is to learn how to prove properties that they satisfy. As hinted by
their name, properties of *inductive datatypes* are proved by *induction*,
and in Dependent Haskell induction corresponds directly to *structural
recursion*.

## Imports and Congruence (`cong`)

We require propositional equality `(:~:)` with `Refl`, `sym`, and `trans`
from `Data.Type.Equality`, `rewrite` from `HaskLib`, `Nat` and `plus` from
`HaskLib.Nat`, and our operations from [Naturals](/Naturals/).

We also define **congruence**: a relation is said to be a *congruence* for
a given function `f` if it is preserved by applying `f`—given evidence that
`x :~: y`, `cong f` returns evidence that `f x :~: f y`. Thanks to
matchability polymorphism (`{m :: Matchability}`, `-XModifiers`, explored
further in [Equality](/Equality/)) together with `RequiredTypeArguments`
(`forall (f :: a %m -> b) -> ...`), a **single** definition of `cong`
works just like Agda's—with **no `@` sign needed**—for both promoted data
constructors (`cong Succ`, matchable arrow `Nat -> Nat`) and partially applied
promoted functions (`cong (plus m)`, `cong (times a)`, unmatchable arrow
`Nat %U -> Nat`):

```haskell
-- | Unified matchability-polymorphic congruence (`cong`): works just like Agda
-- for both constructors (`cong Succ`) and promoted functions (`cong (plus m)`).
cong :: forall {a} {b} {m :: Matchability}.
        forall (f :: a %m -> b) -> forall (x :: a) (y :: a).
        x :~: y -> f x :~: f y
cong _ Refl = Refl

-- | Evidence that 2 * 3 = 6 using ordinary `times` imported from Naturals.
twoTimesThree :: times 2 3 :~: 6
twoTimesThree = Refl
```

## Properties of operators

Operators pop up all the time, and mathematicians have agreed on names for
some of the most common properties:

- *Identity.* Operator `+` has left identity `0` if `0 + n ≡ n`, and right
  identity `0` if `n + 0 ≡ n`, for all `n`. A value that is both a left and
  right identity is just called an identity (or sometimes a *unit*).
- *Associativity.* Operator `+` is associative if the location of
  parentheses does not matter: `(m + n) + p ≡ m + (n + p)`, for all `m`,
  `n`, and `p`.
- *Commutativity.* Operator `+` is commutative if order of arguments does
  not matter: `m + n ≡ n + m`, for all `m` and `n`.
- *Distributivity.* Operator `*` distributes over operator `+` from the
  left if `m * (p + q) ≡ (m * p) + (m * q)`, for all `m`, `p`, and `q`, and
  from the right if `(m + n) * p ≡ (m * p) + (n * p)`, for all `m`, `n`,
  and `p`.

Addition has identity `0` and multiplication has identity `1`; addition and
multiplication are both associative and commutative; and multiplication
distributes over addition.

If you ever bump into an operator at a party, you now know how to make
small talk, by asking whether it has a unit and is associative or
commutative. If you bump into two operators, you might ask them if one
distributes over the other.

Less frivolously, if you ever bump into an operator while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it has an identity, is associative or commutative, or
distributes over another operator. A careful author will often call out
these properties—or their lack—for instance by pointing out that a newly
introduced operator is associative but not commutative.

#### Exercise `operators` (practice) {#operators}

Give another example of a pair of operators that have an identity and are
associative, commutative, and distribute over one another. Give an example
of an operator that has an identity and is associative but is not
commutative. (You do not have to prove these properties.)

## Associativity

One property of addition is that it is *associative*, that is, that the
location of the parentheses does not matter:

```text
(m + n) + p ≡ m + (n + p)
```

Here `m`, `n`, and `p` are variables that range over all natural numbers.
We can test the proposition on specific numbers—say `3`, `4`, and `5`,
where `(3 + 4) + 5 = 7 + 5 = 12 = 3 + 9 = 3 + (4 + 5)`:

```haskell
-- | Concrete instance of associativity: (3 + 4) + 5 = 3 + (4 + 5).
assocExample :: ((3 + 4) + 5 :: Nat) :~: (3 + (4 + 5) :: Nat)
assocExample = Refl
```

The test reveals that associativity is perhaps not as obvious as first it
appears: why should `7 + 5` be the same as `3 + 9`? We might want to gather
more evidence by testing other numbers, but—since there are an infinite
number of naturals—testing can never be complete. Is there any way we can
be sure that associativity holds for *all* the natural numbers?

The answer is yes! We can prove a property holds for all naturals using
*proof by induction*.

## Proof by induction

Recall the definition of natural numbers consists of a *base case* which
tells us that `Zero` is a natural, and an *inductive case* which tells us
that if `m` is a natural then `Succ m` is also a natural.

Proof by induction follows the structure of this definition. To prove a
property of natural numbers by induction, we need to prove two cases. First
is the *base case*, where we show the property holds for `Zero`. Second is
the *inductive case*, where we assume the property holds for an arbitrary
natural `m` (we call this the *inductive hypothesis*), and then show that
the property must also hold for `Succ m`.

If we write `P m` for a property of `m`, then what we need to demonstrate
are the following two inference rules:

<div class="inference-rule">
  <div class="premises">&nbsp;</div>
  <div class="conclusion">P Zero</div>
</div>
<div class="inference-rule">
  <div class="premises">P m</div>
  <div class="conclusion">P (Succ m)</div>
</div>

Why does this work? Again, it can be explained by a creation story:

```text
-- On the first day, one property is known.
P Zero

-- On the second day, two properties are known.
P Zero
P (Succ Zero)

-- On the third day, three properties are known.
P Zero
P (Succ Zero)
P (Succ (Succ Zero))
```

On the *n*'th day there are *n* distinct properties that hold. In
particular, the property `P n` first appears on day *n + 1*.

## Our first proof: associativity (`+-assoc`)

To prove associativity, we take `P m` to be the property
`plus (plus m n) p :~: plus m (plus n p)`. Here `n` and `p` are arbitrary
natural numbers, so if we show the equation holds for all `m` it holds for
all `n` and `p`.

In Dependent Haskell, a universal quantifier over runtime natural numbers
is written `foreach (m :: Nat) -> ...`. Each retained argument is an
ordinary runtime `Nat` value that can also appear in the result type:

```haskell
-- | Associativity of addition: (m + n) + p = m + (n + p).
plusAssoc :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
          -> plus (plus m n) p :~: plus m (plus n p)
plusAssoc Zero     _ _ = Refl
plusAssoc (Succ m) n p = cong Succ (plusAssoc m n p)
```

Let's unpack what GHC checks in each equation:

- **Base case (`Zero`):** We must show `(Zero + n) + p ≡ Zero + (n + p)`.
  Simplifying both sides with the base case of addition yields
  `n + p ≡ n + p`, so `Refl` checks immediately.
- **Inductive case (`Succ m`):** We must show
  `(Succ m + n) + p ≡ Succ m + (n + p)`. Simplifying both sides with the
  inductive case of addition yields `Succ ((m + n) + p) ≡ Succ (m + (n + p))`.
  The recursive invocation `plusAssoc m n p` has as its type the induction
  hypothesis `(m + n) + p ≡ m + (n + p)`, and `cong Succ` prefaces `Succ`
  to each side to yield the needed equation!

Here the inductive hypothesis is not assumed, but instead proved by a
recursive invocation of the function we are defining. This is well founded
because associativity of `Succ m` is proved using associativity of `m`. The
correspondence between proof by induction and definition by recursion is
one of the most appealing aspects of dependent types.

<div class="note-box">
<strong>Totality note:</strong>
Agda's termination checker guarantees that <code>+-assoc</code> terminates
for every <code>m</code> because the recursive call decreases <code>m</code>.
GHC does not enforce termination, so we verify by inspection (and our test
harness audit) that every proof decreases structurally on an inductive
argument and contains no <code>undefined</code>, holes, or circular loops.
</div>

## Induction as recursion

As a concrete example of how induction corresponds to recursion, here is
the computation that occurs when instantiating `m` to `0`, `1`, and `2` in
the proof of associativity:

```haskell
-- | Unrolling `plusAssoc` at m = 0, 1, and 2.
plusAssoc0 :: foreach (n :: Nat) -> foreach (p :: Nat)
           -> plus (plus 0 n) p :~: plus 0 (plus n p)
plusAssoc0 _ _ = Refl

plusAssoc1 :: foreach (n :: Nat) -> foreach (p :: Nat)
           -> plus (plus 1 n) p :~: plus 1 (plus n p)
plusAssoc1 n p = cong Succ (plusAssoc0 n p)

plusAssoc2 :: foreach (n :: Nat) -> foreach (p :: Nat)
           -> plus (plus 2 n) p :~: plus 2 (plus n p)
plusAssoc2 n p = cong Succ (plusAssoc1 n p)
```

## Terminology and notation

The quantifier `foreach (m :: Nat) -> ...` plays the role of Agda's
universal quantifier `∀ (m : ℕ) → ...` (discussed further in
[Quantifiers](/Quantifiers/)). Evidence for a universal quantifier is a
*dependent function*: a variable is associated with each argument type, and
the result type may mention (or depend upon) that variable. Ordinary
functions `Nat -> Nat -> Nat` are the special case where the result type
does not depend on the argument values.

## Our second proof: commutativity (`+-comm`)

Another important property of addition is that it is *commutative*, that
is, that the order of the operands does not matter:

```text
m + n ≡ n + m
```

The proof requires that we first demonstrate two lemmas:

1. **First lemma (`+-identityʳ`):** While the base case of `plus` gives
   left-identity `0 + n ≡ n`, right-identity `m + 0 ≡ m` requires induction
   on `m`.
2. **Second lemma (`+-suc`):** While the inductive case of `plus` pushes
   `Succ` out of the first argument (`Succ m + n ≡ Succ (m + n)`), pushing
   `Succ` out of the second argument (`m + Succ n ≡ Succ (m + n)`) requires
   induction on `m`.

Both lemmas are already proved by induction in `HaskLib.Nat` as `plusZero`
and `plusSucc`, so we reuse them directly:

```haskell
-- | First lemma: right identity of addition (`+-identityʳ`).
plusIdentityR :: foreach (m :: Nat) -> plus m Zero :~: m
plusIdentityR = plusZero

-- | Second lemma: move a successor from the second addend outside (`+-suc`).
plusSuc :: foreach (m :: Nat) -> foreach (n :: Nat)
        -> plus m (Succ n) :~: Succ (plus m n)
plusSuc = plusSucc
```

Finally, here is our proposition's statement and proof by induction on the
**second** argument `n` (not on `m` this time!):

```haskell
-- | Commutativity of addition: m + n = n + m (`+-comm`).
plusComm :: foreach (m :: Nat) -> foreach (n :: Nat) -> plus m n :~: plus n m
plusComm m Zero     = plusZero m
plusComm m (Succ k) = plusSucc m k `trans` cong Succ (plusComm m k)
```

- **Base case (`Zero`):** We must show `m + Zero ≡ Zero + m`, which
  simplifies to `m + Zero ≡ m` and is discharged by our first lemma
  `plusZero m`.
- **Inductive case (`Succ k`):** We must show `m + Succ k ≡ Succ k + m`,
  which simplifies to `m + Succ k ≡ Succ (k + m)`. First `plusSucc m k`
  gives `m + Succ k ≡ Succ (m + k)`, and then `cong Succ (plusComm m k)`
  gives `Succ (m + k) ≡ Succ (k + m)`; chaining them with `trans` completes
  the proof!

## Our first corollary: rearranging {#sections}

We can apply associativity to rearrange parentheses however we like,
without needing induction at all—simply applying `plusAssoc`, `sym`, and
`cong (plus m)`:

```haskell
-- | Rearranging parentheses in a four-way sum: (m + n) + (p + q) = (m + (n + p)) + q.
plusRearrange :: foreach (m :: Nat) -> foreach (n :: Nat)
              -> foreach (p :: Nat) -> foreach (q :: Nat)
              -> plus (plus m n) (plus p q) :~: plus (plus m (plus n p)) q
plusRearrange m n p q =
  plusAssoc m n (plus p q)
    `trans` cong (plus m) (sym (plusAssoc n p q))
    `trans` sym (plusAssoc m (plus n p) q)
```

Notice two tools used here:

- `sym` interchanges the sides of an equation: if `e` provides evidence for
  `x :~: y`, then `sym e` provides evidence for `y :~: x`.
- `cong (plus m)` lifts `sym (plusAssoc n p q)` (`n + (p + q) ≡ (n + p) + q`)
  under the partially applied function `plus m` (mirroring Agda's section
  `cong (m +_)`).

## Creation, one last time

Returning to associativity, we can view the inductive proof as a creation
story for equations: on the first day we know `(0 + n) + p ≡ 0 + (n + p)`
for all `n` and `p`; on the second day we add all equations with `m = 1`;
and on the *m*'th day we know all equations where the first number is less
than *m*.

#### Exercise `finite-+-assoc` (stretch) {#finite-plus-assoc}

Write out what is known about associativity of addition on each of the
first four days using a finite story of creation, as in
[Naturals](/Naturals/#finite-creation).

## Associativity and commutativity with `HaskLib.rewrite`

There is more than one way to skin a cat. PLFA also proves `+-assoc′` and
`+-comm′` using Agda's `rewrite` keyword rather than explicit congruence
and transitivity chains. In Dependent Haskell, `rewrite` (exported from
`HaskLib`) brings a propositional equality `a :~: b` into scope as a local
equality constraint for its body—avoiding explicit `cong` and `trans`:

```haskell
-- | Associativity proved via `HaskLib.rewrite` (`+-assoc′`).
plusAssocRewrite :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
                 -> plus (plus m n) p :~: plus m (plus n p)
plusAssocRewrite Zero     _ _ = Refl
plusAssocRewrite (Succ m) n p = rewrite (plusAssocRewrite m n p) Refl

-- | Commutativity proved via nested `HaskLib.rewrite` (`+-comm′`).
plusCommRewrite :: foreach (m :: Nat) -> foreach (n :: Nat) -> plus m n :~: plus n m
plusCommRewrite m Zero     = rewrite (plusZero m) Refl
plusCommRewrite m (Succ k) = rewrite (plusSucc m k) (rewrite (plusCommRewrite m k) Refl)
```

### Negative control: zero is not equal to its successor

As a sanity check, we verify that GHC rejects a false equality between `0`
and `1` directly with `GHC-83865`:

```{.haskell .fail name="NegZeroSucc" expect="GHC-83865"}
{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
module NegZeroSucc (zeroEqualsOne) where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..))

zeroEqualsOne :: (0 :: Nat) :~: 1
zeroEqualsOne = Refl
```

## Exercises checked directly

### `+-swap` (recommended) {#plus-swap}

Show `m + (n + p) ≡ n + (m + p)` without induction, using only
associativity and commutativity:

```haskell
-- | Swap the first two addends: m + (n + p) = n + (m + p).
plusSwap :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
         -> plus m (plus n p) :~: plus n (plus m p)
plusSwap m n p =
  sym (plusAssoc m n p)
    `trans` rewrite (plusComm m n) Refl
    `trans` plusAssoc n m p
```

### Multiplication laws (`*-distrib-+`, `*-assoc`, `*-comm`)

All of PLFA's multiplication exercises prove directly using our ordinary
Haskell `times` function:

```haskell
-- | Right distributivity of multiplication over addition (`*-distrib-+`):
-- (m + n) * p = m * p + n * p.
timesDistribPlus :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
                 -> times (plus m n) p :~: plus (times m p) (times n p)
timesDistribPlus Zero     _ _ = Refl
timesDistribPlus (Succ m) n p =
  rewrite (timesDistribPlus m n p)
    (sym (plusAssoc p (times m p) (times n p)))

-- | Associativity of multiplication (`*-assoc`): (m * n) * p = m * (n * p).
timesAssoc :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
           -> times (times m n) p :~: times m (times n p)
timesAssoc Zero     _ _ = Refl
timesAssoc (Succ m) n p =
  rewrite (timesAssoc m n p)
    (timesDistribPlus n (times m n) p)

-- | Right zero for multiplication: m * 0 = 0.
timesZeroR :: foreach (m :: Nat) -> times m Zero :~: Zero
timesZeroR Zero     = Refl
timesZeroR (Succ m) = timesZeroR m

-- | Right successor for multiplication: m * (Succ n) = m + m * n.
timesSuccR :: foreach (m :: Nat) -> foreach (n :: Nat)
           -> times m (Succ n) :~: plus m (times m n)
timesSuccR Zero     _ = Refl
timesSuccR (Succ m) n =
  rewrite (timesSuccR m n)
    (cong Succ (plusSwap n m (times m n)))

-- | Commutativity of multiplication (`*-comm`): m * n = n * m.
timesComm :: foreach (m :: Nat) -> foreach (n :: Nat)
          -> times m n :~: times n m
timesComm Zero     n = sym (timesZeroR n)
timesComm (Succ m) n =
  rewrite (timesComm m n)
    (sym (timesSuccR n m))
```

### Truncated subtraction (`0∸n≡0`, `∸-+-assoc`)

The ordinary `monus` definition in [Naturals](/Naturals/) inspects its second
argument first. At zero, subtraction returns the first argument. At a
successor, it inspects the first argument too. Both possibilities give zero
when subtracting from zero (no induction needed—just case analysis!):

```haskell
-- | Concrete examples of truncated subtraction (cross-module from Naturals):
-- 3 ∸ 2 = 1 and 2 ∸ 3 = 0.
threeMonusTwo :: monus 3 2 :~: 1
threeMonusTwo = Refl

twoMonusThree :: monus 2 3 :~: 0
twoMonusThree = Refl

-- | Subtracting any natural from zero gives zero (`0∸n≡0`).
zeroMonus :: foreach (n :: Nat) -> monus Zero n :~: Zero
zeroMonus Zero     = Refl
zeroMonus (Succ _) = Refl
```

Subtracting `n` and then `p` gives the same result as subtracting their sum
`n + p`. The proof splits on `n` first; when `n` and `m` are both
successors, the checked subtraction equations cancel a successor on each
side and the induction hypothesis applies to their predecessors:

```haskell
-- | Two successive subtractions subtract the sum of their operands (`∸-+-assoc`).
monusPlusAssoc :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
               -> monus (monus m n) p :~: monus m (plus n p)
monusPlusAssoc Zero     Zero     _ = Refl
monusPlusAssoc Zero     (Succ _) p = zeroMonus p
monusPlusAssoc (Succ _) Zero     _ = Refl
monusPlusAssoc (Succ m) (Succ n) p = monusPlusAssoc m n p
```

### Exponentiation exercises (`+*^`: `powPlus`, `powMul`, `powTimes`)

All three of PLFA's exponentiation laws (`^-distribˡ-+-*`, `^-distribʳ-*`,
and `^-*-assoc`) prove directly over ordinary `pow` from
[Naturals](/Naturals/):

```haskell
-- | Swap the first two factors: m * (n * p) = n * (m * p).
timesSwap :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
          -> times m (times n p) :~: times n (times m p)
timesSwap m n p =
  sym (timesAssoc m n p)
    `trans` congFirst @times @p (timesComm m n)
    `trans` timesAssoc n m p

-- | Interchange law for multiplication: (a * b) * (c * d) = (a * c) * (b * d).
timesInterchange :: foreach (a :: Nat) -> foreach (b :: Nat)
                 -> foreach (c :: Nat) -> foreach (d :: Nat)
                 -> times (times a b) (times c d) :~: times (times a c) (times b d)
timesInterchange a b c d =
  timesAssoc a b (times c d)
    `trans` cong (times a) (timesSwap b c d)
    `trans` sym (timesAssoc a c (times b d))

-- | Concrete exponentiation example (cross-module from Naturals): 3 ^ 4 = 81.
threePowFour :: pow 3 4 :~: 81
threePowFour = Refl

-- | Distributivity of exponentiation over addition (`^-distribˡ-+-*`):
-- m ^ (n + p) = (m ^ n) * (m ^ p).
powPlus :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
        -> pow m (plus n p) :~: times (pow m n) (pow m p)
powPlus m Zero     p = sym (plusZero (pow m p))
powPlus m (Succ k) p =
  rewrite (powPlus m k p)
    (sym (timesAssoc m (pow m k) (pow m p)))

-- | Distributivity of exponentiation over multiplication (`^-distribʳ-*`):
-- (m * n) ^ p = (m ^ p) * (n ^ p).
powMul :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
       -> pow (times m n) p :~: times (pow m p) (pow n p)
powMul _ _ Zero     = Refl
powMul m n (Succ k) =
  rewrite (powMul m n k)
    (timesInterchange m n (pow m k) (pow n k))

-- | Associativity of iterated exponentiation (`^-*-assoc`):
-- (m ^ n) ^ p = m ^ (n * p).
powTimes :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
         -> pow (pow m n) p :~: pow m (times n p)
powTimes _ n Zero     = rewrite (timesZeroR n) Refl
powTimes m n (Succ k) =
  rewrite (powTimes m n k)
    (rewrite (timesSuccR n k) (sym (powPlus m n (times n k))))
```

### Binary natural laws (`Bin-laws`, stretch) {#Bin-laws}

Finally, PLFA's stretch exercise on binary bitstrings checks completely
with our ordinary Haskell `inc`, `toBin`, and `fromBin` functions! (As in
PLFA, `toBin (fromBin b) :~: b` is false due to leading zeros—for instance,
`toBin (fromBin Nil) = X0 Nil /= Nil`—while the two valid laws prove
cleanly by induction, and in [Relations](/Relations/) we restrict to
canonical bitstrings `Can` to prove `toFromCan`):

```haskell
-- | Incrementing a bitstring adds one to its unary value.
fromInc :: foreach (b :: Bin) -> fromBin (inc b) :~: Succ (fromBin b)
fromInc Nil    = Refl
fromInc (X0 _) = Refl
fromInc (X1 b) =
  rewrite (fromInc b)
    (cong Succ (plusSucc (fromBin b) (fromBin b)))

-- | Round-tripping Nat -> Bin -> Nat is the identity.
fromTo :: foreach (n :: Nat) -> fromBin (toBin n) :~: n
fromTo Zero     = Refl
fromTo (Succ n) = fromInc (toBin n) `trans` cong Succ (fromTo n)
```

## Changes from PLFA

- Adapted from [Induction](https://plfa.inf.ed.ac.uk/Induction/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part1/Induction.lagda.md)).
- Reused `plusZero` (`+-identityʳ`) and `plusSucc` (`+-suc`) from `HaskLib.Nat`.
- Uses a single Agda-style matchability-polymorphic `cong` (`{m :: Matchability}`
  + `RequiredTypeArguments`) for both constructors (`cong Succ`) and promoted
  functions (`cong (plus m)`, `cong (times a)`), with no `@` needed (partial
  application of right-first `pow m` under visible `cong` is tracked in
  `R23_CongRightFirstPartialApp.hs`).
- Checked direct ports of every theorem and exercise in PLFA Induction:
  `assocExample`, `plusAssoc`, `plusAssoc0`/`1`/`2`, `plusAssocRewrite`,
  `plusIdentityR`, `plusSuc`, `plusComm`, `plusCommRewrite`, `plusRearrange`,
  `plusSwap`, `timesDistribPlus`, `timesAssoc`, `timesZeroR`, `timesSuccR`,
  `timesComm`, `timesSwap`, `timesInterchange`, `zeroMonus`, `monusPlusAssoc`,
  `powPlus`, `powMul`, `powTimes`, `fromInc`, and `fromTo`.
- Uses `HaskLib.rewrite` in place of Agda's `rewrite` syntax, and adds an
  explicit negative control (`NegZeroSucc`) verifying GHC rejects `0 :~: 1`
  (`GHC-83865`).
- Omitted Agda's Emacs interactive proof-building walkthrough and Unicode
  table.
