---
title: "Decidable: Booleans and decision procedures"
prev: /Quantifiers/
next: /Lists/
src: content/part1/Decidable.md
module: PLFH.Part1.Decidable
plfaChapter: https://plfa.inf.ed.ac.uk/Decidable/
---

We have a choice as to how to represent relations and predicates:

- As an inductive GADT of **evidence** that the relation holds (like `LE m n`
  in [Relations](/Relations/)).
- As a function that **computes** a `Bool` (`True` or `False`).

In this chapter we explore the relationship between evidence and computation,
and introduce **decidable propositions** (`Dec p`), which combine the best of
both worlds: a decision procedure *computes* whether a proposition holds and
simultaneously *returns proof evidence* (`Yes p` or `No (Not p)`) certifying
its answer!

## Imports

We import `Type`, `(:~:)`, `Void`, `GHC.Sigma`, `Nat` and `plus`, unified
`cong` from [Induction](/Induction/), `Iff` from [Isomorphism](/Isomorphism/),
`Bin` from [Naturals](/Naturals/), and our inductive relations from
[Relations](/Relations/).

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE TypeApplications, TypeOperators #-}
module PLFH.Part1.Decidable
  ( Not
  , Dec (..)
  , decNot
  , decAnd
  , decOr
  , decImp
  , decIff
  , zeroNeqSucc
  , decEqSize
  , decLeSize
  , decLtSize
  , decEven
  , decOdd
  , decEqBin
  , decOne
  , decCan
  , Reflects (..)
  , reflectsToDec
  , Sigma (..)
  , SizeWitness
  , mkSizeWitness
  , plusExists
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void, absurd)
import GHC.Sigma (Sigma (Pair))
import HaskLib.Nat (Nat (..), plus)
import PLFH.Part1.Induction (cong)
import PLFH.Part1.Isomorphism (Iff (..))
import PLFH.Part1.Naturals (Bin (..))
import PLFH.Part1.Relations (Can (..), Even (..), LE (..), LT' (..), Odd (..), One (..), invSleS)
```

## Evidence vs. Computation

A Boolean-valued function such as `leBool :: Nat -> Nat -> Bool` returns a
single bit of information: `True` or `False`, with no guarantee that the bit
matches our inductive relation `LE m n`. To trust `leBool`, we would have to
write *two* additional soundness/completeness proofs relating `leBool m n` to
`LE m n` (via `Reflects`, shown below).

Conversely, inductive evidence like `LE m n` explains *why* the relation
holds—and lets us skip impossible cases in proofs—but forces the caller to
construct derivations like `SleS (SleS ZleN)` by hand.

### Negation (`Not`) and Peano's postulate

Before defining `Dec`, we define logical negation `Not a = a -> Void` (also
re-exported and explored in [Negation](/Negation/)) and prove Peano's
postulate that `Zero` is never equal to `Succ n`:

```haskell
-- | Logical negation: evidence that a proposition implies falsehood (Void).
type Not a = a -> Void

-- | Peano's postulate: Zero is never equal to any successor.
zeroNeqSucc :: Not (Zero :~: Succ n)
zeroNeqSucc eq = case eq of {}
```

## The best of both worlds: `Dec`

A proposition `p :: Type` is **decidable** (`Dec p`) if we can construct
either a proof of `p` (`Yes`) or a refutation `Not p` (`No`):

```haskell
-- | Evidence that a proposition `p` is decidable.
data Dec (p :: Type) where
  Yes :: p     -> Dec p
  No  :: Not p -> Dec p
```

Like `Bool`, `Dec p` has two constructors, so we can branch on it at runtime
in ordinary Haskell programs; unlike `Bool`, each branch delivers a
machine-checked proof (`p` or `Not p`) directly into scope! As PLFA puts it:
*a decision procedure proves itself correct, as attested by its type.*

### Logical connectives for decidables

Every Boolean connective (`not`, `&&`, `||`, implication, bi-implication)
lifts directly to decidable propositions:

```haskell
-- | Decidable propositions are closed under negation, conjunction, disjunction,
-- implication, and bi-implication.
decNot :: Dec p -> Dec (Not p)
decNot (Yes p)  = No (\np -> np p)
decNot (No  np) = Yes np

decAnd :: Dec p -> Dec q -> Dec (p, q)
decAnd (Yes p) (Yes q) = Yes (p, q)
decAnd (No np) _       = No (\(p, _) -> np p)
decAnd _       (No nq) = No (\(_, q) -> nq q)

decOr :: Dec p -> Dec q -> Dec (Either p q)
decOr (Yes p) _       = Yes (Left p)
decOr _       (Yes q) = Yes (Right q)
decOr (No np) (No nq) = No (either np nq)

decImp :: Dec p -> Dec q -> Dec (p -> q)
decImp (No np) _       = Yes (\p -> absurd (np p))
decImp _       (Yes q) = Yes (const q)
decImp (Yes p) (No nq) = No (\f -> nq (f p))

decIff :: Dec p -> Dec q -> Dec (Iff p q)
decIff dp dq = case decAnd (decImp dp dq) (decImp dq dp) of
  Yes (f, g) -> Yes (Iff f g)
  No nfg     -> No (\(Iff f g) -> nfg (f, g))
```

Notice that just as in PLFA's discussion of overlapping equations, when both
`dp` and `dq` are `No` in `decAnd` (or both `Yes` in `decOr`), Haskell's
top-to-bottom clause ordering deterministically selects the first matching
clause—both choices are equally valid proofs.

### Decidable equality (`_≟_`) and ordering (`_≤?_`, `_<?_`) on `Nat`

With `foreach`, `EmptyCase`, and unified `cong Succ`, decidable equality,
weak inequality, and strict inequality on natural numbers are all direct
structural recursions:

```haskell
-- | Decidable propositional equality on Nat (`_≡ℕ?_`).
decEqSize :: foreach (m :: Nat) -> foreach (n :: Nat) -> Dec (m :~: n)
decEqSize Zero     Zero     = Yes Refl
decEqSize Zero     (Succ _) = No (\case {})
decEqSize (Succ _) Zero     = No (\case {})
decEqSize (Succ m) (Succ n) = case decEqSize m n of
  Yes eq -> Yes (cong Succ eq)
  No neq -> No (\Refl -> neq Refl)

-- | Decidable less-than-or-equal relation on Nat (`_≤?_`).
decLeSize :: foreach (m :: Nat) -> foreach (n :: Nat) -> Dec (LE m n)
decLeSize Zero     _        = Yes ZleN
decLeSize (Succ _) Zero     = No (\case {})
decLeSize (Succ m) (Succ n) = case decLeSize m n of
  Yes p -> Yes (SleS p)
  No np -> No (\p -> np (invSleS p))

-- | Decidable strict less-than relation on Nat (`_<?_`).
decLtSize :: foreach (m :: Nat) -> foreach (n :: Nat) -> Dec (LT' m n)
decLtSize Zero     Zero     = No (\case {})
decLtSize Zero     (Succ _) = Yes ZltS
decLtSize (Succ _) Zero     = No (\case {})
decLtSize (Succ m) (Succ n) = case decLtSize m n of
  Yes p -> Yes (SltS p)
  No np -> No (\case SltS q -> np q)
```

### Decidable parity, Boolean reflection (`Reflects`), and `Bin-decidable`

Parity (`decEven`, `decOdd`) is decided by two-step structural recursion on
`Nat` (matching the inner `n` in a `case` expression on the RHS). And
whenever we *do* wish to bridge a Boolean `b :: Bool` back to a proposition
`p`, the standard **`Reflects p b`** GADT packages `OfTrue :: p -> Reflects p True`
and `OfFalse :: Not p -> Reflects p False` (using tick-free promoted `True`
and `False`), from which `reflectsToDec` immediately produces `Dec p`.

Finally, as a bonus extension beyond PLFA's `Decidable` chapter, we also prove
decidability for the binary-numeral predicates introduced in
[Naturals](/Naturals/) and [Relations](/Relations/): propositional equality
(`decEqBin`), positive canonical form (`decOne`), and canonical form
(`decCan`) are all decidable on `Bin`!

```haskell
-- | Decidable evenness predicate on Nat.
decEven :: foreach (n :: Nat) -> Dec (Even n)
decEven Zero     = Yes EvenZ
decEven (Succ n) = case n of
  Zero    -> No (\case EvenS o -> case o of {})
  Succ n' -> case decEven n' of
    Yes ev  -> Yes (EvenS (OddS ev))
    No  nev -> No (\case EvenS (OddS ev) -> nev ev)

-- | Decidable oddness predicate on Nat.
decOdd :: foreach (n :: Nat) -> Dec (Odd n)
decOdd Zero     = No (\case {})
decOdd (Succ n) = case n of
  Zero    -> Yes (OddS EvenZ)
  Succ n' -> case decOdd n' of
    Yes od  -> Yes (OddS (EvenS od))
    No  nod -> No (\case OddS (EvenS od) -> nod od)

-- | Boolean reflection: ties a proposition `p` to a promoted `Bool` `b`.
data Reflects (p :: Type) (b :: Bool) where
  OfTrue  :: p -> Reflects p True
  OfFalse :: Not p -> Reflects p False

-- | Reflecting a Boolean yields a decision procedure.
reflectsToDec :: foreach (b :: Bool) -> Reflects p b -> Dec p
reflectsToDec True  (OfTrue p)   = Yes p
reflectsToDec False (OfFalse np) = No np

-- | Decidable equality on binary numbers (`Bin`).
decEqBin :: foreach (a :: Bin) -> foreach (b :: Bin) -> Dec (a :~: b)
decEqBin Nil    Nil    = Yes Refl
decEqBin Nil    (X0 _) = No (\case {})
decEqBin Nil    (X1 _) = No (\case {})
decEqBin (X0 _) Nil    = No (\case {})
decEqBin (X0 _) (X1 _) = No (\case {})
decEqBin (X0 a) (X0 b) = case decEqBin a b of
  Yes Refl -> Yes Refl
  No  neq  -> No (\Refl -> neq Refl)
decEqBin (X1 _) Nil    = No (\case {})
decEqBin (X1 _) (X0 _) = No (\case {})
decEqBin (X1 a) (X1 b) = case decEqBin a b of
  Yes Refl -> Yes Refl
  No  neq  -> No (\Refl -> neq Refl)

-- | Decidable `One` predicate (`One?`).
decOne :: foreach (b :: Bin) -> Dec (One b)
decOne Nil    = No (\case {})
decOne (X0 b) = case decOne b of
  Yes o  -> Yes (OneX0 o)
  No  no -> No (\case OneX0 o -> no o)
decOne (X1 b) = case b of
  Nil   -> Yes OneX1
  X0 b' -> case decOne (X0 b') of
    Yes o  -> Yes (OneX1' o)
    No  no -> No (\case OneX1' o -> no o)
  X1 b' -> case decOne (X1 b') of
    Yes o  -> Yes (OneX1' o)
    No  no -> No (\case OneX1' o -> no o)

-- | Decidable canonical-form predicate (`Can?`).
decCan :: foreach (b :: Bin) -> Dec (Can b)
decCan Nil    = No (\case CanOne o -> case o of {})
decCan (X0 b) = case b of
  Nil   -> Yes CanZ
  X0 b' -> case decOne (X0 b') of
    Yes o  -> Yes (CanOne (OneX0 o))
    No  no -> No (\case CanOne (OneX0 o) -> no o)
  X1 b' -> case decOne (X1 b') of
    Yes o  -> Yes (CanOne (OneX0 o))
    No  no -> No (\case CanOne (OneX0 o) -> no o)
decCan (X1 b) = case decOne (X1 b) of
  Yes o  -> Yes (CanOne o)
  No  no -> No (\case CanOne o -> no o)
```

## Witness-carrying dependent pairs (`Sigma`)

In Agda, the `From-yes` / `T` combinator lets proof-carrying code turn a
decidable test on closed values (such as `2 ≤? 4`) into an implicit proof
discharged automatically during type checking.

In Dependent Haskell, type-class / constraint solving plays the analogous role
of automatically discharging statically known invariants, while at runtime
we carry existential witnesses directly using retained dependent pairs
`GHC.Sigma.Sigma` (`some (x :: a) | p x`, constructed with `Pair x px`):

```haskell
-- | A dependent pair carrying a runtime size `k` and evidence that Zero <= k.
type SizeWitness = some (k :: Nat) | LE Zero k

-- | Package any runtime size with its proof of Zero <= k.
mkSizeWitness :: Nat -> SizeWitness
mkSizeWitness k = Pair k ZleN

-- | Inline retained dependent sum returned directly from a `foreach` function.
plusExists :: foreach (m :: Nat) -> foreach (n :: Nat)
           -> some (k :: Nat) | k :~: plus m n
plusExists m n = Pair (plus m n) Refl
```

## Exercises

#### Exercise `erasure` (practice)

Define erasure `eraseDec :: Dec p -> Bool` mapping `Yes _` to `True` and
`No _` to `False`, and verify at runtime that `eraseDec (decAnd dp dq)` agrees
with `eraseDec dp && eraseDec dq`, and similarly for `decOr`, `decNot`, and
`decIff`.

#### Exercise `guarded-minus` (practice)

Using `LE n m`, define a guarded subtraction function
`minus :: foreach (m :: Nat) -> foreach (n :: Nat) -> LE n m -> Nat`
that subtracts `n` from `m` only when given evidence that `n ≤ m`, with an
absurd `case p of {}` in the impossible `Zero` / `Succ` branch.

## Changes from PLFA

- Adapted from [Decidable](https://plfa.inf.ed.ac.uk/Decidable/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part1/Decidable.lagda.md)),
  licensed under CC BY 4.0.
- `Not`, `zeroNeqSucc`, `Dec`, `decNot`/`And`/`Or`/`Imp`/`Iff`, `decEqSize`,
  `decLeSize`, `decLtSize`, `decEven`, `decOdd`, `decEqBin`/`decOne`/`decCan`,
  `Reflects`, `reflectsToDec`, and `Sigma`/`some` (`SizeWitness`,
  `mkSizeWitness`, and inline `plusExists`) all port directly and pass
  `-dcore-lint -dstg-lint`.
- Uses unified `cong Succ` from [Induction](/Induction/), `Data.Void.Void`,
  `EmptyCase` (`\case {}`), and tick-free promoted constructors (`Zero`,
  `Succ`, `True`, `False`).
