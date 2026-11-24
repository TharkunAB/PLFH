---
title: "Relations: Inductive definition of relations"
prev: /Induction/
next: /Equality/
src: content/part1/Relations.md
module: PLFH.Part1.Relations
plfaChapter: https://plfa.inf.ed.ac.uk/Relations/
---

After defining operations on the naturals and proving properties of them
by induction, we now turn to **inductive relations**: **indexed datatypes**
(GADTs) whose constructors represent inference rules.

In Agda, indexed datatypes are written `data _≤_ : ℕ → ℕ → Set where ...`.
In Dependent Haskell, the exact same concept is expressed with a `data` GADT
indexed by promoted values of kind `Nat`—not a GHC `type family` (no
`-XTypeFamilies` is needed!).

## Imports

We import propositional equality, `Void` (for negation in `notBothEvenOdd`),
`rewrite` from `HaskLib`, `Nat` and addition lemmas from `HaskLib.Nat`,
matchability-polymorphic `cong` from [Induction](/Induction/), and binary
numerals from [Naturals](/Naturals/).

```haskell
{-# LANGUAGE DependentTypes #-}
module PLFH.Part1.Relations
  ( LE (..)
  , twoLeFour
  , invSleS
  , invZleN
  , leRefl
  , leTrans
  , leAntisym
  , Total (..)
  , leTotal
  , plusMonoR
  , plusMonoL
  , plusMono
  , timesMonoR
  , timesMonoL
  , timesMono
  , LT' (..)
  , ltTrans
  , Trichotomy (..)
  , ltTrichotomy
  , ltToLe
  , leToLt
  , DiffWitness (..)
  , leToDiff
  , diffToLe
  , plusMonoLtR
  , plusMonoLtL
  , plusMonoLt
  , Even (..)
  , Odd (..)
  , evenPlusEven
  , oddPlusEven
  , evenPlusOdd
  , oddPlusOdd
  , evenOrOdd
  , notBothEvenOdd
  , One (..)
  , Can (..)
  , incOne
  , incCan
  , toBinCan
  , PosNat (..)
  , onePos
  , toBinDoubleSucc
  , toFromDoubleOne
  , toFromOne
  , toFromCan
  ) where

import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void)
import HaskLib (rewrite)
import HaskLib.Nat (Nat (..), plus, plusSucc, plusZero)
import PLFH.Part1.Induction (cong, timesComm)
import PLFH.Part1.Naturals (Bin (..), fromBin, inc, times, toBin)
```

## Defining relations

The relation we define first is comparison between natural numbers: `m ≤ n`.
Just as `Nat` was defined inductively by a base case and an inductive step,
an inductive relation is defined by **inference rules**:

- **Base case:** for all naturals `n`, zero is less than or equal to `n`.
- **Inductive case:** for all naturals `m` and `n`, if `m` is less than or
  equal to `n`, then `Succ m` is less than or equal to `Succ n`.

We can write these two rules in natural-deduction notation:

<div class="inference-rule">
  <div class="premises">&nbsp;</div>
  <div class="conclusion">ZleN :: LE Zero n</div>
</div>
<div class="inference-rule">
  <div class="premises">LE m n</div>
  <div class="conclusion">SleS :: LE (Succ m) (Succ n)</div>
</div>

The base case has no premises above the horizontal line, so it is an axiom;
the inductive case takes a derivation of `LE m n` above the line and
produces a derivation of `LE (Succ m) (Succ n)` below it.

These rules correspond directly to a GADT in Dependent Haskell. Under
`-XDataKinds`, the constructors `Zero` and `Succ` can be written directly at
the type level without any leading tick:

```haskell
-- | Evidence that one natural number is less than or equal to another.
data LE (m :: Nat) (n :: Nat) where
  ZleN :: LE Zero n
  SleS :: LE m n -> LE (Succ m) (Succ n)
```

Notice the difference between `Nat` and `LE`: `Nat` is a single type, whereas
`LE` is an **indexed datatype (GADT)**—one type `LE m n` for each pair of
natural numbers `m` and `n` (in type-theory texts this is often called an
*"indexed family of types"*, which is a `data` GADT rather than a GHC
`type family`). Some of these types are inhabited (`LE 2 4`),
while others are empty (`LE 4 2` or `LE 1 0`). A value of type `LE m n` is
**evidence** (a proof tree) that `m ≤ n`.

For example, here is a proof that `2 ≤ 4`. Reading from the inside out, we
start with `ZleN :: LE 0 2`, apply `SleS` to obtain `LE 1 3`, and apply
`SleS` once more to obtain `LE 2 4`:

```haskell
-- | Concrete evidence that 2 <= 4 (using decimal literals for fixed numbers).
twoLeFour :: LE 2 4
twoLeFour = SleS (SleS ZleN)
```

### Implicit arguments

In `ZleN :: LE Zero n` and `SleS :: LE m n -> LE (Succ m) (Succ n)`, the
type variables `m` and `n` are implicitly universally quantified and inferred
automatically by GHC—matching Agda's curly-brace implicit arguments `{m n : ℕ}`.
Whenever GHC cannot infer an index on its own, or when we wish to spell out
the instantiation explicitly, we can pass it with `@` using `-XTypeApplications`.

## Inversion

In our definition of `LE`, the only way to prove `Succ m ≤ Succ n` is to
apply `SleS` to a proof of `m ≤ n`. Therefore, given evidence of
`LE (Succ m) (Succ n)`, we can **invert** the rule by pattern matching to
recover evidence of `LE m n`. Likewise, the only constructor capable of
producing `LE m Zero` is `ZleN`, which forces `m` to be `Zero`:

```haskell
-- | Inversion on successor inequality: if Succ m <= Succ n then m <= n.
invSleS :: LE (Succ m) (Succ n) -> LE m n
invSleS (SleS p) = p

-- | Inversion on zero upper bound: if m <= Zero then m = Zero.
invZleN :: LE m Zero -> m :~: Zero
invZleN ZleN = Refl
```

Because `ZleN` cannot have type `LE (Succ m) (Succ n)` and `SleS` cannot have
type `LE m Zero`, GHC knows that both one-clause definitions are completely
exhaustive without needing an absurd branch.

## Properties of ordering relations

What properties do we expect a relation like `≤` to satisfy? Mathematicians
classify binary relations using standard structural properties:

- **Reflexive:** for all `n`, `n ≤ n`.
- **Transitive:** for all `m`, `n`, and `p`, if `m ≤ n` and `n ≤ p`, then `m ≤ p`.
- **Anti-symmetric:** for all `m` and `n`, if `m ≤ n` and `n ≤ m`, then `m = n`.
- **Total:** for all `m` and `n`, either `m ≤ n` or `n ≤ m`.

These properties combine into familiar families of orderings:

- A **preorder** is reflexive and transitive.
- A **partial order** is a preorder that is also anti-symmetric.
- A **total order** is a partial order that is also total.

(As PLFA notes: *"If you ever bump into a relation at a party, you now
have a ready supply of small talk."*)

### Reflexivity

Reflexivity must build `n` layers of `SleS` wrapped around `ZleN`. Because
the proof structure depends on the runtime value of `n`, the argument `n` is
retained with `foreach (n :: Nat) ->`:

```haskell
-- | Reflexivity: n <= n for every finite n.
leRefl :: foreach (n :: Nat) -> LE n n
leRefl Zero     = ZleN
leRefl (Succ n) = SleS (leRefl n)
```

### Transitivity

Transitivity does *not* need retained `Nat` arguments at all: we induct
directly on the proof `LE m n` (and in the inductive step, simultaneously on
`LE n p`):

```haskell
-- | Transitivity: if m <= n and n <= p then m <= p.
leTrans :: LE m n -> LE n p -> LE m p
leTrans ZleN     _        = ZleN
leTrans (SleS p) (SleS q) = SleS (leTrans p q)
```

Why is there no clause for `leTrans (SleS p) ZleN`? The first argument
`SleS p` refines the middle index `n` to `Succ n'`, while `ZleN` requires
that same index `n` to be `Zero`. Since `Succ n'` and `Zero` cannot unify,
GHC statically rules out that case as impossible.

### Anti-symmetry

Anti-symmetry likewise inducts directly on the two inequality derivations,
using unified `cong Succ` from [Induction](/Induction/) in the inductive step:

```haskell
-- | Antisymmetry: if m <= n and n <= m then m = n.
leAntisym :: LE m n -> LE n m -> m :~: n
leAntisym ZleN     ZleN     = Refl
leAntisym (SleS p) (SleS q) = cong Succ (leAntisym p q)
```

#### Exercise `≤-antisym-cases` (`leAntisym` impossible cases, practice)

Why did `leAntisym` omit the clauses `leAntisym ZleN (SleS q)` and
`leAntisym (SleS p) ZleN`? Check that adding either clause would be rejected
as unreachable because `Zero` and `Succ k` are distinct constructors.

### Totality

To state that `≤` is **total**, we define a datatype `Total m n` holding
either evidence that `m ≤ n` (`Forward`) or evidence that `n ≤ m` (`Flipped`):

```haskell
-- | Evidence that either m <= n or n <= m.
data Total (m :: Nat) (n :: Nat) where
  Forward :: LE m n -> Total m n
  Flipped :: LE n m -> Total m n
```

In PLFA, the recursive call inside `≤-total (suc m) (suc n)` uses Agda's
`with` abstraction to inspect the result of `≤-total m n`. In Haskell,
ordinary `case ... of` expressions perform the exact same inspection while
splitting both `m` and `n` directly in the function equations:

```haskell
-- | Ordering on naturals is total.
leTotal :: foreach (m n :: Nat) -> Total m n
leTotal Zero     _        = Forward ZleN
leTotal (Succ _) Zero     = Flipped ZleN
leTotal (Succ m) (Succ n) = case leTotal m n of
  Forward p -> Forward (SleS p)
  Flipped p -> Flipped (SleS p)
```

Notice that when `m = n = 0`, both `Forward ZleN` and `Flipped ZleN` are
valid values of `Total 0 0`; our first clause picks `Forward ZleN`.

## Monotonicity

If one operation preserves an ordering relation, we say it is **monotonic**
with respect to that ordering. For addition on natural numbers:

- If `p ≤ q`, then `n + p ≤ n + q` (right monotonicity, `plusMonoR`).
- If `m ≤ n`, then `m + p ≤ n + p` (left monotonicity, `plusMonoL`).
- If `m ≤ n` and `p ≤ q`, then `m + p ≤ n + q` (combined monotonicity, `plusMono`).

Right monotonicity is a direct induction on `n` because `plus` recurses on
its first argument:

```haskell
-- | Right monotonicity: if p <= q then n + p <= n + q.
plusMonoR :: foreach (n :: Nat) -> LE p q -> LE (plus n p) (plus n q)
plusMonoR Zero     pq = pq
plusMonoR (Succ n) pq = SleS (plusMonoR n pq)
```

Left monotonicity inducts on `p`, using `plusZero`, `plusSucc`, and `rewrite`
from `HaskLib` to move the constructors out from the right operand (whereas
PLFA derives `+-monoˡ-≤` from `+-monoʳ-≤` via `+-comm`):

```haskell
-- | Left monotonicity: if m <= n then m + p <= n + p.
plusMonoL :: foreach (m n p :: Nat)
          -> LE m n -> LE (plus m p) (plus n p)
plusMonoL m n Zero     mn = rewrite (plusZero m) (rewrite (plusZero n) mn)
plusMonoL m n (Succ p) mn =
  rewrite (plusSucc m p)
    (rewrite (plusSucc n p) (SleS (plusMonoL m n p mn)))
```

Combining left and right monotonicity with `leTrans` yields full monotonicity
of addition in one line:

```haskell
-- | Combined monotonicity: if m <= n and p <= q then m + p <= n + q.
plusMono :: foreach (m n p q :: Nat)
         -> LE m n -> LE p q -> LE (plus m p) (plus n q)
plusMono m n p q mn pq = leTrans (plusMonoL m n p mn) (plusMonoR n pq)
```

### Multiplication monotonicity (`*-mono-≤`)

Multiplication is likewise monotonic with respect to `≤`: right monotonicity
(`timesMonoR`) follows by induction on `n` using `plusMono`, left monotonicity
(`timesMonoL`) follows in one line from `timesMonoR` and `timesComm` from
[Induction](/Induction/), and `leTrans` combines them:

```haskell
-- | Right monotonicity of multiplication: if p <= q then n * p <= n * q.
timesMonoR :: foreach (n p q :: Nat)
           -> LE p q -> LE (times n p) (times n q)
timesMonoR Zero     _ _ _  = ZleN
timesMonoR (Succ n) p q pq = plusMono p q (times n p) (times n q) pq (timesMonoR n p q pq)

-- | Left monotonicity of multiplication: if m <= n then m * p <= n * p.
timesMonoL :: foreach (m n p :: Nat)
           -> LE m n -> LE (times m p) (times n p)
timesMonoL m n p mn =
  rewrite (timesComm m p)
    (rewrite (timesComm n p) (timesMonoR p m n mn))

-- | Combined monotonicity of multiplication (`*-mono-≤`):
-- if m <= n and p <= q then m * p <= n * q.
timesMono :: foreach (m n p q :: Nat)
          -> LE m n -> LE p q -> LE (times m p) (times n q)
timesMono m n p q mn pq = leTrans (timesMonoL m n p mn) (timesMonoR n p q pq)
```

## Strict inequality

Just as we defined non-strict inequality `LE`, we can define **strict
inequality** `LT' m n` (`m < n`) inductively (named `LT'` so it does not clash
with `Prelude.LT`):

- **Base case:** `Zero < Succ n` for every `n`.
- **Inductive case:** if `m < n`, then `Succ m < Succ n`.

```haskell
-- | Strict inequality on natural numbers.
data LT' (m :: Nat) (n :: Nat) where
  ZltS :: LT' Zero (Succ n)
  SltS :: LT' m n -> LT' (Succ m) (Succ n)
```

Strict inequality is **transitive** (a *strict partial order*, since it is
also irreflexive—which we prove in [Negation](/Negation/)):

```haskell
-- | Strict inequality is transitive.
ltTrans :: LT' m n -> LT' n p -> LT' m p
ltTrans ZltS     (SltS _) = ZltS
ltTrans (SltS p) (SltS q) = SltS (ltTrans p q)
```

And every pair of natural numbers satisfies **trichotomy**: either `m < n`,
or `m = n`, or `n < m`:

```haskell
-- | Trichotomy witness: m < n, m = n, or n < m.
data Trichotomy (m :: Nat) (n :: Nat) where
  TriLT :: LT' m n -> Trichotomy m n
  TriEQ :: m :~: n -> Trichotomy m n
  TriGT :: LT' n m -> Trichotomy m n

-- | Every pair of finite naturals satisfies trichotomy.
ltTrichotomy :: foreach (m n :: Nat) -> Trichotomy m n
ltTrichotomy Zero     Zero     = TriEQ Refl
ltTrichotomy Zero     (Succ _) = TriLT ZltS
ltTrichotomy (Succ _) Zero     = TriGT ZltS
ltTrichotomy (Succ m) (Succ n) = case ltTrichotomy m n of
  TriLT p  -> TriLT (SltS p)
  TriEQ eq -> TriEQ (cong Succ eq)
  TriGT p  -> TriGT (SltS p)
```

### Relating `<`, `≤`, and addition

Strict inequality `m < n` is equivalent to `Succ m ≤ n`, and non-strict
inequality `m ≤ n` holds if and only if there exists a natural number `k`
such that `m + k = n`:

```haskell
-- | Strict inequality implies shifted non-strict inequality: m < n -> Succ m <= n.
ltToLe :: LT' m n -> LE (Succ m) n
ltToLe ZltS     = SleS ZleN
ltToLe (SltS p) = SleS (ltToLe p)

-- | Shifted non-strict inequality implies strict inequality: Succ m <= n -> m < n.
leToLt :: LE (Succ m) n -> LT' m n
leToLt (SleS ZleN)     = ZltS
leToLt (SleS (SleS p)) = SltS (leToLt (SleS p))

-- | Witness that m + k = n for some runtime Nat k.
data DiffWitness (m :: Nat) (n :: Nat) where
  MkDiff :: foreach (k :: Nat) -> plus m k :~: n -> DiffWitness m n

-- | From m <= n we can compute a difference witness k with m + k = n.
leToDiff :: foreach (m n :: Nat) -> LE m n -> DiffWitness m n
leToDiff Zero     n p = case p of
  ZleN -> MkDiff n Refl
leToDiff (Succ m) n p = case n of
  Zero    -> case p of {}
  Succ n' -> case p of
    SleS q -> case leToDiff m n' q of
      MkDiff k eq -> MkDiff k (rewrite eq Refl)

-- | Conversely, m <= m + k for any finite m and k.
diffToLe :: foreach (m k :: Nat) -> LE m (plus m k)
diffToLe Zero     _ = ZleN
diffToLe (Succ m) k = SleS (diffToLe m k)
```

### Monotonicity of strict inequality (`+-mono-<`)

Addition is also monotonic with respect to strict inequality: `m < n` and
`p < q` imply `m + p < n + q`:

```haskell
-- | Right monotonicity of strict inequality: if p < q then n + p < n + q.
plusMonoLtR :: foreach (n :: Nat) -> LT' p q -> LT' (plus n p) (plus n q)
plusMonoLtR Zero     pq = pq
plusMonoLtR (Succ n) pq = SltS (plusMonoLtR n pq)

-- | Left monotonicity of strict inequality: if m < n then m + p < n + p.
plusMonoLtL :: foreach (m n p :: Nat)
            -> LT' m n -> LT' (plus m p) (plus n p)
plusMonoLtL m n Zero     mn = rewrite (plusZero m) (rewrite (plusZero n) mn)
plusMonoLtL m n (Succ p) mn =
  rewrite (plusSucc m p)
    (rewrite (plusSucc n p) (SltS (plusMonoLtL m n p mn)))

-- | Combined monotonicity of strict inequality (`+-mono-<`):
-- if m < n and p < q then m + p < n + q.
plusMonoLt :: foreach (m n p q :: Nat)
           -> LT' m n -> LT' p q -> LT' (plus m p) (plus n q)
plusMonoLt m n p q mn pq = ltTrans (plusMonoLtL m n p mn) (plusMonoLtR n pq)
```

## Even and odd

Inductive relations can also be defined **mutually**. A number is **even** if
it is zero, or the successor of an **odd** number; a number is **odd** if it
is the successor of an **even** number.

In Agda, mutually recursive datatypes require forward type signatures before
their definitions. In Haskell, top-level definitions in a module are mutually
recursive automatically, so we write `Even` and `Odd` directly:

```haskell
-- | Mutually inductive parity predicates on Nat.
data Even (n :: Nat) where
  EvenZ :: Even Zero
  EvenS :: Odd n -> Even (Succ n)

data Odd (n :: Nat) where
  OddS :: Even n -> Odd (Succ n)
```

Now we prove that the sum of two even numbers is even, mutually with the fact
that the sum of an odd number and an even number is odd—and similarly for the
other two combinations of parity. Notice that none of these four theorems
even need `foreach` binders: pattern matching on the GADT proof `Even m` or
`Odd m` refines `m` enough for GHC to reduce `plus m n` directly!

```haskell
-- | Even + Even = Even (no `foreach` needed: GADT matching refines `m`).
evenPlusEven :: Even m -> Even n -> Even (plus m n)
evenPlusEven EvenZ      en = en
evenPlusEven (EvenS om) en = EvenS (oddPlusEven om en)

-- | Odd + Even = Odd.
oddPlusEven :: Odd m -> Even n -> Odd (plus m n)
oddPlusEven (OddS em) en = OddS (evenPlusEven em en)

-- | Even + Odd = Odd.
evenPlusOdd :: Even m -> Odd n -> Odd (plus m n)
evenPlusOdd EvenZ      on = on
evenPlusOdd (EvenS om) on = OddS (oddPlusOdd om on)

-- | Odd + Odd = Even.
oddPlusOdd :: Odd m -> Odd n -> Even (plus m n)
oddPlusOdd (OddS em) on = EvenS (evenPlusOdd em on)
```

Furthermore, every natural number is either even or odd, and no natural
number is both:

```haskell
-- | Every natural number is either even or odd.
evenOrOdd :: foreach (n :: Nat) -> Either (Even n) (Odd n)
evenOrOdd Zero     = Left EvenZ
evenOrOdd (Succ n) = case evenOrOdd n of
  Left  ev -> Right (OddS ev)
  Right od -> Left  (EvenS od)

-- | No natural number is both even and odd.
notBothEvenOdd :: Even n -> Odd n -> Void
notBothEvenOdd (EvenS o) (OddS e) = notBothEvenOdd e o
```

## Bin-predicates (canonical binary representations)

Recall the `Bin` representation of binary numbers from [Naturals](/Naturals/)
and the round-trip proof `fromTo` from [Induction](/Induction/). Why didn't
we prove the opposite round trip `toBin (fromBin b) :~: b` for *all* `b :: Bin`?
Because `Bin` allows non-canonical bitstrings with leading zeros, such as
`Nil` (value `0`) and `X0 (X0 Nil)` (also value `0`), whereas `toBin 0` is
`X0 Nil`.

Following PLFA's **Bin-predicates** stretch exercise, we define two unary
predicates on `Bin`:

- `One b` holds when `b` has at least one `1` bit and no leading zeros
  (i.e. its most significant bit is `1`, representing a strictly positive
  number).
- `Can b` holds when `b` is a **canonical** binary numeral: either canonical
  zero (`X0 Nil`), or a positive canonical numeral (`One b`).

```haskell
-- | Evidence that a binary number is positive and has no leading zero bits.
data One (b :: Bin) where
  OneX1  :: One (X1 Nil)
  OneX0  :: One b -> One (X0 b)
  OneX1' :: One b -> One (X1 b)

-- | Evidence that a binary number is in canonical form (unique per natural).
data Can (b :: Bin) where
  CanZ   :: Can (X0 Nil)
  CanOne :: One b -> Can b
```

First, incrementing preserves both `One` and `Can`, so converting any natural
number to binary produces a canonical bitstring (`toBinCan`, PLFA's `to-Can`):

```haskell
-- | Incrementing a positive canonical binary number stays positive canonical.
incOne :: foreach (b :: Bin) -> One b -> One (inc b)
incOne Nil    p = case p of {}
incOne (X0 _) p = case p of
  OneX0 o -> OneX1' o
incOne (X1 b) p = case b of
  Nil -> case p of
    OneX1    -> OneX0 OneX1
    OneX1' o -> case o of {}
  X0 b' -> case p of
    OneX1' o -> OneX0 (incOne (X0 b') o)
  X1 b' -> case p of
    OneX1' o -> OneX0 (incOne (X1 b') o)

-- | Incrementing any canonical binary number yields a canonical binary number.
incCan :: foreach (b :: Bin) -> Can b -> Can (inc b)
incCan Nil    p = case p of {}
incCan (X0 _) p = case p of
  CanZ             -> CanOne OneX1
  CanOne (OneX0 o) -> CanOne (OneX1' o)
incCan (X1 b) p = case p of
  CanOne o -> CanOne (incOne (X1 b) o)

-- | Converting any natural number to binary produces a canonical bitstring (`to-Can`).
toBinCan :: foreach (n :: Nat) -> Can (toBin n)
toBinCan Zero     = CanZ
toBinCan (Succ n) = incCan (toBin n) (toBinCan n)
```

Second, we prove the converse round-trip law `toFromCan`: for every canonical
bitstring `b` (witnessed by `Can b`), `toBin (fromBin b) :~: b`. We establish
that every `One` bitstring denotes a strictly positive natural (`onePos`),
and that doubling a positive natural shifts its binary representation left by
a zero bit (`toBinDoubleSucc`):

```haskell
-- | Witness that a natural number is strictly positive (`n = Succ k`).
data PosNat (n :: Nat) where
  MkPos :: foreach (k :: Nat) -> n :~: Succ k -> PosNat n

-- | Every `One` bitstring represents a strictly positive natural number.
onePos :: foreach (b :: Bin) -> One b -> PosNat (fromBin b)
onePos Nil    o = case o of {}
onePos (X0 b) o = case o of
  OneX0 o' -> case onePos b o' of
    MkPos k eq -> rewrite eq (MkPos (plus k (Succ k)) Refl)
onePos (X1 b) _ = case b of
  Nil   -> MkPos Zero Refl
  X0 b' -> MkPos (plus (fromBin (X0 b')) (fromBin (X0 b'))) Refl
  X1 b' -> MkPos (plus (fromBin (X1 b')) (fromBin (X1 b'))) Refl

-- | Doubling a positive natural shifts its binary representation left by one zero bit.
toBinDoubleSucc :: foreach (n :: Nat) -> toBin (plus (Succ n) (Succ n)) :~: X0 (toBin (Succ n))
toBinDoubleSucc Zero     = Refl
toBinDoubleSucc (Succ k) =
  rewrite (plusSucc (Succ k) (Succ k))
    (rewrite (toBinDoubleSucc k) Refl)

toFromDoubleOne :: foreach (b :: Bin) -> One b -> toBin (plus (fromBin b) (fromBin b)) :~: X0 b
toFromDoubleOne b o =
  let ih = toFromOne b o
  in case onePos b o of
    MkPos k eq -> go (toBinDoubleSucc k) eq ih
  where
    go :: toBin (plus (Succ k) (Succ k)) :~: X0 (toBin (Succ k))
       -> fromBin b :~: Succ k
       -> toBin (fromBin b) :~: b
       -> toBin (plus (fromBin b) (fromBin b)) :~: X0 b
    go dbl Refl Refl = dbl

-- | Round-trip law for positive canonical bitstrings: `toBin (fromBin b) = b`.
toFromOne :: foreach (b :: Bin) -> One b -> toBin (fromBin b) :~: b
toFromOne Nil    o = case o of {}
toFromOne (X0 b) o = case o of
  OneX0 o' -> toFromDoubleOne b o'
toFromOne (X1 b) o = case b of
  Nil -> case o of
    OneX1    -> Refl
    OneX1' x -> case x of {}
  X0 b' -> case o of
    OneX1' o' -> cong inc (toFromDoubleOne (X0 b') o')
  X1 b' -> case o of
    OneX1' o' -> cong inc (toFromDoubleOne (X1 b') o')

-- | Full round-trip law for canonical binary numbers (`to-from`):
-- together with `Induction.fromTo`, `Nat` and canonical `Bin` are in bijection.
toFromCan :: foreach (b :: Bin) -> Can b -> toBin (fromBin b) :~: b
toFromCan Nil    c = case c of
  CanOne o -> case o of {}
toFromCan (X0 b) c = case b of
  Nil   -> case c of
    CanZ     -> Refl
    CanOne o -> case o of { OneX0 o' -> case o' of {} }
  X0 b' -> case c of
    CanOne o -> toFromOne (X0 (X0 b')) o
  X1 b' -> case c of
    CanOne o -> toFromOne (X0 (X1 b')) o
toFromCan (X1 b) c = case c of
  CanOne o -> toFromOne (X1 b) o
```

Together with `fromTo` in [Induction](/Induction/), `toBinCan` and `toFromCan`
establish a full constructive bijection between `Nat` and canonical `Bin`!

### Negative control: `1 <= 0` is uninhabited

We verify that GHC rejects an attempt to construct `LE 1 0` using `ZleN`:

```{.haskell .fail name="NegOneLeZero" expect="GHC-83865"}
{-# LANGUAGE DependentTypes #-}
module NegOneLeZero (oneLeZero) where

import HaskLib.Nat (Nat (..))
import PLFH.Part1.Relations (LE (..))

oneLeZero :: LE 1 0
oneLeZero = ZleN
```

## Changes from PLFA

- Adapted from [Relations](https://plfa.inf.ed.ac.uk/Relations/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part1/Relations.lagda.md)),
  licensed under CC BY 4.0.
- Every core theorem (`LE`, `invSleS`, `invZleN`, `leRefl`, `leTrans`,
  `leAntisym`, `Total`, `leTotal`, `plusMonoR`, `plusMonoL`, `plusMono`,
  `timesMonoR`, `timesMonoL`, `timesMono`, `LT'`, `ltTrans`, `Trichotomy`,
  `ltTrichotomy`, `ltToLe`, `leToLt`, `DiffWitness`, `leToDiff`, `diffToLe`,
  `plusMonoLtR`, `plusMonoLtL`, `plusMonoLt`, `Even`/`Odd` with all four parity
  sums plus `evenOrOdd`/`notBothEvenOdd`, and the complete `One`/`Can`
  canonical binary bijection `toBinCan` & `toFromCan`) ports directly and
  passes `-dcore-lint -dstg-lint`.
- All promoted constructors (`Zero`, `Succ`, `Nil`, `X0`, `X1`) are written
  without leading `'` ticks under `-XDataKinds`, and visible `cong` from
  [Induction](/Induction/) handles both the constructor `Succ` and the ordinary
  unary function `inc`.
- `leTotal`, `plusMonoL`, `plusMonoLtL`, and `ltTrichotomy` split their
  retained arguments directly in function equations.
- `evenPlusEven`, `oddPlusEven`, `evenPlusOdd`, and `oddPlusOdd` need no
  `foreach` binders at all: matching on the GADT proof refines `m` enough for
  GHC to reduce ordinary `plus m n` directly.
