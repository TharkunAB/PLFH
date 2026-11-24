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
{-# LANGUAGE GADTs, Modifiers, PolyKinds, TypeApplications, TypeOperators #-}
module PLFH.Part1.Induction
  ( cong
  , congSecond
  , plusAssoc
  , plusAssocRewrite
  , plusIdentityR
  , plusSuc
  , plusComm
  , plusRearrange
  , plusSwap
  , timesDistribPlus
  , timesAssoc
  , timesZeroR
  , timesSuccR
  , timesComm
  , timesSwap
  , timesInterchange
  , zeroMonus
  , monusPlusAssoc
  , powPlus
  , powMul
  , powTimes
  , fromInc
  , fromTo
  , twoTimesThree
  ) where

import Data.Type.Equality ((:~:) (Refl), sym, trans)
import GHC.Exts (U)
import HaskLib (rewrite)
import HaskLib.Nat (Nat (..), congFirst, congSucc, plus, plusSucc, plusZero)
import PLFH.Part1.Naturals (Bin (..), fromBin, inc, monus, pow, times, toBin)
```

> Induction makes you feel guilty for getting something out of nothing
> ... but it is one of the greatest ideas of civilization.
> — Herbert Wilf

Now that we have defined natural numbers and arithmetic operations on them,
our next step is to prove properties that they satisfy. Just as in Agda,
properties of inductive datatypes are proved by **induction**, and induction
corresponds directly to **structural recursion**.

## Checking `times` from an importing module

First, we confirm that GHC reduces `times` imported from
`PLFH.Part1.Naturals` at closed values:

```haskell
-- | Evidence that 2 * 3 = 6 using ordinary `times` imported from Naturals.
twoTimesThree :: times ('Succ ('Succ 'Zero)) ('Succ ('Succ ('Succ 'Zero)))
             :~: 'Succ ('Succ ('Succ ('Succ ('Succ ('Succ 'Zero)))))
twoTimesThree = Refl
```

## Our first proof: associativity (`+-assoc`)

Addition is *associative* if parentheses do not matter:

    (m + n) + p ≡ m + (n + p)

In Dependent Haskell, a universal quantifier over runtime natural numbers is
written `foreach (m :: Nat) -> ...`. Each retained argument is an ordinary
runtime `Nat` value that can also appear in the result type.

Here is the direct port of PLFA's `+-assoc`, using `HaskLib.Nat`'s
ordinary `plus` and `congSucc`:

```haskell
-- | Associativity of addition: (m + n) + p = m + (n + p).
plusAssoc :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
          -> plus (plus m n) p :~: plus m (plus n p)
plusAssoc Zero     _ _ = Refl
plusAssoc (Succ m) n p = congSucc (plusAssoc m n p)
```

Let's unpack what GHC checks in each equation:

- **Base case (`Zero`):** GHC refines `m` to `'Zero`. Using the defining
  equation `plus Zero n = n`, both `plus (plus 'Zero n) p` and
  `plus 'Zero (plus n p)` simplify to `plus n p`, so `Refl` checks.
- **Inductive case (`Succ m`):** GHC refines the first argument to `'Succ m`.
  Using `plus (Succ m) n = Succ (plus m n)`, the left side reduces to
  `'Succ (plus (plus m n) p)` and the right side reduces to
  `'Succ (plus m (plus n p))`. The recursive call `plusAssoc m n p` supplies
  the induction hypothesis `plus (plus m n) p :~: plus m (plus n p)`, and
  `congSucc` lifts it through `'Succ`.

<div class="note-box">
<strong>Totality note:</strong>
Agda's termination checker guarantees that <code>+-assoc</code> terminates
for every <code>m</code> because the recursive call decreases <code>m</code>.
GHC does not enforce termination, so we verify by inspection (and our test
harness audit) that every proof decreases structurally on an inductive
argument and contains no <code>undefined</code>, holes, or circular loops.
</div>

### Associativity with `HaskLib.rewrite`

PLFA also proves `+-assoc′` using Agda's `rewrite` keyword. In Dependent
Haskell, `rewrite` (exported from `HaskLib`, equal to `gcastWith`
from `Data.Type.Equality`, with `withEquality` retained as a compatibility
alias) brings a propositional equality `a :~: b` into scope as a local
`a ~ b` constraint for the body—playing the same role as Agda's `rewrite`:

```haskell
-- | Associativity proved via `HaskLib.rewrite` (analogous to Agda `rewrite`).
plusAssocRewrite :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
                 -> plus (plus m n) p :~: plus m (plus n p)
plusAssocRewrite Zero     _ _ = Refl
plusAssocRewrite (Succ m) n p = rewrite (plusAssocRewrite m n p) Refl
```

### Negative control: zero is not equal to its successor

As a sanity check, we verify that GHC rejects a false equality between
`'Zero` and `'Succ 'Zero` directly with `GHC-83865`:

```{.haskell .fail name="NegZeroSucc" expect="GHC-83865"}
{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
module NegZeroSucc (zeroEqualsOne) where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..))

zeroEqualsOne :: (0 :: Nat) :~: 1
zeroEqualsOne = Refl
```

## Commutativity (`+-comm`)

To prove `m + n = n + m`, PLFA first establishes two lemmas:

1. **Right identity (`+-identityʳ`):** `plus m 'Zero :~: m`
2. **Right successor (`+-suc`):** `plus m ('Succ n) :~: 'Succ (plus m n)`

Both lemmas are already proved by induction in `HaskLib.Nat` as `plusZero`
and `plusSucc`! We reuse them directly:

```haskell
-- | Right identity of addition (reused from HaskLib.Nat.plusZero).
plusIdentityR :: foreach (m :: Nat) -> plus m 'Zero :~: m
plusIdentityR = plusZero

-- | Move a successor from the second addend outside (reused from HaskLib.Nat.plusSucc).
plusSuc :: foreach (m :: Nat) -> foreach (n :: Nat)
        -> plus m ('Succ n) :~: 'Succ (plus m n)
plusSuc = plusSucc
```

Now we prove commutativity by induction on the **second** argument `n`:

```haskell
-- | Commutativity of addition: m + n = n + m.
plusComm :: foreach (m :: Nat) -> foreach (n :: Nat) -> plus m n :~: plus n m
plusComm m n = case n of
  Zero   -> plusZero m
  Succ k -> plusSucc m k `trans` congSucc (plusComm m k)
```

<div class="wip-notice">
<strong>[WIP NOTICE — Pattern matching a non-leading retained argument in equations (R03)]</strong>
In Agda, <code>+-comm</code> splits directly on its second argument in the
function equations (<code>+-comm m zero = ...; +-comm m (suc n) = ...</code>).
On GHC <code>db2586fdc2</code>, constructor equations may only split the
<em>first</em> retained index column; writing <code>plusComm m Zero = ...</code>
fails with <code>GHC-83605</code>. Splitting via an explicit <code>case n of</code>
on the right-hand side works cleanly. See
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R03_SecondColumnPattern.hs"><code>reproducers/R03_SecondColumnPattern.hs</code></a>.
</div>

## Rearranging (`+-rearrange`) and Congruence

PLFA uses `+-assoc`, `sym`, and a section `cong (m +_)` to prove:

    (m + n) + (p + q) ≡ (m + (n + p)) + q

With Dependent Haskell's unmatchable function arrow (`%U ->`, Serokell R23)
and partial application of `plus`, we can write PLFA's generic unary `cong`
and apply `cong @(plus m)` directly! (We also keep `congSecond` exported for
binary congruence.)

```haskell
-- | Generic unary congruence for any unmatchable function `f :: a %U -> b`.
cong :: forall {a} {b} (f :: a %U -> b) (x :: a) (y :: a). x :~: y -> f x :~: f y
cong Refl = Refl

-- | Lift an equality through the second argument of a binary size function.
congSecond :: forall (f :: Nat %U -> Nat %U -> Nat) l m n.
              m :~: n -> f l m :~: f l n
congSecond Refl = Refl

-- | Rearranging parentheses in a four-way sum, using PLFA's direct `cong @(plus m)`.
plusRearrange :: foreach (m :: Nat) -> foreach (n :: Nat)
              -> foreach (p :: Nat) -> foreach (q :: Nat)
              -> plus (plus m n) (plus p q) :~: plus (plus m (plus n p)) q
plusRearrange m n p q =
  plusAssoc m n (plus p q)
    `trans` cong @(plus m) (sym (plusAssoc n p q))
    `trans` sym (plusAssoc m (plus n p) q)
```

<div class="note-box">
<strong>Fixed compiler gap (<code>692eae0778</code> / <code>9cc4065fab</code>):</strong>
On earlier baselines (<code>db2586fdc2</code>–<code>1a02a866e7</code>),
<code>cong @(plus m)</code> failed with an untouchable meta-variable error.
That fix is now published on <code>dependent-haskell</code> and tracked as
regression check
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/fixed/R03_CongPartialApp.hs"><code>reproducers/fixed/R03_CongPartialApp.hs</code></a>.
</div>

## Exercises checked directly

### `+-swap` (recommended) {#plus-swap}

```haskell
-- | Swap the first two addends: m + (n + p) = n + (m + p),
-- using `HaskLib.rewrite` directly inside a `trans` chain!
plusSwap :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
         -> plus m (plus n p) :~: plus n (plus m p)
plusSwap m n p =
  sym (plusAssoc m n p)
    `trans` rewrite (plusComm m n) Refl
    `trans` plusAssoc n m p
```

<div class="note-box">
<strong>Fixed compiler gap (<code>692eae0778</code> / <code>9cc4065fab</code>):</strong>
On earlier baselines (<code>db2586fdc2</code>–<code>1a02a866e7</code>),
calling <code>rewrite (plusComm m n) Refl</code> inside <code>`trans`</code>
failed with an untouchable meta-variable error. Fixed and tracked as regression
check
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/fixed/R03_WithEqualityUnderTrans.hs"><code>reproducers/fixed/R03_WithEqualityUnderTrans.hs</code></a>.
</div>

### Multiplication laws (`*-distrib-+`, `*-assoc`, `*-comm`)

All of PLFA's multiplication exercises prove directly using our ordinary
Haskell `times` function!

```haskell
-- | Right distributivity of multiplication over addition:
-- (m + n) * p = m * p + n * p.
timesDistribPlus :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
                 -> times (plus m n) p :~: plus (times m p) (times n p)
timesDistribPlus Zero     _ _ = Refl
timesDistribPlus (Succ m) n p =
  rewrite (timesDistribPlus m n p)
    (sym (plusAssoc p (times m p) (times n p)))

-- | Associativity of multiplication: (m * n) * p = m * (n * p).
timesAssoc :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
           -> times (times m n) p :~: times m (times n p)
timesAssoc Zero     _ _ = Refl
timesAssoc (Succ m) n p =
  rewrite (timesAssoc m n p)
    (timesDistribPlus n (times m n) p)

-- | Right zero for multiplication: m * 0 = 0.
timesZeroR :: foreach (m :: Nat) -> times m 'Zero :~: 'Zero
timesZeroR Zero     = Refl
timesZeroR (Succ m) = timesZeroR m

-- | Right successor for multiplication: m * (Succ n) = m + m * n.
timesSuccR :: foreach (m :: Nat) -> foreach (n :: Nat)
           -> times m ('Succ n) :~: plus m (times m n)
timesSuccR Zero     _ = Refl
timesSuccR (Succ m) n =
  rewrite (timesSuccR m n)
    (congSucc (plusSwap n m (times m n)))

-- | Commutativity of multiplication: m * n = n * m.
timesComm :: foreach (m :: Nat) -> foreach (n :: Nat)
          -> times m n :~: times n m
timesComm Zero     n = sym (timesZeroR n)
timesComm (Succ m) n =
  rewrite (timesComm m n)
    (sym (timesSuccR n m))
```

### Truncated subtraction (`0∸n≡0`, `∸-+-assoc`)

The ordinary `monus` definition in [Naturals](/Naturals/) inspects its second
argument first. At zero, subtraction returns the first argument. At a successor,
it inspects the first argument too. Both possibilities give zero when we
subtract from zero:

```haskell
-- | Subtracting any natural from zero gives zero (`0∸n≡0`).
zeroMonus :: foreach (n :: Nat) -> monus 'Zero n :~: 'Zero
zeroMonus Zero     = Refl
zeroMonus (Succ _) = Refl
```

Subtracting `n` and then `p` gives the same result as subtracting their sum
`n + p`. The proof splits on `n` first; when `n` and `m` are both successors,
the checked subtraction equations cancel a successor on each side and the
induction hypothesis applies to their predecessors:

```haskell
-- | Two successive subtractions subtract the sum of their operands (`∸-+-assoc`).
monusPlusAssoc :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
               -> monus (monus m n) p :~: monus m (plus n p)
monusPlusAssoc m n p = subtractLeft n m p

subtractLeft :: foreach (n :: Nat) -> foreach (m :: Nat) -> foreach (p :: Nat)
             -> monus (monus m n) p :~: monus m (plus n p)
subtractLeft Zero     _ _ = Refl
subtractLeft (Succ n) m p = subtractSucc m n p

subtractSucc :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
             -> monus (monus m ('Succ n)) p :~: monus m (plus ('Succ n) p)
subtractSucc Zero     _ p = zeroMonus p
subtractSucc (Succ m) n p = monusPlusAssoc m n p
```

<div class="note-box">
<strong>Fixed compiler gap (<code>63e2f0974b</code> / <code>76e67f4fdb</code>):</strong>
Checked open equations for ordinary <code>monus</code> published on
<code>dependent-haskell</code> at
<a href="https://github.com/Tritlo/ghc/commit/63e2f0974b174dc86bef79c3a84d1d76fea3dadf"><code>63e2f0974b</code></a>
(tracked as regression check
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/fixed/R13_MonusOpenEq.hs"><code>reproducers/fixed/R13_MonusOpenEq.hs</code></a>),
unlocking both <code>zeroMonus</code> and <code>monusPlusAssoc</code> directly!
</div>

### Exponentiation exercises (`+*^`: `powPlus`, `powMul`, `powTimes`)

With checked carried-argument source equations published in `1f873969e5`, all
three of PLFA's exponentiation laws (`^-distribˡ-+-*`, `^-distribʳ-*`, and
`^-*-assoc`) prove directly over ordinary `pow` from [Naturals](/Naturals/)!

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
    `trans` congSecond @times @a (timesSwap b c d)
    `trans` sym (timesAssoc a c (times b d))

-- | Distributivity of exponentiation over addition (`^-distribˡ-+-*`):
-- m ^ (n + p) = (m ^ n) * (m ^ p).
powPlus :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
        -> pow m (plus n p) :~: times (pow m n) (pow m p)
powPlus m n p = case n of
  Zero   -> sym (plusZero (pow m p))
  Succ k -> rewrite (powPlus m k p)
              (sym (timesAssoc m (pow m k) (pow m p)))

-- | Distributivity of exponentiation over multiplication (`^-distribʳ-*`):
-- (m * n) ^ p = (m ^ p) * (n ^ p).
powMul :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
       -> pow (times m n) p :~: times (pow m p) (pow n p)
powMul m n p = case p of
  Zero   -> Refl
  Succ k -> rewrite (powMul m n k)
              (timesInterchange m n (pow m k) (pow n k))

-- | Associativity of iterated exponentiation (`^-*-assoc`):
-- (m ^ n) ^ p = m ^ (n * p).
powTimes :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
         -> pow (pow m n) p :~: pow m (times n p)
powTimes m n p = case p of
  Zero   -> rewrite (timesZeroR n) Refl
  Succ k -> rewrite (powTimes m n k)
              (sym (powPlus m n (times n k))
                 `trans` congSecond @pow @m (sym (timesSuccR n k)))
```

<div class="note-box">
<strong>Fixed compiler gap (<code>1f873969e5</code>):</strong>
Checked open equations for ordinary <code>pow</code> (structural recursion on
a non-leading argument carrying <code>m</code> unchanged) published on
<code>dependent-haskell</code> at
<a href="https://github.com/Tritlo/ghc/commit/1f873969e589e84b632e5d0304399ab4d2c997e3"><code>1f873969e5</code></a>
(tracked as regression check
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/fixed/R13_PowOpenEq.hs"><code>reproducers/fixed/R13_PowOpenEq.hs</code></a>),
completing <strong>every single arithmetic theorem and exercise in PLFA
Induction</strong>!
</div>

### Binary natural laws (`Bin-laws`, stretch) {#Bin-laws}

On the other hand, PLFA's stretch exercise on binary bitstrings checks
completely with our ordinary Haskell `inc`, `toBin`, and `fromBin` functions!
(As in PLFA, `toBin (fromBin x) :~: x` is false due to leading zeros such as
`Nil` vs `X0 Nil`, while the two valid laws prove cleanly by induction:)

```haskell
-- | Incrementing a bitstring adds one to its unary value.
fromInc :: foreach (b :: Bin) -> fromBin (inc b) :~: 'Succ (fromBin b)
fromInc Nil    = Refl
fromInc (X0 _) = Refl
fromInc (X1 b) =
  rewrite (fromInc b)
    (congSucc (plusSucc (fromBin b) (fromBin b)))

-- | Round-tripping Nat -> Bin -> Nat is the identity.
fromTo :: foreach (n :: Nat) -> fromBin (toBin n) :~: n
fromTo Zero     = Refl
fromTo (Succ n) = fromInc (toBin n) `trans` congSucc (fromTo n)
```

## Changes from PLFA

- Adapted from [Induction](https://plfa.inf.ed.ac.uk/Induction/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part1/Induction.lagda.md)).
- Reused `plusZero` (`+-identityʳ`) and `plusSucc` (`+-suc`) from `HaskLib.Nat`.
- Checked direct ports of **every** theorem and exercise in PLFA Induction:
  `plusAssoc`, `plusAssocRewrite`, `plusComm`, `cong`/`plusRearrange`,
  `plusSwap`, `timesDistribPlus`, `timesAssoc`, `timesZeroR`, `timesSuccR`,
  `timesComm`, `timesSwap`, `timesInterchange`, `zeroMonus`, `monusPlusAssoc`,
  **`powPlus`**, **`powMul`**, **`powTimes`**, `fromInc`, and `fromTo`!
- Uses `HaskLib.rewrite` (corresponding to Agda's `rewrite`, with `withEquality` retained in `HaskLib` as a compatibility alias).
- Added an explicit negative control (`NegZeroSucc`) verifying GHC rejects
  `'Zero :~: 'Succ 'Zero` (`GHC-83865`).
- Only the ergonomic pattern-matching limitation for splitting a non-leading
  retained column directly in function equations (`R03_SecondColumnPattern.hs`)
  remains as a `[WIP NOTICE]` (using explicit `case` works cleanly).
