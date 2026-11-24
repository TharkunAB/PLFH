---
title: "Induction: Proof by Induction"
prev: /Naturals/
next: /Relations/
src: content/part1/Induction.md
module: PLFH.Part1.Induction
plfaChapter: https://plfa.inf.ed.ac.uk/22.08/Induction/
---

```haskell
{-# LANGUAGE AllowAmbiguousTypes, DataKinds, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, Modifiers, PolyKinds, TypeApplications, TypeOperators #-}
module PLFH.Part1.Induction
  ( congSecond
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
  , fromInc
  , fromTo
  , twoTimesThree
  ) where

import Data.Type.Equality ((:~:) (Refl), sym, trans)
import GHC.Exts (U)
import HaskLib (rewrite)
import HaskLib.Nat (Nat (..), congFirst, congSucc, plus, plusSucc, plusZero)
import PLFH.Part1.Naturals (Bin (..), fromBin, inc, times, toBin)
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

Just as `HaskLib.Nat` provides `congFirst` to lift an equality through the
first argument of a binary size function, we define `congSecond` for the
second argument:

```haskell
-- | Lift an equality through the second argument of a binary size function.
congSecond :: forall (f :: Nat %U -> Nat %U -> Nat) l m n.
              m :~: n -> f l m :~: f l n
congSecond Refl = Refl

-- | Rearranging parentheses in a four-way sum.
plusRearrange :: foreach (m :: Nat) -> foreach (n :: Nat)
              -> foreach (p :: Nat) -> foreach (q :: Nat)
              -> plus (plus m n) (plus p q) :~: plus (plus m (plus n p)) q
plusRearrange m n p q =
  plusAssoc m n (plus p q)
    `trans` congSecond @plus @m (sym (plusAssoc n p q))
    `trans` sym (plusAssoc m (plus n p) q)
```

<div class="wip-notice">
<strong>[WIP NOTICE — Partial application in generic <code>cong @(plus m)</code> (R03/R17/R23)]</strong>
Writing PLFA's direct section <code>cong @(plus m) (sym (plusAssoc n p q))</code>
with a generic unary <code>cong :: forall (f :: a %U -> b) x y. x :~: y -> f x :~: f y</code>
currently fails on GHC <code>db2586fdc2</code> with an <em>untouchable</em>
meta-variable error bound by the retained application. Passing the unapplied
binary function and fixed argument explicitly via <code>congSecond @plus @m</code>
checks cleanly. See
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R03_CongPartialApp.hs"><code>reproducers/R03_CongPartialApp.hs</code></a>.
</div>

## Exercises checked directly

### `+-swap` (recommended) {#plus-swap}

```haskell
-- | Swap the first two addends: m + (n + p) = n + (m + p).
plusSwap :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
         -> plus m (plus n p) :~: plus n (plus m p)
plusSwap m n p =
  sym (plusAssoc m n p)
    `trans` congFirst @plus @p (plusComm m n)
    `trans` plusAssoc n m p
```

<div class="wip-notice">
<strong>[WIP NOTICE — <code>rewrite</code> on a retained call inside <code>trans</code>/<code>congSucc</code> (R03)]</strong>
Using <code>rewrite (plusComm m n) Refl</code> inside a chain of
<code>`trans`</code> calls (or inside <code>congSucc</code>) fails on GHC
<code>1a02a866e7</code> because the retained application binds an implication
constraint that renders the surrounding meta-variables untouchable. Putting
<code>rewrite</code> on the <em>outside</em> of the expression, or using
<code>congFirst</code>/<code>congSecond</code>, works cleanly. See
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R03_WithEqualityUnderTrans.hs"><code>reproducers/R03_WithEqualityUnderTrans.hs</code></a>.
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

### Monus & Exponentiation exercises (`0∸n≡0`, `∸-+-assoc`, `+*^`)

<div class="wip-notice">
<strong>[WIP NOTICE — Blocked on open source equations for <code>monus</code> and <code>pow</code> (R13/R16)]</strong>
Because GHC <code>db2586fdc2</code> does not yet publish open source equations
for <code>monus</code> or <code>pow</code>, the following PLFA Induction
exercises cannot be stated directly over ordinary <code>monus</code> and
<code>pow</code> without duplicating them as type families:
<ul>
  <li><code>zeroMonus :: foreach (n :: Nat) -&gt; monus 'Zero n :~: 'Zero</code></li>
  <li><code>monusPlusAssoc :: foreach (m :: Nat) -&gt; foreach (n :: Nat) -&gt; foreach (p :: Nat) -&gt; monus (monus m n) p :~: monus m (plus n p)</code></li>
  <li><code>powPlus</code>, <code>powMul</code>, <code>powTimes</code> (exponentiation laws <code>+*^</code>)</li>
</ul>
Following PLFH's yardstick policy, we leave these un-worked-around until R13/R16
supports them. Minimal reproducers:
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_MonusOpenEq.hs"><code>R13_MonusOpenEq.hs</code></a>
and
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_PowOpenEq.hs"><code>R13_PowOpenEq.hs</code></a>.
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

## Changes from PLFA `v22.08`

- Adapted from [Induction (v22.08)](https://plfa.inf.ed.ac.uk/22.08/Induction/)
  ([source](https://github.com/plfa/plfa.github.io/blob/e2d545f3df0db4d4206c5448735665abde02d81f/src/plfa/part1/Induction.lagda.md)).
- Reused `plusZero` (`+-identityʳ`) and `plusSucc` (`+-suc`) from `HaskLib.Nat`.
- Checked direct ports of `plusAssoc`, `plusAssocRewrite`, `plusComm`,
  `plusRearrange`, `plusSwap`, `timesDistribPlus`, `timesAssoc`, `timesZeroR`,
  `timesSuccR`, `timesComm`, `fromInc`, and `fromTo`.
- Uses `HaskLib.rewrite` (corresponding to Agda's `rewrite`, with `withEquality` retained in `HaskLib` as a compatibility alias).
- Added an explicit negative control (`NegZeroSucc`) verifying GHC rejects
  `'Zero :~: 'Succ 'Zero` (`GHC-83865`).
- Marked `monus` and `pow` exercises, second-column equation splitting,
  `cong @(plus m)`, and nested `rewrite` under `trans` with `[WIP NOTICE]`
  callouts and minimal reproducers.
