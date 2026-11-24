---
title: "Equality: Equality and equational reasoning"
prev: /Relations/
next: /Isomorphism/
src: content/part1/Equality.md
module: PLFH.Part1.Equality
plfaChapter: https://plfa.inf.ed.ac.uk/Equality/
---

```haskell
{-# LANGUAGE AllowAmbiguousTypes, DataKinds, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, Modifiers, PolyKinds, RankNTypes, RequiredTypeArguments #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications, TypeOperators #-}
module PLFH.Part1.Equality
  ( EqP (..)
  , toEqP
  , symP
  , transP
  , congP
  , congAppP
  , substP
  , substU
  , beginEq
  , stepEq
  , qedEq
  , plusZeroChain
  , Leibniz
  , leibnizRefl
  , leibnizTrans
  , eqToLeibniz
  , leibnizToEq
  , LeibnizU
  , leibnizUSym
  , leibnizUToEq
  , evenComm
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import GHC.Exts (U)
import HaskLib (rewrite)
import HaskLib.Nat (Nat (..), congSucc, plus)
import PLFH.Part1.Induction (plusComm)
import PLFH.Part1.Relations (Even (..))
```

So far we have imported propositional equality `(:~:)` from
`Data.Type.Equality`. In this chapter we define propositional equality
from scratch, prove its fundamental properties (`sym`, `trans`, `cong`,
`cong-app`, `subst`), and compare it with **Leibniz equality**—which
turns out to exercise two marquee Dependent Haskell features at once:
**matchability arrows (`%U`)** (Serokell R23) and **type-level lambdas**
(Serokell R17)!

## Defining equality (`_≡_`)

In PLFA, propositional equality is a single-constructor indexed datatype
whose constructor `refl` witnesses that every value equals itself:

```haskell
-- | Kind-polymorphic propositional equality (matching Data.Type.Equality.:~:).
data EqP (x :: a) (y :: a) where
  ReflP :: EqP x x
```

## Equality is an equivalence relation

Symmetry and transitivity follow immediately by pattern matching on `ReflP`:

```haskell
-- | Symmetry: if x = y then y = x.
symP :: EqP x y -> EqP y x
symP ReflP = ReflP

-- | Transitivity: if x = y and y = z then x = z.
transP :: EqP x y -> EqP y z -> EqP x z
transP ReflP q = q
```

## Congruence and Substitution

In Dependent Haskell, type-level functions come in two flavors controlled by
**matchability** (`-XModifiers`, Serokell R23):

- **Matchable arrows (`a -> b`)** classify generative, injective type
  constructors such as `Even :: Nat -> Type` or `EqP x :: a -> Type`.
- **Unmatchable arrows (`a %U -> b`)** classify arbitrary type-level functions,
  including promoted ordinary Haskell functions (like `plus`) and type-level
  lambdas (`\z -> ...`).

Using `%U` gives us a fully general congruence and application-congruence:

```haskell
-- | Congruence: equal inputs yield equal outputs under any unmatchable function f.
congP :: forall {a} {b} (f :: a %U -> b) (x :: a) (y :: a).
         EqP x y -> EqP (f x) (f y)
congP ReflP = ReflP

-- | Application congruence: equal functions yield equal results at any input x.
congAppP :: forall {a} {b} (f :: a %U -> b) (g :: a %U -> b) (x :: a).
            EqP f g -> EqP (f x) (g x)
congAppP ReflP = ReflP

-- | Substitution for matchable predicates (e.g. GADTs like `Even`).
substP :: forall {a} (p :: a -> Type) (x :: a) (y :: a).
          EqP x y -> p x -> p y
substP ReflP px = px

-- | Substitution for unmatchable predicates (e.g. type lambdas or promoted functions).
substU :: forall {a} (p :: a %U -> Type) (x :: a) (y :: a).
          EqP x y -> p x -> p y
substU ReflP px = px
```

### Example: `even-comm` via substitution

In PLFA, `even-comm` uses `subst even (+-comm m n)` to transfer a proof of
`even (m + n)` into a proof of `even (n + m)`. Here we write the exact
same theorem using `substP @Even`:

```haskell
-- | Convert standard `Data.Type.Equality.:~:` into our local `EqP`.
toEqP :: x :~: y -> EqP x y
toEqP Refl = ReflP

-- | If m + n is even, then n + m is even (PLFA's direct `subst even (+-comm m n)`).
evenComm :: foreach (m :: Nat) -> foreach (n :: Nat)
         -> Even (plus m n) -> Even (plus n m)
evenComm m n ev = substP @Even (toEqP (plusComm m n)) ev
```

<div class="note-box">
<strong>Fixed compiler panic (<code>692eae0778</code> / <code>9cc4065fab</code>):</strong>
On earlier GHC baselines (<code>db2586fdc2</code>–<code>1a02a866e7</code>),
<code>substP @Even (toEqP (plusComm m n)) ev</code> triggered an internal
<code>tcInstFun: invalid retained instantiations</code> panic at
<code>compiler/GHC/Tc/Gen/App.hs:3947</code>. Fixed on
<code>dependent-haskell</code> and verified as regression check
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/fixed/R03_TcInstFunPanic.hs"><code>reproducers/fixed/R03_TcInstFunPanic.hs</code></a>.
</div>

## Equational reasoning chains with `RequiredTypeArguments`

In PLFA, chains of equalities are written with `begin ... ≡⟨ reason ⟩ ... ∎`
so every intermediate expression is checked by the typechecker. In GHC with
`RequiredTypeArguments` (`forall x y z -> ...`), we can write explicit
equational reasoning combinators where the intermediate types appear directly
in the proof term:

```haskell
-- | Start an equational reasoning chain from `x` to `y`.
beginEq :: forall x y -> x :~: y -> x :~: y
beginEq _ _ p = p

-- | End an equational reasoning chain at `x`.
qedEq :: forall x -> x :~: x
qedEq _ = Refl

-- | One reasoned step: from `x` to `y` by `p`, followed by `y` to `z`.
stepEq :: forall x y z -> x :~: y -> y :~: z -> x :~: z
stepEq _ _ _ Refl Refl = Refl

-- | Example equational chain proving `n + 0 = n`.
plusZeroChain :: foreach (n :: Nat) -> plus n 'Zero :~: n
plusZeroChain Zero     = beginEq (type (plus 'Zero 'Zero)) (type 'Zero) (qedEq (type 'Zero))
plusZeroChain (Succ n) =
  stepEq (type (plus ('Succ n) 'Zero)) (type ('Succ (plus n 'Zero))) (type ('Succ n))
    Refl
    (stepEq (type ('Succ (plus n 'Zero))) (type ('Succ n)) (type ('Succ n))
      (congSucc (plusZeroChain n))
      (qedEq (type ('Succ n))))
```

## Leibniz equality

Gottfried Wilhelm Leibniz proposed defining equality via *the identity of
indiscernibles*: `x` equals `y` if every predicate `P` that holds of `x`
also holds of `y`.

With matchable predicates (`a -> Type`), reflexivity, transitivity, and
equivalence with `EqP` work cleanly:

```haskell
-- | Leibniz equality over matchable predicates `p :: a -> Type`.
type Leibniz (x :: a) (y :: a) = forall (p :: a -> Type). p x -> p y

leibnizRefl :: Leibniz x x
leibnizRefl px = px

leibnizTrans :: forall {a} (x :: a) (y :: a) (z :: a).
                Leibniz x y -> Leibniz y z -> Leibniz x z
leibnizTrans xy yz px = yz (xy px)

eqToLeibniz :: EqP x y -> Leibniz x y
eqToLeibniz ReflP px = px

leibnizToEq :: forall {a} (x :: a) (y :: a). Leibniz x y -> EqP x y
leibnizToEq f = f @(EqP x) ReflP
```

What about **symmetry** of Leibniz equality (`Leibniz x y -> Leibniz y x`)?
In PLFA, symmetry instantiates `P` with the lambda `λ z → z ≡ x`.
With Dependent Haskell's **type-level lambdas (R17)** and **unmatchable
arrows (`%U`, R23)**, we can write that exact predicate directly!

```haskell
-- | Leibniz equality over unmatchable predicates `p :: a %U -> Type`.
type LeibnizU (x :: a) (y :: a) = forall (p :: a %U -> Type). p x -> p y

-- | Symmetry of LeibnizU using an inline type-level lambda (R17)!
leibnizUSym :: forall {a} (x :: a) (y :: a). LeibnizU x y -> LeibnizU y x
leibnizUSym xy = case xy @(\z -> EqP z x) ReflP of
  ReflP -> \px -> px

-- | Recovering EqP from LeibnizU via an inline type-level lambda.
leibnizUToEq :: forall {a} (x :: a) (y :: a). LeibnizU x y -> EqP x y
leibnizUToEq f = f @(\z -> EqP x z) ReflP
```

<div class="wip-notice">
<strong>[WIP NOTICE — Matchability subtyping in Leibniz equality (R23)]</strong>
While inline type-level lambdas inside visible type applications
(<code>xy @(\z -&gt; EqP z x)</code>) <em>do</em> work on GHC
<code>db2586fdc2</code>, instantiating <code>LeibnizU</code> (which expects
an unmatchable predicate <code>a %U -&gt; Type</code>) directly at the
matchable constructor <code>@(EqP x)</code> fails with <code>GHC-83865</code>
(<em>Couldn't match kind Matchable with Unmatchable</em>), requiring an
eta-expanded lambda <code>@(\z -&gt; EqP x z)</code>. See minimal reproducer
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R23_MatchabilityInLeibniz.hs"><code>reproducers/R23_MatchabilityInLeibniz.hs</code></a>.
</div>

## Changes from PLFA

- Adapted from [Equality](https://plfa.inf.ed.ac.uk/Equality/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part1/Equality.lagda.md)).
- `EqP`, `symP`, `transP`, `congP`, `congAppP`, `substP`, `substU`,
  `evenComm`, and both `Leibniz` and `LeibnizU` (with `leibnizUSym` via R17
  type-level lambdas!) port directly and pass `-dcore-lint -dstg-lint`.
- Explained GHC's matchable (`->`) vs. unmatchable (`%U ->`) arrow distinction
  and marked the R17/R23 boundaries with `[WIP NOTICE]`.
- Note on universe polymorphism: PLFA finishes with level-polymorphic `_≡′_`;
  Haskell's `PolyKinds` already makes `EqP` kind-polymorphic by default.
