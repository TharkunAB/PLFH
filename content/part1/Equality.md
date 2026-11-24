---
title: "Equality: Equality and equational reasoning"
prev: /Relations/
next: /Isomorphism/
src: content/part1/Equality.md
module: PLFH.Part1.Equality
plfaChapter: https://plfa.inf.ed.ac.uk/Equality/
---

Much of our reasoning has involved equality. Given two terms `M` and `N`,
both of type `A`, we write `M :~: N` (in Agda, `M ≡ N`) to assert that `M`
and `N` are interchangeable. So far we have imported propositional equality
`(:~:)` from `Data.Type.Equality`. In this chapter we look under the hood:
we define propositional equality from scratch, prove its fundamental
properties (`sym`, `trans`, `cong`, `cong-app`, `subst`), explain equational
reasoning chains and rewriting, and compare Martin-Löf's inductive definition
of equality (1975) with **Leibniz equality** (1686)—which exercises two
marquee Dependent Haskell features at once: **matchability arrows (`%U`)**
and **type-level lambdas**.

## Imports

We import `Type` from `Data.Kind`, `Matchability` from `GHC.Types`, `U` from
`GHC.Exts`, `(:~:)` from `Data.Type.Equality`, `Nat` and `plus` from
`HaskLib.Nat`, `cong` and `plusComm` from [Induction](/Induction/), and
`Even` from [Relations](/Relations/).

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
import GHC.Types (Matchability)
import HaskLib.Nat (Nat (..), plus)
import PLFH.Part1.Induction (cong, plusComm)
import PLFH.Part1.Relations (Even (..))
```

## Equality

We declare equality as an inductive relation with a single constructor `ReflP`
witnessing that any value `x` (of any kind `a`, thanks to `-XPolyKinds`) is
equal to itself:

```haskell
-- | Kind-polymorphic propositional equality (matching Data.Type.Equality.:~:).
data EqP (x :: a) (y :: a) where
  ReflP :: EqP x x
```

That single line is the entire definition! As Martin-Löf observed, once
equality is defined inductively with `ReflP` as its sole constructor, every
other law of equality—symmetry, transitivity, congruence, and substitution—is
not an axiom, but a **theorem** proved by pattern matching on `ReflP`.

## Equality is an equivalence relation

An **equivalence relation** is one which is reflexive, symmetric, and
transitive. Reflexivity is built in as the constructor `ReflP`; symmetry and
transitivity follow immediately by pattern matching on `ReflP` (which forces
GHC to unify `x` and `y` in the body of the clause):

```haskell
-- | Symmetry: if x = y then y = x.
symP :: EqP x y -> EqP y x
symP ReflP = ReflP

-- | Transitivity: if x = y and y = z then x = z.
transP :: EqP x y -> EqP y z -> EqP x z
transP ReflP q = q
```

Notice how `transP ReflP q = q` only needs to match the first equality: once
`ReflP` unifies `x` with `y`, `q :: EqP y z` already has type `EqP x z`.

## Congruence and substitution

Equality satisfies **congruence**: if two terms are equal, they remain equal
after applying the same function to both (`congP`), and if two functions are
equal, applying them to the same argument yields equal results (`congAppP`).
Equality also satisfies **substitution**: if `x` and `y` are equal, and a
property `p` holds of `x`, then `p` also holds of `y`.

In Dependent Haskell, type-level functions come in two flavors controlled by
**matchability** (`-XModifiers`):

- **Matchable arrows (`a -> b`)** classify generative, injective type
  constructors such as `Succ :: Nat -> Nat`, `Even :: Nat -> Type`, or
  `EqP x :: a -> Type`.
- **Unmatchable arrows (`a %U -> b`)** classify arbitrary type-level functions,
  including promoted ordinary Haskell functions (like `plus m`) and type-level
  lambdas (`\z -> ...`).

By quantifying over `{m :: Matchability}` with `RequiredTypeArguments` in
`congP`, a single Agda-style congruence combinator handles *both* constructors
(`congP Succ`) and promoted functions (`congP (plus m)`) with no `@` needed!
For substitution, we provide both `substP` (for matchable predicates such as
GADTs like `Even`) and `substU` (for unmatchable predicates such as type
lambdas or promoted functions):

```haskell
-- | Agda-style matchability-polymorphic congruence: works for both constructors
-- (`congP Succ`) and promoted functions (`congP (plus m)`).
congP :: forall {a} {b} {m :: Matchability}.
         forall (f :: a %m -> b) -> forall (x :: a) (y :: a).
         EqP x y -> EqP (f x) (f y)
congP _ ReflP = ReflP

-- | Application congruence: equal functions yield equal results at any input x.
congAppP :: forall {a} {b} {m :: Matchability} (f :: a %m -> b) (g :: a %m -> b) (x :: a).
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

In PLFA, `even-comm` proves that if `m + n` is even then `n + m` is even by
applying `subst even (+-comm m n)`. Here we write the exact same proof using
`substP @Even`:

```haskell
-- | Convert standard `Data.Type.Equality.:~:` into our local `EqP`.
toEqP :: x :~: y -> EqP x y
toEqP Refl = ReflP

-- | If m + n is even, then n + m is even (PLFA's direct `subst even (+-comm m n)`).
evenComm :: foreach (m :: Nat) -> foreach (n :: Nat)
         -> Even (plus m n) -> Even (plus n m)
evenComm m n ev = substP @Even (toEqP (plusComm m n)) ev
```

## Chains of equations

In PLFA, equational reasoning chains are written with mixfix operators:

```text
begin
  e₁
≡⟨ p₁ ⟩
  e₂
≡⟨ p₂ ⟩
  e₃
∎
```

Each intermediate expression `eᵢ` is checked by the typechecker against the
proof step justifying it. In Dependent Haskell with `-XRequiredTypeArguments`
(`forall x y z -> ...`), we can build the exact same self-documenting
combinators where every intermediate type appears directly in the proof term:

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
```

Here is our earlier right-identity proof `plus n Zero :~: n` written as an
explicit equational chain, using `cong Succ` for the inductive step:

```haskell
-- | Example equational chain proving `n + 0 = n`.
plusZeroChain :: foreach (n :: Nat) -> plus n Zero :~: n
plusZeroChain Zero     = beginEq (type (plus Zero Zero)) (type Zero) (qedEq (type Zero))
plusZeroChain (Succ n) =
  stepEq (type (plus (Succ n) Zero)) (type (Succ (plus n Zero))) (type (Succ n))
    Refl
    (stepEq (type (Succ (plus n Zero))) (type (Succ n)) (type (Succ n))
      (cong Succ (plusZeroChain n))
      (qedEq (type (Succ n))))
```

## Rewriting

Just as Agda provides `rewrite` as a compact shorthand for applying `subst`,
`HaskLib` exports `rewrite :: (x :~: y) -> ((x ~ y) => r) -> r`. When you
write `rewrite eq body`, GHC temporarily brings the type equality `x ~ y`
into scope while checking `body`—just as we did in `plusMonoL` in
[Relations](/Relations/) and `plusSwap` in [Induction](/Induction/).

Whenever Agda needs **multiple rewrites** or a **`with` abstraction** to
generalize over an intermediate term before rewriting, Haskell lets you nest
`rewrite eq1 (rewrite eq2 body)` directly or bind the intermediate result in
a `case ... of` expression (or helper function).

## Leibniz equality

The inductive definition of equality above is due to Per Martin-Löf (1975).
Almost three centuries earlier, Gottfried Wilhelm Leibniz (1686) formulated
equality via **the identity of indiscernibles**: two objects are equal if and
only if they satisfy all the same properties.

> *Eadem sunt, quorum unum potest substitui alteri salva veritate.*
> ("Things are the same if one can be substituted for the other with truth preserved.")
> — G. W. Leibniz

(As PLFA reminds us, Mr. Spock put the contrapositive even more concisely:
*"A difference that makes no difference is no difference."*)

In type theory, Leibniz equality states that `x` and `y` of kind `a` are
equal if, for every predicate `p`, a proof of `p x` can be transformed into a
proof of `p y`.

Over matchable predicates (`p :: a -> Type`), reflexivity is the identity
function, transitivity is function composition, and equivalence with `EqP`
follows directly:

```haskell
-- | Leibniz equality over matchable predicates `p :: a -> Type`.
type Leibniz (x :: a) (y :: a) = forall (p :: a -> Type). p x -> p y

-- | Reflexivity of Leibniz equality is the identity function.
leibnizRefl :: Leibniz x x
leibnizRefl px = px

-- | Transitivity of Leibniz equality is function composition.
leibnizTrans :: forall {a} (x :: a) (y :: a) (z :: a).
                Leibniz x y -> Leibniz y z -> Leibniz x z
leibnizTrans xy yz px = yz (xy px)

-- | Martin-Löf equality implies Leibniz equality (indiscernibility of identicals).
eqToLeibniz :: EqP x y -> Leibniz x y
eqToLeibniz ReflP px = px

-- | Leibniz equality implies Martin-Löf equality (identity of indiscernibles).
leibnizToEq :: forall {a} (x :: a) (y :: a). Leibniz x y -> EqP x y
leibnizToEq f = f @(EqP x) ReflP
```

Look closely at `leibnizToEq`: we instantiate `p` with the matchable
partially-applied constructor `EqP x` (whose kind is `a -> Type`), feed it
`ReflP :: EqP x x`, and out pops `EqP x y`!

What about **symmetry** of Leibniz equality (`LeibnizU x y -> LeibnizU y x`)?
In PLFA, `sym-≐` is proved purely inside Leibniz equality without touching
Martin-Löf equality at all, by instantiating `xy` with the predicate
`Q z = P z → P x` and feeding it `refl-≐ P`. In Dependent Haskell today,
capturing an unmatchable predicate variable `p :: a %U -> Type` inside an
inline type-level lambda triggers `GHC-27185`; instead, we prove `leibnizUSym`
using the inline type-level lambda `\z -> EqP z x` (placing the bound variable
on the *left* of `EqP`), feeding it `ReflP :: EqP x x` to obtain `EqP y x`,
and matching on `ReflP`. Because `\z -> EqP z x` is a **type-level lambda**
(unmatchable, `a %U -> Type`), we state symmetry over `LeibnizU` using
Dependent Haskell's **type-level lambdas** and **unmatchable arrows (`%U`)**:

```haskell
-- | Leibniz equality over unmatchable predicates `p :: a %U -> Type`.
type LeibnizU (x :: a) (y :: a) = forall (p :: a %U -> Type). p x -> p y

-- | Symmetry of LeibnizU using an inline type-level lambda `\z -> EqP z x`.
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
(<code>xy @(\z -&gt; EqP z x)</code>) <em>do</em> work,
instantiating <code>LeibnizU</code> (which expects
an unmatchable predicate <code>a %U -&gt; Type</code>) directly at the
matchable constructor <code>@(EqP x)</code> fails with <code>GHC-83865</code>
(<em>Couldn't match kind Matchable with Unmatchable</em>), requiring an
eta-expanded lambda <code>@(\z -&gt; EqP x z)</code>. See minimal reproducer
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R23_MatchabilityInLeibniz.hs"><code>reproducers/R23_MatchabilityInLeibniz.hs</code></a>.
</div>

## Universe polymorphism

In Agda, types live in a hierarchy of universes (`Set`, `Set₁`, `Set₂`, …)
to avoid Russell's paradox, so PLFA concludes this chapter by introducing
universe-polymorphic equality `_≡′_` parameterized by a universe level `ℓ`.

In GHC Haskell with `-XPolyKinds`, the kind parameter `a` in
`data EqP (x :: a) (y :: a)` is already kind-polymorphic by default, so a
single definition of `EqP` works uniformly at `Nat`, `Bin`, `Type`, or any
promoted user-defined datatype without explicit universe levels! (Note the
foundational trade-off: GHC uses `Type :: Type` rather than a stratified
universe hierarchy—so unlike Agda, GHC's type system is not logically
consistent on its own and relies on our proof discipline of structural
termination and zero `undefined`/`unsafeCoerce`.)

#### Exercise `cong₂` (practice)

Define two-argument congruence: given a binary type-level function `f` and
proofs `EqP x x'` and `EqP y y'`, produce `EqP (f x y) (f x' y')`.

#### Exercise `Leibniz` reflexivity, symmetry, and transitivity (practice)

Show that `leibnizTrans` is associative and has `leibnizRefl` as both left
and right identity, and write `eqToLeibnizU :: EqP x y -> LeibnizU x y`.

## Changes from PLFA

- Adapted from [Equality](https://plfa.inf.ed.ac.uk/Equality/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part1/Equality.lagda.md)),
  licensed under CC BY 4.0.
- `EqP`, `symP`, `transP`, matchability-polymorphic `congP`/`congAppP`,
  `substP`, `substU`, `evenComm` (via `substP @Even`), `RequiredTypeArguments`
  equational chains (`beginEq`/`stepEq`/`qedEq`/`plusZeroChain`), and both
  `Leibniz` and `LeibnizU` (with `leibnizUSym` via inline type-level lambdas)
  port directly and pass `-dcore-lint -dstg-lint`.
- All promoted constructors (`Zero`, `Succ`) are written without leading `'`
  ticks under `-XDataKinds`.
- Explained GHC's matchable (`->`) vs. unmatchable (`%U ->`) arrow distinction
  and marked matchability subtyping in `LeibnizU` with `[WIP NOTICE]`
  (`R23_MatchabilityInLeibniz.hs`).
- PLFA's universe-polymorphic `_≡′_` corresponds to GHC's `-XPolyKinds`,
  which already makes `EqP` kind-polymorphic out of the box.
