---
title: "DeBruijn: Intrinsically-typed de Bruijn representation"
prev: /Properties/
next: /Inference/
src: content/part2/DeBruijn.md
module: PLFH.Part2.DeBruijn
plfaChapter: https://plfa.inf.ed.ac.uk/19.08/DeBruijn/
---

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
module PLFH.Part2.DeBruijn
  ( Ty (..)
  , Ctx (..)
  , Lookup (..)
  , Term (..)
  , ext
  , rename
  , exts
  , subst
  , substSingle
  , termTwo
  , Value (..)
  , Step (..)
  , Progress (..)
  , valZero
  ) where

import Data.Kind (Type)
```

In [Lambda](/Lambda/) and [Properties](/Properties/), we gave an
*extrinsic* formalization: terms were untyped first, and a separate typing
judgment `HasType g m a` selected the well-typed terms.

In PLFA's **DeBruijn** chapter, terms are **intrinsically typed**: a value
of type `Term g a` *is already* a well-typed term in context `g` of type `a`,
using de Bruijn indices (`Lookup g a`) instead of variable names. As a result,
substitution is guaranteed type-preserving by construction—**Preservation**
holds automatically by the type of `Step`!

This chapter is a demanding stress test for Dependent Haskell because it
requires **promoting an indexed GADT (`Term g a`) to a kind** and indexing
`Value`, `Step`, and `Progress` over those promoted intrinsically-typed terms.

## Types, contexts, and de Bruijn lookups

```haskell
-- | Simple types: natural numbers and functions.
data Ty = TNat | TArr Ty Ty
  deriving (Show)

-- | Nameless typing contexts.
data Ctx = CEmpty | CExt Ctx Ty

-- | Intrinsically typed de Bruijn indices (Γ ∋ A).
data Lookup (g :: Ctx) (a :: Ty) where
  Z :: Lookup ('CExt g a) a
  S :: Lookup g a -> Lookup ('CExt g b) a
```

## Intrinsically typed terms (`Γ ⊢ A`)

```haskell
-- | Intrinsically typed STLC terms with naturals, case, and μ-recursion.
data Term (g :: Ctx) (a :: Ty) where
  Var  :: Lookup g a -> Term g a
  Lam  :: Term ('CExt g a) b -> Term g ('TArr a b)
  App  :: Term g ('TArr a b) -> Term g a -> Term g b
  Zero :: Term g 'TNat
  Suc  :: Term g 'TNat -> Term g 'TNat
  Case :: Term g 'TNat -> Term g a -> Term ('CExt g 'TNat) a -> Term g a
  Mu   :: Term ('CExt g a) a -> Term g a

-- | Closed intrinsically-typed numeral 2.
termTwo :: Term g 'TNat
termTwo = Suc (Suc Zero)
```

## Simultaneous renaming and substitution (type-preserving by construction!)

All of PLFA's simultaneous renaming (`ext`, `rename`) and capture-avoiding
simultaneous substitution (`exts`, `subst`, `substSingle`) port directly to
Haskell with **identical** types and definitions:

```haskell
-- | Extend a variable renaming under a binder.
ext :: (forall a. Lookup g a -> Lookup d a)
    -> (forall a. Lookup ('CExt g b) a -> Lookup ('CExt d b) a)
ext _   Z     = Z
ext rho (S x) = S (rho x)

-- | Simultaneous renaming on intrinsically typed terms.
rename :: (forall a. Lookup g a -> Lookup d a) -> Term g b -> Term d b
rename rho (Var x)      = Var (rho x)
rename rho (Lam n)      = Lam (rename (ext rho) n)
rename rho (App l m)    = App (rename rho l) (rename rho m)
rename _   Zero         = Zero
rename rho (Suc m)      = Suc (rename rho m)
rename rho (Case l m n) = Case (rename rho l) (rename rho m) (rename (ext rho) n)
rename rho (Mu n)       = Mu (rename (ext rho) n)

-- | Extend a simultaneous substitution under a binder.
exts :: (forall a. Lookup g a -> Term d a)
     -> (forall a. Lookup ('CExt g b) a -> Term ('CExt d b) a)
exts _     Z     = Var Z
exts sigma (S x) = rename S (sigma x)

-- | Simultaneous substitution on intrinsically typed terms.
subst :: (forall a. Lookup g a -> Term d a) -> Term g b -> Term d b
subst sigma (Var x)      = sigma x
subst sigma (Lam n)      = Lam (subst (exts sigma) n)
subst sigma (App l m)    = App (subst sigma l) (subst sigma m)
subst _     Zero         = Zero
subst sigma (Suc m)      = Suc (subst sigma m)
subst sigma (Case l m n) = Case (subst sigma l) (subst sigma m) (subst (exts sigma) n)
subst sigma (Mu n)       = Mu (subst (exts sigma) n)

-- | Substitute a single closed/open term `w` for variable `Z` in `n` (N [ W ]).
substSingle :: Term ('CExt g a) b -> Term g a -> Term g b
substSingle n w = subst (\case { Z -> w; S x -> Var x }) n
```

## Promoting `Term g a`: Values, Reduction, and Progress!

Remarkably, GHC (`db2586fdc2`) **accepts promoting the indexed GADT `Term g a`**
as the kind of `Value`, `Step`, and `Progress` (using `StandaloneKindSignatures`),
including calling our ordinary Haskell `substSingle` directly in the types of
`BetaLam`, `BetaSuc`, and `BetaMu`!

```haskell
-- | Values indexed by promoted intrinsically-typed terms!
type Value :: forall (g :: Ctx) (a :: Ty). Term g a -> Type
data Value m where
  VLam  :: Value ('Lam n)
  VZero :: Value 'Zero
  VSuc  :: Value v -> Value ('Suc v)

-- | Type-preserving one-step reduction indexed by promoted `Term g a`.
type Step :: forall (g :: Ctx) (a :: Ty). Term g a -> Term g a -> Type
data Step m n where
  XiApp1   :: Step l l' -> Step ('App l m) ('App l' m)
  XiApp2   :: Value v -> Step m m' -> Step ('App v m) ('App v m')
  BetaLam  :: Value w -> Step ('App ('Lam n) w) (substSingle n w)
  XiSuc    :: Step m m' -> Step ('Suc m) ('Suc m')
  XiCase   :: Step l l' -> Step ('Case l m n) ('Case l' m n)
  BetaZero :: Step ('Case 'Zero m n) m
  BetaSuc  :: Value v -> Step ('Case ('Suc v) m n) (substSingle n v)
  BetaMu   :: Step ('Mu n) (substSingle n ('Mu n))

-- | Progress witness indexed by a closed intrinsically-typed term.
type Progress :: forall (a :: Ty). Term 'CEmpty a -> Type
data Progress m where
  PStep :: Step m n -> Progress m
  PDone :: Value m  -> Progress m

-- | Concrete witness that `Zero` is already a value.
valZero :: Progress ('Zero :: Term 'CEmpty 'TNat)
valZero = PDone VZero
```

## Intrinsically-typed Progress (`progress :: foreach (m :: Term 'CEmpty a) -> Progress m`)

<div class="wip-notice">
<strong>[WIP NOTICE — <code>foreach</code> over an indexed GADT domain (R03)]</strong>
While GHC <code>db2586fdc2</code> accepts promoting <code>Term g a</code>
and forming the exact signature of intrinsically-typed progress:
<pre class="wip"><code>progress :: forall (a :: Ty). foreach (m :: Term 'CEmpty a) -&gt; Progress m</code></pre>
pattern matching on a retained binder whose type is an <em>indexed GADT</em>
(<code>Term 'CEmpty a</code>) is not yet supported:
<ul>
  <li>Matching in function equations fails with <code>GHC-83605</code>
      (<code>foreach</code> currently requires a closed, unparameterized,
      non-GADT algebraic domain).</li>
  <li>Matching via <code>case m of</code> does not refine the type-level index
      <code>m</code> to the matched constructor (<code>Couldn't match type
      'Lam n0 with m</code>).</li>
</ul>
This cleanly marks the current R03 frontier for intrinsically-typed
metatheory! See minimal reproducers
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R03_ForEachGadtEquations.hs"><code>R03_ForEachGadtEquations.hs</code></a>
and
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R03_ForEachGadtCase.hs"><code>R03_ForEachGadtCase.hs</code></a>.
</div>

## Changes from PLFA `v19.08`

- Adapted from [DeBruijn (v19.08)](https://plfa.inf.ed.ac.uk/19.08/DeBruijn/)
  ([source](https://github.com/plfa/plfa.github.io/blob/63fcbbe25ec3686ff4c6df2c5b58a96b3a2054f3/src/plfa/part2/DeBruijn.lagda.md)).
- `Ty`, `Ctx`, `Lookup`, `Term`, `ext`, `rename`, `exts`, `subst`,
  `substSingle`, and the GADT-promoted `Value`, `Step`, and `Progress`
  definitions all compile cleanly with `-dcore-lint -dstg-lint`!
- Intrinsically-typed `progress` (`foreach (m :: Term 'CEmpty a) -> Progress m`)
  is marked `[WIP NOTICE]` as an R03 milestone blocker (retained quantification
  and refinement over indexed GADT domains).
