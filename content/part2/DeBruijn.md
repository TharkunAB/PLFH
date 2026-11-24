---
title: "DeBruijn: Intrinsically-typed de Bruijn representation"
prev: /Properties/
next: /Inference/
src: content/part2/DeBruijn.md
module: PLFH.Part2.DeBruijn
plfaChapter: https://plfa.inf.ed.ac.uk/DeBruijn/
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
  , valZero
  , IsVal (..)
  , checkValue
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

## Promoting `Term g a`: Values

Remarkably, GHC **accepts promoting the indexed GADT `Term g a`**
as the kind of `Value` (using `StandaloneKindSignatures`):

```haskell
-- | Values indexed by promoted intrinsically-typed terms!
type Value :: forall (g :: Ctx) (a :: Ty). Term g a -> Type
data Value m where
  VLam  :: Value ('Lam n)
  VZero :: Value 'Zero
  VSuc  :: Value v -> Value ('Suc v)

-- | Concrete witness that `Zero` is already a value.
valZero :: Value ('Zero :: Term 'CEmpty 'TNat)
valZero = VZero

-- | Classification of a closed intrinsically-typed term as a value or non-value.
type IsVal :: forall (a :: Ty). Term 'CEmpty a -> Type
data IsVal m where
  YesVal :: Value m -> IsVal m
  NotVal :: IsVal m

-- | Case-based value classification over retained intrinsically-typed `Term 'CEmpty a`!
checkValue :: forall (a :: Ty). foreach (m :: Term 'CEmpty a) -> IsVal m
checkValue m = case m of
  Var x      -> case x of {}
  Lam _      -> YesVal VLam
  App _ _    -> NotVal
  Zero       -> YesVal VZero
  Suc n      -> case checkValue n of
    YesVal v -> YesVal (VSuc v)
    NotVal   -> NotVal
  Case _ _ _ -> NotVal
  Mu _       -> NotVal
```

## Intrinsically-typed Reduction (`Step`) and Progress (`progress`)

<div class="wip-notice">
<strong>[WIP NOTICE — Functional <code>Step</code> (R13/R16) &amp; Equation-style <code>foreach</code> on indexed GADTs (R03)]</strong>
Two distinct Dependent Haskell frontiers remain open here:
<ol>
  <li><strong>R13/R16 (Open equations for GADT-indexed higher-order <code>substSingle</code>):</strong>
      Writing qualified <code>Syntax.substSingle</code> in <code>BetaLam</code>/<code>BetaSuc</code>/<code>BetaMu</code>
      still fails with <code>GHC-68947</code>/<code>GHC-70565</code> because
      <code>substSingle</code> calls higher-order GADT-indexed <code>subst</code>.
      See <a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_SubstSingleUOpenEq.hs"><code>R13_SubstSingleUOpenEq.hs</code></a>.</li>
  <li><strong>R03 (Direct equation-style matching on <code>foreach (m :: Term 'CEmpty a)</code>):</strong>
      While <code>case m of</code> now works cleanly (see <code>checkValue</code> above!),
      matching <code>Term 'CEmpty a</code> directly in function equations still hits
      <code>GHC-83605</code>. See
      <a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R03_ForEachGadtEquations.hs"><code>R03_ForEachGadtEquations.hs</code></a>.</li>
</ol>
</div>

## Changes from PLFA

- Adapted from [DeBruijn](https://plfa.inf.ed.ac.uk/DeBruijn/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/DeBruijn.lagda.md)).
- `Ty`, `Ctx`, `Lookup`, `Term`, `ext`, `rename`, `exts`, `subst`,
  `substSingle`, GADT-promoted `Value`, and case-based **`IsVal`/`checkValue`**
  over retained `foreach (m :: Term 'CEmpty a)` all compile cleanly with
  `-dcore-lint -dstg-lint` and pass our `.hi` interface soundness audit!
- Functional `Step` (`substSingle`, R13/R16) and direct equation-style
  `foreach` on indexed GADTs (`R03_ForEachGadtEquations.hs`) remain marked
  `[WIP NOTICE]`.
