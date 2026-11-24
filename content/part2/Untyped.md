---
title: "Untyped: Untyped lambda calculus with full normalisation"
prev: /Inference/
next: /Status/
src: content/part2/Untyped.md
module: PLFH.Part2.Untyped
plfaChapter: https://plfa.inf.ed.ac.uk/19.08/Untyped/
---

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
module PLFH.Part2.Untyped
  ( Fin (..)
  , UTerm (..)
  , extU
  , renameU
  , extsU
  , substU
  , substSingleU
  , Neutral (..)
  , Normal (..)
  , BetaStep (..)
  , BetaSteps (..)
  , idTerm
  , idIsNormal
  , omegaTerm
  ) where

import Data.Kind (Type)
import HaskLib.Size (Size (..))
```

In PLFA's **Untyped** chapter, the simply-typed calculus is stripped down to
the pure untyped lambda calculus—where every term has the single universal
type, contexts reduce to a natural number `n :: Size` counting variables in
scope, and variables are well-scoped de Bruijn indices `Fin n`.

## Well-scoped de Bruijn indices (`Fin n`) and terms (`UTerm n`)

```haskell
-- | Finite set {0, ..., n-1}: well-scoped de Bruijn variables in depth `n`.
data Fin (n :: Size) where
  FZ :: Fin ('Succ n)
  FS :: Fin n -> Fin ('Succ n)

-- | Well-scoped untyped lambda terms with `n` free variables in scope.
data UTerm (n :: Size) where
  UVar :: Fin n -> UTerm n
  ULam :: UTerm ('Succ n) -> UTerm n
  UApp :: UTerm n -> UTerm n -> UTerm n

-- | Closed identity term: λx. x.
idTerm :: UTerm 'Zero
idTerm = ULam (UVar FZ)

-- | The classic diverging term Ω = (λx. x x) (λx. x x).
omegaTerm :: UTerm 'Zero
omegaTerm = UApp selfApp selfApp
  where
    selfApp :: UTerm 'Zero
    selfApp = ULam (UApp (UVar FZ) (UVar FZ))
```

## Scope-preserving renaming and substitution

```haskell
-- | Lift a variable renaming under a lambda binder.
extU :: (Fin m -> Fin n) -> Fin ('Succ m) -> Fin ('Succ n)
extU _   FZ     = FZ
extU rho (FS x) = FS (rho x)

-- | Simultaneous renaming on well-scoped untyped terms.
renameU :: (Fin m -> Fin n) -> UTerm m -> UTerm n
renameU rho (UVar x)   = UVar (rho x)
renameU rho (ULam b)   = ULam (renameU (extU rho) b)
renameU rho (UApp l m) = UApp (renameU rho l) (renameU rho m)

-- | Lift a substitution under a lambda binder.
extsU :: (Fin m -> UTerm n) -> Fin ('Succ m) -> UTerm ('Succ n)
extsU _     FZ     = UVar FZ
extsU sigma (FS x) = renameU FS (sigma x)

-- | Simultaneous capture-avoiding substitution on well-scoped untyped terms.
substU :: (Fin m -> UTerm n) -> UTerm m -> UTerm n
substU sigma (UVar x)   = sigma x
substU sigma (ULam b)   = ULam (substU (extsU sigma) b)
substU sigma (UApp l m) = UApp (substU sigma l) (substU sigma m)

-- | Single-variable substitution `b [ w ]`.
substSingleU :: UTerm ('Succ n) -> UTerm n -> UTerm n
substSingleU b w = substU (\case { FZ -> w; FS x -> UVar x }) b
```

## Neutral forms, Normal forms, and Full β-Reduction (Promoted GADT!)

Just as in [DeBruijn](/DeBruijn/), GHC accepts **promoting the indexed GADT
`UTerm n`** to index `Neutral`, `Normal`, `BetaStep` (calling ordinary
`substSingleU` directly in `Beta`!), and `BetaSteps`:

```haskell
-- | Neutral terms: a variable applied to zero or more normal arguments.
type Neutral :: forall (n :: Size). UTerm n -> Type
data Neutral t where
  NVar :: Neutral ('UVar x)
  NApp :: Neutral l -> Normal m -> Neutral ('UApp l m)

-- | Normal forms under full β-reduction (no β-redexes anywhere).
type Normal :: forall (n :: Size). UTerm n -> Type
data Normal t where
  NNeu :: Neutral t -> Normal t
  NLam :: Normal b  -> Normal ('ULam b)

-- | Full β-reduction (including under lambdas and in neutral arguments).
type BetaStep :: forall (n :: Size). UTerm n -> UTerm n -> Type
data BetaStep t t' where
  XiApp1 :: BetaStep l l' -> BetaStep ('UApp l m) ('UApp l' m)
  XiApp2 :: BetaStep m m' -> BetaStep ('UApp l m) ('UApp l m')
  XiLam  :: BetaStep b b' -> BetaStep ('ULam b) ('ULam b')
  Beta   :: BetaStep ('UApp ('ULam b) w) (substSingleU b w)

-- | Multi-step full β-reduction.
type BetaSteps :: forall (n :: Size). UTerm n -> UTerm n -> Type
data BetaSteps t t' where
  BRefl :: BetaSteps t t
  BCons :: BetaStep s t -> BetaSteps t u -> BetaSteps s u

-- | Evidence that λx. x is in full normal form!
idIsNormal :: Normal ('ULam ('UVar 'FZ) :: UTerm 'Zero)
idIsNormal = NLam (NNeu NVar)
```

<div class="wip-notice">
<strong>[WIP NOTICE — Gas-bounded normalizer over promoted <code>UTerm n</code> (R03)]</strong>
Writing PLFA's gas-bounded full β-normalizer
<code>eval :: Gas -&gt; foreach (t :: UTerm n) -&gt; Steps t</code> hits the
same R03 indexed-GADT <code>foreach</code> boundary documented in
<a href="/DeBruijn/">DeBruijn</a>
(<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R03_ForEachGadtEquations.hs"><code>R03_ForEachGadtEquations.hs</code></a>).
All well-scoped syntax, renaming, substitution, and promoted
<code>Neutral</code>/<code>Normal</code>/<code>BetaStep</code> relations
compile cleanly with <code>-dcore-lint -dstg-lint</code>.
</div>

## Changes from PLFA `v19.08`

- Adapted from [Untyped (v19.08)](https://plfa.inf.ed.ac.uk/19.08/Untyped/)
  ([source](https://github.com/plfa/plfa.github.io/blob/63fcbbe25ec3686ff4c6df2c5b58a96b3a2054f3/src/plfa/part2/Untyped.lagda.md)).
- Checked direct ports of `Fin`, `UTerm`, `extU`, `renameU`, `extsU`,
  `substU`, `substSingleU`, `Neutral`, `Normal`, `BetaStep`, `BetaSteps`,
  `idIsNormal`, and `omegaTerm`.
- Marked gas-bounded normalization over `foreach (t :: UTerm n)` with
  `[WIP NOTICE]` (same R03 indexed-GADT domain boundary as `DeBruijn`).
