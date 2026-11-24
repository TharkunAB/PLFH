---
title: "BigStep: Big-step operational semantics"
prev: /Bisimulation/
next: /Substitution/
src: content/part2/BigStep.md
module: PLFH.Part2.BigStep
plfaChapter: https://plfa.inf.ed.ac.uk/19.08/BigStep/
---

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
module PLFH.Part2.BigStep
  ( Env (..)
  , Clos (..)
  , lookupEnv
  , EvalBig (..)
  , idClos
  , evalIdApp
  ) where

import Data.Kind (Type)
import HaskLib.Size (Size (..))
import PLFH.Part2.Untyped (Fin (..), UTerm (..))
```

In PLFA's **BigStep** chapter, we give a *big-step* (environment-and-closure)
operational semantics for the untyped lambda calculus and study its
relationship to small-step substitution semantics.

## Environments, closures, and environment lookup

An environment `Env n` holds `n` closures (one for each free de Bruijn
variable in scope), and a closure `Clos` packages a captured environment
together with a lambda body:

```haskell
-- | Closure environment matching de Bruijn scope depth `n`.
data Env (n :: Size) where
  ENil  :: Env 'Zero
  ECons :: Clos -> Env n -> Env ('Succ n)

-- | A closure pairing an environment of depth `n` with a lambda body.
data Clos where
  MkClos :: Env n -> UTerm ('Succ n) -> Clos

-- | Runtime lookup of a well-scoped de Bruijn variable in a matching environment.
lookupEnv :: Env n -> Fin n -> Clos
lookupEnv (ECons c _) FZ     = c
lookupEnv (ECons _ e) (FS x) = lookupEnv e x

-- | Closure for the closed identity function λx. x.
idClos :: Clos
idClos = MkClos ENil (UVar FZ)
```

## Big-step evaluation relation (`e ⊢ t ⇓ v`)

We can state `EvalBig` cleanly using a relational lookup `EnvLookup` so the
relation compiles with `-dcore-lint -dstg-lint`, while recording the R13/R16
blocker on calling the ordinary `lookupEnv` function directly in `EVar`:

```haskell
-- | Relational environment lookup: variable `x` maps to closure `c` in `e`.
type EnvLookup :: forall (n :: Size). Env n -> Fin n -> Clos -> Type
data EnvLookup e x c where
  ELZ :: EnvLookup ('ECons c e) 'FZ c
  ELS :: EnvLookup e x c -> EnvLookup ('ECons c' e) ('FS x) c

-- | Big-step evaluation: in environment `e`, term `t` evaluates to closure `v`.
type EvalBig :: forall (n :: Size). Env n -> UTerm n -> Clos -> Type
data EvalBig e t v where
  EVar :: EnvLookup e x c -> EvalBig e ('UVar x) c
  ELam :: EvalBig e ('ULam b) ('MkClos e b)
  EApp :: EvalBig e l ('MkClos e' b)
       -> EvalBig e m v
       -> EvalBig ('ECons v e') b w
       -> EvalBig e ('UApp l m) w

-- | Concrete big-step derivation: (λx. x) (λy. y) ⇓ <[], λy. y>.
evalIdApp :: EvalBig 'ENil
                     ('UApp ('ULam ('UVar 'FZ)) ('ULam ('UVar 'FZ)))
                     ('MkClos 'ENil ('UVar 'FZ))
evalIdApp = EApp ELam ELam (EVar ELZ)
```

<div class="wip-notice">
<strong>[WIP NOTICE — Calling GADT-indexed <code>lookupEnv</code> directly in types (R13/R16)]</strong>
In PLFA, the variable rule calls the function <code>lookupEnv</code> directly
in the constructor type:
<pre class="wip"><code>EVar :: EvalBig e ('UVar x) (lookupEnv e x)</code></pre>
On GHC <code>d15cbd41fe</code>, GHC rejects <code>lookupEnv</code> in types
with <code>GHC-68947</code> (<em>No checked equations are available for
<code>lookupEnv</code> in a type</em>), because <code>lookupEnv</code> matches
two indexed GADT arguments (<code>Env n</code> and <code>Fin n</code>)
simultaneously. See minimal reproducer
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_LookupEnvOpenEq.hs"><code>reproducers/R13_LookupEnvOpenEq.hs</code></a>.
</div>

## Changes from PLFA `v19.08`

- Adapted from [BigStep (v19.08)](https://plfa.inf.ed.ac.uk/19.08/BigStep/)
  ([source](https://github.com/plfa/plfa.github.io/blob/63fcbbe25ec3686ff4c6df2c5b58a96b3a2054f3/src/plfa/part2/BigStep.lagda.md)).
- Checked direct ports of `Env`, `Clos`, `lookupEnv`, `EvalBig`, and
  `evalIdApp` (using relational `EnvLookup` in `EVar`).
- Marked direct functional `lookupEnv e x` inside `EVar` with `[WIP NOTICE]`
  (`R13_LookupEnvOpenEq.hs`, `GHC-68947`).
