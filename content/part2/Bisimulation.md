---
title: "Bisimulation: Relating reduction systems"
prev: /More/
next: /BigStep/
src: content/part2/Bisimulation.md
module: PLFH.Part2.Bisimulation
plfaChapter: https://plfa.inf.ed.ac.uk/Bisimulation/
---

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
module PLFH.Part2.Bisimulation
  ( SimRel (..)
  , Leg (..)
  , simValueLam
  ) where

import Data.Kind (Type)
import PLFH.Part2.More (Ctx (..), Term (..), Ty (..), Value (..))
```

In PLFA's **Bisimulation** chapter, we relate two reduction systems (such as
two variants of product/let operational semantics) by defining a structural
simulation relation `_~_` on intrinsically-typed terms and proving that
values and steps are preserved across the relation (`Leg`, `sim`).

## Simulation relation (`_~_`) and simulation legs (`Leg`)

```haskell
-- | Structural simulation relation over promoted extended STLC terms.
type SimRel :: forall (g :: Ctx) (a :: Ty). Term g a -> Term g a -> Type
data SimRel m m' where
  SimRefl :: SimRel m m
  SimLam  :: SimRel n n' -> SimRel ('Lam n) ('Lam n')
  SimApp  :: SimRel l l' -> SimRel m m' -> SimRel ('App l m) ('App l' m')
  SimPair :: SimRel m m' -> SimRel n n' -> SimRel ('Pair m n) ('Pair m' n')

-- | One leg of a simulation diagram for an arbitrary reduction relation `step`:
-- m' steps to n' with n ~ n'.
type Leg :: forall (g :: Ctx) (a :: Ty). (Term g a -> Term g a -> Type) -> Term g a -> Term g a -> Type
data Leg step m' n where
  MkLeg :: step m' n' -> SimRel n n' -> Leg step m' n

-- | Simulation preserves lambda values cleanly.
simValueLam :: SimRel ('Lam n) ('Lam n') -> Value ('Lam n) -> Value ('Lam n')
simValueLam _ VLam = VLam
```

## Value preservation across promoted GADT indices (R11 Core Lint bug!)

<div class="wip-notice">
<strong>[WIP NOTICE — GHC Core Lint failure in Desugar: R11 mixed-kind coercion binder!]</strong>
Writing the general value-preservation lemma over promoted <code>Term g a</code>:
<pre class="wip"><code>simValue :: SimRel m m' -&gt; Value m -&gt; Value m'
simValue SimRefl         v           = v
simValue (SimLam _)      VLam        = VLam
simValue (SimPair s1 s2) (VPair v w) = VPair (simValue s1 v) (simValue s2 w)</code></pre>
typechecks, but fails <strong>Core Lint immediately after Desugar</strong> on
published GHC <code>1a02a866e7</code> with:
<pre class="wip"><code>*** Core Lint errors : in result of Desugar (before optimization) ***
  R11 mixed-kind coercion binder: 'Pair m n ~# ('Pair (v |&gt; ...) (w |&gt; ...) |&gt; ...)</code></pre>
This directly exercises Serokell card <strong>R11 (Homogeneous equality)</strong>
for GADT pattern matching on promoted indexed GADTs! (Already fixed on the
compiler team's queued 597 candidate.) See minimal reproducer
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R11_MixedKindCoercionCoreLint.hs"><code>reproducers/R11_MixedKindCoercionCoreLint.hs</code></a>.
</div>

## Changes from PLFA

- Adapted from [Bisimulation](https://plfa.inf.ed.ac.uk/Bisimulation/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/Bisimulation.lagda.md)).
- `SimRel`, `Leg` (parameterized cleanly over any reduction relation `step`),
  and `simValueLam` compile with `-dcore-lint -dstg-lint`.
- General `simValue` (and full `sim`) uncovered a real **R11 Core Lint error**
  in GHC's desugarer when matching two GADTs indexed by a promoted GADT (`Term g a`),
  tracked in `R11_MixedKindCoercionCoreLint.hs`.
