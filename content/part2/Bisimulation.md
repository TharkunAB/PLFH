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
  , simValue
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

-- | General value preservation across promoted GADT indices (`~-val`).
simValue :: SimRel m m' -> Value m -> Value m'
simValue SimRefl         v           = v
simValue (SimLam _)      VLam        = VLam
simValue (SimPair s1 s2) (VPair v w) = VPair (simValue s1 v) (simValue s2 w)
```

<div class="note-box">
<strong>Fixed Core Lint bug (<code>692eae0778</code> / <code>9cc4065fab</code>):</strong>
On earlier GHC baselines (<code>d15cbd41fe</code>–<code>1a02a866e7</code>),
general <code>simValue</code> typechecked and then failed Desugar Core Lint with
<code>R11 mixed-kind coercion binder</code> when matching two GADTs indexed by
promoted <code>Term g a</code>. Fixed on <code>dependent-haskell</code> and
tracked as regression check
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/fixed/R11_MixedKindCoercionCoreLint.hs"><code>reproducers/fixed/R11_MixedKindCoercionCoreLint.hs</code></a>!
</div>

## Changes from PLFA

- Adapted from [Bisimulation](https://plfa.inf.ed.ac.uk/Bisimulation/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/Bisimulation.lagda.md)).
- `SimRel`, `Leg` (parameterized cleanly over any reduction relation `step`),
  `simValueLam`, and full **`simValue`** all compile with `-dcore-lint -dstg-lint`!
- Full `sim` waits on checked functional `Step` for extended STLC in [More](/More/).
