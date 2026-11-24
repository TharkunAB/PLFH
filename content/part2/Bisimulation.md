---
title: "Bisimulation: Relating reduction systems"
prev: /More/
next: /BigStep/
src: content/part2/Bisimulation.md
module: PLFH.Part2.Bisimulation
plfaChapter: https://plfa.inf.ed.ac.uk/Bisimulation/
---

Suppose you have two slightly different operational semantics—or a source
language with syntactic sugar (like `let x = M in N`) and a core language into
which it translates (`(λ x. N) M`). How do you prove that the two languages
**behave identically**?

The classic tool from concurrency theory and programming-language metatheory
(introduced by David Park and Robin Milner) is **simulation** and
**bisimulation**. Given a relation `M ~ M'` connecting states of the first
system to states of the second:

```text
    M  ~  M'
    |     :
    v     v
    N  ~  N'
```

- `~` is a **lock-step simulation** if whenever `M ~ M'` and `M —→ N`, there
  exists `N'` such that `M' —→ N'` and `N ~ N'` (and values correspond to
  values!).
- `~` is a **weak simulation** if one step `M —→ N` is matched by zero or more
  steps `M' —↠ N'`.
- `~` is a **bisimulation** if *both* `~` and its converse are simulations—so
  neither system can take a step or reach a value that the other cannot match!

In PLFA's **Bisimulation** chapter, we define a structural simulation relation
`SimRel` (`_~_`) over our promoted intrinsically-typed extended STLC terms from
[More](/More/), define the existential simulation leg `Leg`, and prove that
simulation preserves values (`simValue`) across promoted GADT indices.

## Imports

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
module PLFH.Part2.Bisimulation
  ( SimRel (..)
  , Leg (..)
  , simSym
  , simTrans
  , simValueLam
  , simValue
  ) where

import Data.Kind (Type)
import PLFH.Part2.More (Ctx (..), Term (..), Ty (..), Value (..))
```

## Simulation relation (`_~_`), simulation legs (`Leg`), and value preservation (`~-val`)

Notice how `Leg` is parameterized directly by any reduction relation
`step :: Term g a -> Term g a -> Type` (whether one-step `Step` for lock-step
simulation or multi-step `Steps` for weak simulation!): `MkLeg s rel` packages
the existential target term `n'` together with the matching step `step m' n'`
and the restored relation `SimRel n n'`.

And look at **`simValue :: SimRel m m' -> Value m -> Value m'`**—matching
simultaneously on two GADTs (`SimRel` and `Value`) both indexed by the
*promoted indexed GADT* `Term g a`, checking directly with `-dcore-lint -dstg-lint`!

```haskell
-- | Structural simulation relation over promoted extended STLC terms.
type SimRel :: forall (g :: Ctx) (a :: Ty). Term g a -> Term g a -> Type
data SimRel m m' where
  SimRefl :: SimRel m m
  SimLam  :: SimRel n n' -> SimRel (Lam n) (Lam n')
  SimApp  :: SimRel l l' -> SimRel m m' -> SimRel (App l m) (App l' m')
  SimPair :: SimRel m m' -> SimRel n n' -> SimRel (Pair m n) (Pair m' n')

-- | One leg of a simulation diagram for an arbitrary reduction relation `step`:
-- `m'` steps to some `n'` with `n ~ n'`.
type Leg :: forall (g :: Ctx) (a :: Ty). (Term g a -> Term g a -> Type) -> Term g a -> Term g a -> Type
data Leg step m' n where
  MkLeg :: step m' n' -> SimRel n n' -> Leg step m' n

-- | Symmetry of `SimRel`: `m ~ m'` implies `m' ~ m` (making `SimRel` a bisimulation relation!).
simSym :: SimRel m m' -> SimRel m' m
simSym SimRefl         = SimRefl
simSym (SimLam s)      = SimLam (simSym s)
simSym (SimApp s1 s2)  = SimApp (simSym s1) (simSym s2)
simSym (SimPair s1 s2) = SimPair (simSym s1) (simSym s2)

-- | Transitivity of `SimRel`: `l ~ m` and `m ~ n` implies `l ~ n`.
simTrans :: SimRel l m -> SimRel m n -> SimRel l n
simTrans SimRefl         s               = s
simTrans s               SimRefl         = s
simTrans (SimLam s1)     (SimLam s2)     = SimLam (simTrans s1 s2)
simTrans (SimApp l1 m1)  (SimApp l2 m2)  = SimApp (simTrans l1 l2) (simTrans m1 m2)
simTrans (SimPair m1 n1) (SimPair m2 n2) = SimPair (simTrans m1 m2) (simTrans n1 n2)

-- | Simulation preserves lambda values cleanly.
simValueLam :: SimRel (Lam n) (Lam n') -> Value (Lam n) -> Value (Lam n')
simValueLam _ VLam = VLam

-- | General value preservation across promoted GADT indices (`~-val`).
simValue :: SimRel m m' -> Value m -> Value m'
simValue SimRefl         v           = v
simValue (SimLam _)      VLam        = VLam
simValue (SimPair s1 s2) (VPair v w) = VPair (simValue s1 v) (simValue s2 w)
```

## Exercises

#### Exercise `sim-sym` (practice)

Prove that `SimRel` is symmetric (`simSym :: SimRel m m' -> SimRel m' m`) and
hence that `simValue` works in *both* directions (making `SimRel` value-preserving
as a bisimulation!).

#### Exercise `sim-trans` (practice)

Prove that `SimRel` is transitive (`simTrans :: SimRel l m -> SimRel m n -> SimRel l n`),
observing how `SimRefl` handles the base cases cleanly.

#### Exercise `sim-extend` (recommended)

Extend `SimRel` with congruence constructors for `Suc`, `Inl`, `Inr`, and
`Cons`, and extend `simValue` to handle `VSuc`, `VInl`, `VInr`, and `VCons`.

## Changes from PLFA

- Adapted from [Bisimulation](https://plfa.inf.ed.ac.uk/Bisimulation/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/Bisimulation.lagda.md)),
  licensed under CC BY 4.0.
- `SimRel`, `Leg` (parameterized cleanly over any reduction relation `step`),
  `simValueLam`, and full `simValue` all compile with `-dcore-lint -dstg-lint`
  and zero promoted-constructor ticks.
- Full step-simulation (`sim`) waits on checked functional `Step` for extended
  STLC in [More](/More/) (`R13_SubstSingleUOpenEq.hs`).
