---
title: "Adequacy: Adequacy of denotational semantics with respect to operational semantics"
prev: /Soundness/
next: /ContextualEquivalence/
src: content/part3/Adequacy.md
module: PLFH.Part3.Adequacy
plfaChapter: https://plfa.inf.ed.ac.uk/22.08/Adequacy/
plfaEdition: "PLFA v22.08"
plfaAuthors: "Philip Wadler, Wen Kokke, and Jeremy G. Siek"
---

```haskell
{-# LANGUAGE AllowAmbiguousTypes, DataKinds, EmptyCase, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, PolyKinds, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures, TypeApplications, TypeFamilies #-}
{-# LANGUAGE TypeOperators, UndecidableInstances #-}
module PLFH.Part3.Adequacy
  ( AboveFun (..)
  , aboveFunArr
  , aboveFunJoinL
  , aboveFunJoinR
  , aboveFunSub
  , notAboveFunBot
  , aboveFunJoin
  , notAboveFunJoin
  , notAboveFunJoinInv
  , decAboveFun
  , WHNF (..)
  , HaltsV (..)
  , LogE
  , LogArr (..)
  , LogV
  , logVBotLam
  , logVJoinLam
  , notAboveFunLogV
  ) where

import Data.Kind (Type)
import Data.Void (Void, absurd)
import HaskLib.Nat (Nat (..))
import PLFH.Part1.Decidable (Dec (..))
import PLFH.Part1.Negation (Not)
import PLFH.Part2.BigStep (Clos (..), Env (..), EvalBig (..))
import PLFH.Part2.Untyped (UTerm (..))
import PLFH.Part3.Denotational
  ( Factor (..)
  , SomeArrMem (..)
  , Sub (..)
  , ValMem (..)
  , Value (..)
  , allFunsMem
  , memToSub
  , subInv
  )
```

In PLFA's **Adequacy** chapter, we connect the denotational semantics back to
call-by-name operational evaluation ([BigStep](/BigStep/)): whenever a term
has a non-trivial function denotation (`AboveFun`), it halts at a lambda
abstraction.

## Being greater than or equal to a function (`AboveFun`) and its decidability

Using our checked **`subInv`** theorem from [Denotational](/Denotational/),
**every single property of `AboveFun`**—including `notAboveFunBot`,
`aboveFunJoin`, and the **decision procedure `decAboveFun`**—compiles directly
with `-dcore-lint -dstg-lint`!

```haskell
-- | Evidence that value `u` is at least some function entry `v ↦ w`.
data AboveFun (u :: Value) where
  MkAboveFun :: Sub ('Arr v w) u -> AboveFun u

aboveFunArr :: AboveFun ('Arr v w)
aboveFunArr = MkAboveFun SubRefl

aboveFunJoinL :: AboveFun a -> AboveFun ('Join a b)
aboveFunJoinL (MkAboveFun lt) = MkAboveFun (SubJoinR1 lt)

aboveFunJoinR :: AboveFun b -> AboveFun ('Join a b)
aboveFunJoinR (MkAboveFun lt) = MkAboveFun (SubJoinR2 lt)

aboveFunFromMem :: ValMem ('Arr v w) u -> AboveFun u
aboveFunFromMem m = MkAboveFun (memToSub m)

-- | Upward closure of `AboveFun` under `Sub` (`above-fun-⊑`).
aboveFunSub :: foreach (u :: Value) -> AboveFun u -> Sub u u' -> AboveFun u'
aboveFunSub u (MkAboveFun lt') lt = MkAboveFun (SubTrans u lt' lt)

-- | Bottom is never above a function (`above-fun⊥`), proved via `subInv`!
notAboveFunBot :: Not (AboveFun 'Bot)
notAboveFunBot (MkAboveFun lt) = case subInv Bot lt MemArr of
  MkFactor u2 f s _ _ -> case allFunsMem u2 f of
    MkSomeArrMem _ _ m -> case s m of {}

-- | If `u ⊔ u'` is above a function, then `u` or `u'` is (`above-fun-⊔`).
aboveFunJoin :: foreach (u :: Value) -> foreach (u' :: Value)
             -> AboveFun ('Join u u') -> Either (AboveFun u) (AboveFun u')
aboveFunJoin u u' (MkAboveFun lt) = case subInv (Join u u') lt MemArr of
  MkFactor g f s _ _ -> case allFunsMem g f of
    MkSomeArrMem _ _ m -> case s m of
      MemJoinL x -> Left  (aboveFunFromMem x)
      MemJoinR y -> Right (aboveFunFromMem y)

-- | If neither `u` nor `u'` is above a function, neither is their join.
notAboveFunJoin :: foreach (u :: Value) -> foreach (u' :: Value)
                -> Not (AboveFun u) -> Not (AboveFun u') -> Not (AboveFun ('Join u u'))
notAboveFunJoin u u' nu nu' af = case aboveFunJoin u u' af of
  Left  au  -> nu au
  Right au' -> nu' au'

-- | Converse: if `u ⊔ u'` is not above a function, neither component is.
notAboveFunJoinInv :: Not (AboveFun ('Join u u')) -> (Not (AboveFun u), Not (AboveFun u'))
notAboveFunJoinInv n = (\af -> n (aboveFunJoinL af), \af -> n (aboveFunJoinR af))

-- | Decision procedure for `AboveFun` (`above-fun?`)!
decAboveFun :: foreach (v :: Value) -> Dec (AboveFun v)
decAboveFun Bot        = No notAboveFunBot
decAboveFun (Arr _ _)  = Yes aboveFunArr
decAboveFun (Join a b) = case (decAboveFun a, decAboveFun b) of
  (Yes af, _)    -> Yes (aboveFunJoinL af)
  (_, Yes af)    -> Yes (aboveFunJoinR af)
  (No na, No nb) -> No (notAboveFunJoin a b na nb)
```

## The step-indexed / value-indexed logical relation (`LogV`, `LogE`)

In PLFA, the logical relation `𝕍 : Value → Clos → Set` cannot be defined as an
inductive datatype because `𝔼` appears in a **negative position** in the
`v ↦ w` clause. Instead, it is defined by **large elimination** (structural
recursion on `Value` returning `Type`). In Dependent Haskell, a closed
`type family` over promoted `Value` and `Clos` (with `newtype LogArr` wrapping
the higher-rank `forall c`) encodes `LogV` and `LogE` directly!

```haskell
-- | Weak-head normal form: a lambda abstraction.
type WHNF :: forall (n :: Nat). UTerm n -> Type
data WHNF m where
  WLam :: WHNF ('ULam b)

-- | Witness that evaluating `m` in `e` halts at a closure related to `v` by `LogV`.
type HaltsV :: forall (n :: Nat). Env n -> UTerm n -> Value -> Type
data HaltsV e m v where
  MkHaltsV :: EvalBig e m c' -> LogV v c' -> HaltsV e m v

-- | Expression logical relation `𝔼`: if `v` is above a function, `c` halts in `LogV`.
type LogE :: Value -> Clos -> Type
type family LogE v c where
  LogE v ('MkClos m e) = AboveFun v -> HaltsV e m v

-- | Wrapper for the impredicative `forall c` in the `Arr` clause of `LogV`.
newtype LogArr (v :: Value) (w :: Value) (e :: Env n) (b :: UTerm ('Succ n)) =
  MkLogArr { runLogArr :: forall (c :: Clos). LogE v c -> AboveFun w -> HaltsV ('ECons c e) b w }

-- | Value logical relation `𝕍` defined by recursion on `Value` and `Clos`!
type LogV :: Value -> Clos -> Type
type family LogV v c where
  LogV v ('MkClos ('UVar x) e)           = Void
  LogV v ('MkClos ('UApp l m) e)         = Void
  LogV 'Bot ('MkClos ('ULam b) e)        = ()
  LogV ('Arr v w) ('MkClos ('ULam b) e)  = LogArr v w e b
  LogV ('Join u v) ('MkClos ('ULam b) e) =
    (LogV u ('MkClos ('ULam b) e), LogV v ('MkClos ('ULam b) e))

-- | `Bot` relates trivially to every lambda closure.
logVBotLam :: LogV 'Bot ('MkClos ('ULam b) e)
logVBotLam = ()

-- | Join introduction for `LogV` on lambda closures.
logVJoinLam :: LogV u ('MkClos ('ULam b) e) -> LogV v ('MkClos ('ULam b) e)
            -> LogV ('Join u v) ('MkClos ('ULam b) e)
logVJoinLam u v = (u, v)

-- | Any value not above a function relates trivially to every lambda closure (`not-above-fun-𝕍`).
notAboveFunLogV :: forall (n :: Nat) (b :: UTerm ('Succ n)) (e :: Env n).
                   foreach (v :: Value) -> Not (AboveFun v) -> LogV v ('MkClos ('ULam b) e)
notAboveFunLogV Bot        _  = ()
notAboveFunLogV (Arr _ _)  na = absurd (na aboveFunArr)
notAboveFunLogV (Join a b) na =
  ( notAboveFunLogV @n @b @e a (\af -> na (aboveFunJoinL af))
  , notAboveFunLogV @n @b @e b (\af -> na (aboveFunJoinR af)) )
```

<div class="wip-notice">
<strong>[WIP NOTICE — Subsumption (<code>sub-𝕍</code>/<code>sub-𝔼</code>) &amp; Fundamental Lemma (R03/R11)]</strong>
Finishing PLFA's <code>sub-𝕍</code> (specifically the <code>SubDist</code>
branch) and the fundamental lemma of the logical relation requires:
<ul>
  <li><strong>R11:</strong> Determinism of call-by-name big-step evaluation
      (<code>evalDeterm</code> in <a href="/BigStep/">BigStep</a>), which hits
      the Desugar Core Lint bug
      <a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R11_MixedKindCoercionCoreLint.hs"><code>R11_MixedKindCoercionCoreLint.hs</code></a>
      on GHC <code>d15cbd41fe</code> (already fixed on private candidate
      <code>f21ab22285</code> / <code>d033d0132d</code>!).</li>
  <li><strong>R03:</strong> Case analysis on the promoted <code>UTerm n</code>
      inside <code>Clos</code> in <code>𝕍→WHNF</code> and <code>sub-𝕍</code>
      (<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R03_ForEachGadtEquations.hs"><code>R03_ForEachGadtEquations.hs</code></a>).</li>
</ul>
</div>

## Changes from PLFA `v22.08`

- Adapted from [Adequacy (v22.08)](https://plfa.inf.ed.ac.uk/22.08/Adequacy/)
  ([source](https://github.com/plfa/plfa.github.io/blob/e2d545f3df0db4d4206c5448735665abde02d81f/src/plfa/part3/Adequacy.lagda.md))
  by Philip Wadler, Wen Kokke, and Jeremy G. Siek (CC BY 4.0).
- Checked direct ports of `AboveFun`, `aboveFunSub`, **`notAboveFunBot`**,
  **`aboveFunJoin`**, `notAboveFunJoin`, `notAboveFunJoinInv`,
  **`decAboveFun`**, `WHNF`, `HaltsV`, `LogE`, `LogArr`, `LogV`, `logVBotLam`,
  `logVJoinLam`, and **`notAboveFunLogV`**.
- Marked `sub-𝕍`/`sub-𝔼` and the fundamental lemma with `[WIP NOTICE]`
  referencing `R11_MixedKindCoercionCoreLint.hs` and `R03_ForEachGadtEquations.hs`.
