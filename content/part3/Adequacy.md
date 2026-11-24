---
title: "Adequacy: Adequacy of denotational semantics with respect to operational semantics"
prev: /Soundness/
next: /ContextualEquivalence/
src: content/part3/Adequacy.md
module: PLFH.Part3.Adequacy
plfaChapter: https://plfa.inf.ed.ac.uk/Adequacy/
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
  , LogVLam
  , logVBotLam
  , logVJoinLam
  , notAboveFunLogV
  , haltsVJoin
  , subLogVLam
  , subLogE
  , EnvLogHit (..)
  , EnvLog
  , envLogNil
  , envLogCons
  , fundamental
  , HaltsBig (..)
  , adequacyBigStep
  , adequacyIdApp
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void, absurd)
import HaskLib.Nat (Nat (..))
import PLFH.Part1.Decidable (Dec (..))
import PLFH.Part1.Negation (Not)
import PLFH.Part2.BigStep (Clos (..), Env (..), EnvLookup (..), EvalBig (..), evalDeterm)
import PLFH.Part2.Untyped (Fin (..), UTerm (..))
import PLFH.Part3.Denotational
  ( Denotes (..)
  , Factor (..)
  , SomeArrMem (..)
  , Sub (..)
  , ValEnv (..)
  , ValLookup (..)
  , ValMem (..)
  , ValW (..)
  , Value (..)
  , allFunsMem
  , denotIdAppId
  , memToSub
  , subInv
  , unArrW
  , unJoinW
  )
```

In PLFA's **Adequacy** chapter, we connect the denotational semantics back to
call-by-name operational evaluation ([BigStep](/BigStep/)): whenever a closed
term has a non-trivial function denotation (`AboveFun`), it halts at a lambda
abstraction!

With `BigStep.evalDeterm` now proved unconditionally on published GHC
`9cc4065fab`, the **entire Big-Step Adequacy theorem**—`decAboveFun`, the
negative-position logical relation `LogVLam`/`LogE`, **full subsumption across
all 8 `Sub` constructors (`subLogVLam` and `subLogE`, including `SubDist`!)**,
the **complete Fundamental Lemma (`fundamental`, all 6 `Denotes` rules!)**, and
**unconditional Big-Step Adequacy (`adequacyBigStep`)**—compiles directly with
`-dcore-lint -dstg-lint` and executes at runtime!

## Being greater than or equal to a function (`AboveFun`) and its decidability

Using our checked **`subInv`** theorem from [Denotational](/Denotational/),
every property of `AboveFun`—including `notAboveFunBot`, `aboveFunJoin`, and
the decision procedure `decAboveFun`—compiles directly:

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

## The value-indexed logical relation (`LogVLam`, `LogE`) and Subsumption (`sub-𝕍`, `sub-𝔼`)

In PLFA, the logical relation `𝕍` cannot be defined as an inductive datatype
because `𝔼` appears in a **negative position** in the `v ↦ w` clause. Instead,
it is defined by **large elimination** on `Value` (`LogVLam`, a 3-line closed
type family over promoted `Value`, paired with `newtype LogArr` wrapping the
impredicative `forall k d m`). Because every call-by-name big-step evaluation
terminates at a lambda closure (`evalBigIsLam` in [BigStep](/BigStep/)),
`HaltsV` directly packages `EvalBig e m ('MkClos ('ULam b) d)` with
`LogVLam v d b`:

```haskell
-- | Weak-head normal form: a lambda abstraction.
type WHNF :: forall (n :: Nat). UTerm n -> Type
data WHNF m where
  WLam :: WHNF ('ULam b)

-- | Witness that evaluating `m` in `e` halts at a lambda closure related to `v`.
type HaltsV :: forall (n :: Nat). Env n -> UTerm n -> Value -> Type
data HaltsV e m v where
  MkHaltsV :: EvalBig e m ('MkClos ('ULam b) d) -> LogVLam v d b -> HaltsV e m v

-- | Expression logical relation `𝔼`: if `v` is above a function, `(m, e)` halts in `LogVLam`.
type LogE :: forall (k :: Nat). Value -> Env k -> UTerm k -> Type
type LogE v e m = AboveFun v -> HaltsV e m v

-- | Wrapper for the impredicative `forall k d m` in the `Arr` clause of `LogVLam`.
newtype LogArr (v :: Value) (w :: Value) (e :: Env n) (b :: UTerm ('Succ n)) =
  MkLogArr { runLogArr :: forall (k :: Nat) (d :: Env k) (m :: UTerm k).
                          LogE v d m -> AboveFun w -> HaltsV ('ECons ('MkClos m d) e) b w }

-- | Value logical relation `𝕍` on lambda closures, defined by recursion on `Value`!
type LogVLam :: forall (n :: Nat). Value -> Env n -> UTerm ('Succ n) -> Type
type family LogVLam v e b where
  LogVLam 'Bot        e b = ()
  LogVLam ('Arr v w)  e b = LogArr v w e b
  LogVLam ('Join u v) e b = (LogVLam u e b, LogVLam v e b)

logVBotLam :: LogVLam 'Bot e b
logVBotLam = ()

logVJoinLam :: LogVLam u e b -> LogVLam v e b -> LogVLam ('Join u v) e b
logVJoinLam u v = (u, v)

-- | Any value not above a function relates trivially to every lambda closure (`not-above-fun-𝕍`).
notAboveFunLogV :: forall (n :: Nat) (e :: Env n) (b :: UTerm ('Succ n)).
                   foreach (v :: Value) -> Not (AboveFun v) -> LogVLam v e b
notAboveFunLogV Bot        _  = ()
notAboveFunLogV (Arr _ _)  na = absurd (na aboveFunArr)
notAboveFunLogV (Join a c) na =
  ( notAboveFunLogV @n @e @b a (\af -> na (aboveFunJoinL af))
  , notAboveFunLogV @n @e @b c (\af -> na (aboveFunJoinR af)) )

-- | Join introduction for the expression logical relation (`𝔼-⊔`), using
-- `decAboveFun` and our unconditional `BigStep.evalDeterm`!
haltsVJoin :: forall (n :: Nat) (e :: Env n) (m :: UTerm n).
              foreach (w1 :: Value) -> foreach (w2 :: Value)
           -> LogE w1 e m
           -> LogE w2 e m
           -> LogE ('Join w1 w2) e m
haltsVJoin w1 w2 le1 le2 af = case (decAboveFun w1, decAboveFun w2) of
  (Yes af1, Yes af2) -> case (le1 af1, le2 af2) of
    (MkHaltsV ev1 lv1, MkHaltsV ev2 lv2) -> case evalDeterm ev1 ev2 of
      Refl -> MkHaltsV ev1 (lv1, lv2)
  (Yes af1, No na2) -> case le1 af1 of
    MkHaltsV (ev1 :: EvalBig e m ('MkClos ('ULam b) (d :: Env k))) lv1 ->
      MkHaltsV ev1 (lv1, notAboveFunLogV @k @d @b w2 na2)
  (No na1, Yes af2) -> case le2 af2 of
    MkHaltsV (ev2 :: EvalBig e m ('MkClos ('ULam b) (d :: Env k))) lv2 ->
      MkHaltsV ev2 (notAboveFunLogV @k @d @b w1 na1, lv2)
  (No na1, No na2) -> absurd (notAboveFunJoin w1 w2 na1 na2 af)

subDistHelper :: forall (n :: Nat) (e :: Env n) (b :: UTerm ('Succ n))
                        (a :: Value) (w1 :: Value) (w2 :: Value).
                 ValW w1 -> ValW w2
              -> (LogArr a w1 e b, LogArr a w2 e b)
              -> LogArr a ('Join w1 w2) e b
subDistHelper (MkValW w1) (MkValW w2) (f1, f2) =
  MkLogArr (\le af -> haltsVJoin w1 w2 (runLogArr f1 le) (runLogArr f2 le) af)

-- | Full unconditional downward closure of `LogVLam` under all 8 rules of `Sub` (`sub-𝕍`)!
subLogVLam :: forall (n :: Nat) (e :: Env n) (b :: UTerm ('Succ n)) (u :: Value) (v :: Value).
              ValW u -> ValW v
           -> Sub u v
           -> LogVLam v e b
           -> LogVLam u e b
subLogVLam _  _  SubBot             _  = ()
subLogVLam _  _  SubRefl            lv = lv
subLogVLam wu wv (SubJoinL l1 l2)   lv = case unJoinW wu of
  (wu1, wu2) -> (subLogVLam @n @e @b wu1 wv l1 lv, subLogVLam @n @e @b wu2 wv l2 lv)
subLogVLam wu wv (SubJoinR1 l1)     lv = case unJoinW wv of
  (wv1, _) -> subLogVLam @n @e @b wu wv1 l1 (fst lv)
subLogVLam wu wv (SubJoinR2 l2)     lv = case unJoinW wv of
  (_, wv2) -> subLogVLam @n @e @b wu wv2 l2 (snd lv)
subLogVLam wu wv (SubTrans mid l1 l2) lv = go (MkValW mid) l1 l2 lv
  where
    go :: forall (m :: Value). ValW m -> Sub u m -> Sub m v -> LogVLam v e b -> LogVLam u e b
    go wMid s1 s2 x =
      subLogVLam @n @e @b @u @m wu wMid s1 (subLogVLam @n @e @b @m @v wMid wv s2 x)
subLogVLam wu wv (SubArr l1 l2)     lv = case (unArrW wu, unArrW wv) of
  ((wu1, wu2), (wv1, wv2)) ->
    MkLogArr (\le -> subLogE wu2 wv2 l2 (runLogArr lv (subLogE wv1 wu1 l1 le)))
subLogVLam wu _  SubDist            lv = case unArrW wu of
  (_, wJoin) -> case unJoinW wJoin of
    (ww1, ww2) -> subDistHelper @n @e @b ww1 ww2 lv

-- | Full unconditional downward closure of `LogE` under `Sub` (`sub-𝔼`)!
subLogE :: forall (n :: Nat) (e :: Env n) (m :: UTerm n) (u :: Value) (v :: Value).
           ValW u -> ValW v
        -> Sub u v
        -> LogE v e m
        -> LogE u e m
subLogE wu@(MkValW u) wv lt le af = case le (aboveFunSub u af lt) of
  MkHaltsV (ev :: EvalBig e m ('MkClos ('ULam b) (d :: Env k))) lv ->
    MkHaltsV ev (subLogVLam @k @d @b wu wv lt lv)
```

## The Fundamental Lemma and Unconditional Big-Step Adequacy!

Every single rule of `Denotes` (`DVar`, `DElim`, `DIntro`, `DBot`, `DJoin`,
`DSub`) checks unconditionally in `fundamental`, yielding unconditional
`adequacyBigStep` and an executable halting derivation `adequacyIdApp`:

```haskell
-- | Pointwise logical relation witness for a variable lookup in `e'`.
data EnvLogHit (e' :: Env n) (x :: Fin n) (v :: Value) where
  MkEnvLogHit :: EnvLookup e' x ('MkClos m' d') -> LogE v d' m' -> EnvLogHit e' x v

-- | Environment logical relation (`𝒢`): every variable value in `e` is
-- logically related to its closure in `e'`.
type EnvLog (e' :: Env n) (e :: ValEnv n) =
  forall (x :: Fin n) (v :: Value). ValLookup e x v -> EnvLogHit e' x v

envLogNil :: EnvLog 'ENil 'VNil
envLogNil lk = case lk of {}

envLogCons :: LogE v d' m' -> EnvLog e' e -> EnvLog ('ECons ('MkClos m' d') e') ('VCons e v)
envLogCons le _  VLZ      = MkEnvLogHit ELZ le
envLogCons _  el (VLS lk) = case el lk of
  MkEnvLogHit envLk le' -> MkEnvLogHit (ELS envLk) le'

-- | Unconditional Fundamental Lemma of the logical relation:
-- if `e ⊢ m ↓ v` and `e' 𝒢 e`, then `v 𝔼 (m, e')`!
fundamental :: forall (n :: Nat) (e' :: Env n) (e :: ValEnv n) (m :: UTerm n) (v :: Value).
               ValW v
            -> EnvLog e' e
            -> Denotes e m v
            -> LogE v e' m
fundamental _  el (DVar lk) af = case el lk of
  MkEnvLogHit envLk le -> case le af of
    MkHaltsV ev lv -> MkHaltsV (EVar envLk ev) lv
fundamental (MkValW v) el (DElim wArg@(MkValW vArg) d1 d2) af =
  case fundamental (MkValW (Arr vArg v)) el d1 aboveFunArr of
    MkHaltsV evL lvL -> case runLogArr lvL (fundamental wArg el d2) af of
      MkHaltsV evB lvB -> MkHaltsV (EApp evL evB) lvB
fundamental wv el (DIntro dBody) _ = case unArrW wv of
  (_, wv2) -> MkHaltsV ELam (MkLogArr (\le -> fundamental wv2 (envLogCons le el) dBody))
fundamental _  _  DBot af = absurd (notAboveFunBot af)
fundamental _  el (DJoin w1@(MkValW v1) w2@(MkValW v2) d1 d2) af =
  haltsVJoin v1 v2 (fundamental w1 el d1) (fundamental w2 el d2) af
fundamental wv el (DSub wSuper d1 lt) af =
  subLogE wv wSuper lt (fundamental wSuper el d1) af

-- | Big-step termination witness: `(m, e)` evaluates to some lambda closure.
data HaltsBig (e :: Env n) (m :: UTerm n) where
  MkHaltsBig :: EvalBig e m ('MkClos ('ULam b) d) -> HaltsBig e m

-- | Unconditional Big-Step Adequacy theorem (`adequacy`):
-- every closed term with a non-trivial function denotation halts at a lambda!
adequacyBigStep :: ValW v -> Denotes 'VNil m v -> AboveFun v -> HaltsBig 'ENil m
adequacyBigStep wv d af = case fundamental wv envLogNil d af of
  MkHaltsV ev _ -> MkHaltsBig ev

-- | Concrete execution of adequacy: `[] ⊢ id · id ↓ ⊥ ↦ ⊥` produces a real
-- call-by-name halting derivation for `(λx. x) (λx. x)`!
adequacyIdApp :: HaltsBig 'ENil ('UApp ('ULam ('UVar 'FZ)) ('ULam ('UVar 'FZ)))
adequacyIdApp =
  adequacyBigStep (MkValW (Arr Bot Bot)) (denotIdAppId (MkValW Bot)) aboveFunArr
```

<div class="wip-notice">
<strong>[WIP NOTICE — <code>foreach</code> + Type-Family Rewriting Bug (R03) &amp; Big-Step → Small-Step Bridge]</strong>
<ul>
  <li><strong>Discharged on <code>9cc4065fab</code>:</strong> <code>EvalDeterm</code>
      is now proved unconditionally as <code>BigStep.evalDeterm</code>
      (<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/fixed/R11_MixedKindCoercionCoreLint.hs"><code>reproducers/fixed/R11_MixedKindCoercionCoreLint.hs</code></a>),
      making <code>subLogVLam</code>, <code>fundamental</code>, and
      <code>adequacyBigStep</code> 100% unconditional!</li>
  <li><strong>Open compiler bug uncovered while writing <code>subLogVLam</code>:</strong>
      Matching a GADT equality (<code>u :~: v</code> or <code>u :~: 'Zero</code>)
      under a retained <code>foreach (u :: Nat)</code> binder fails to rewrite
      a closed type family <code>F u</code> (<code>GHC-05617</code>:
      <em>Could not deduce <code>F v1 ~ F u2</code> from the context
      <code>v1 ~ u2</code></em>!), whereas erased <code>forall</code> succeeds.
      Matching <code>Sub</code> before unpacking <code>ValW</code> kept
      <code>subLogVLam</code> completely clean. See minimal reproducer
      <a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R03_ForEachGadtEqTypeFamily.hs"><code>R03_ForEachGadtEqTypeFamily.hs</code></a>.</li>
  <li><strong>Big-step → Small-step bridge:</strong> Relating
      <code>HaltsBig</code> back to multi-step full β-reduction
      (<code>BetaSteps m ('ULam b)</code>) waits on R03/R13 substitution
      lemmas for closing closures.</li>
</ul>
</div>

## Changes from PLFA

- Adapted from [Adequacy](https://plfa.inf.ed.ac.uk/Adequacy/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part3/Adequacy.lagda.md))
  by Philip Wadler, Wen Kokke, and Jeremy G. Siek (CC BY 4.0).
- Checked direct ports of `AboveFun`, `aboveFunSub`, **`notAboveFunBot`**,
  **`aboveFunJoin`**, `notAboveFunJoin`, `notAboveFunJoinInv`,
  **`decAboveFun`**, `WHNF`, `HaltsV`, `LogE`, `LogArr`, `LogVLam`,
  `notAboveFunLogV`, **`haltsVJoin`**, **`subLogVLam`** (all 8 `Sub` rules!),
  **`subLogE`**, **`fundamental`** (all 6 `Denotes` rules!),
  **unconditional `adequacyBigStep`** (via `BigStep.evalDeterm`), and
  executable `adequacyIdApp`!
- Uncovered and reported a minimal R03 compiler bug:
  `reproducers/R03_ForEachGadtEqTypeFamily.hs`.
