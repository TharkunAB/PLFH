---
title: "Adequacy: Adequacy of denotational semantics with respect to operational semantics"
prev: /Soundness/
next: /ContextualEquivalence/
src: content/part3/Adequacy.md
module: PLFH.Part3.Adequacy
plfaChapter: https://plfa.inf.ed.ac.uk/Adequacy/
---

In [Soundness](/Soundness/) we proved that operational reduction preserves
denotations (`M —↠ N` implies `ℰ M ≃ ℰ N`). Notice, however, that Soundness
alone would *also* be satisfied by a completely degenerate semantics that
assigns every term the exact same meaning.

What guarantees that our finite-table semantics truly **distinguishes**
terminating programs from diverging ones? **Computational Adequacy** (Gordon
Plotkin, 1977):

> *Whenever a closed term `M` has a non-trivial function denotation (`AboveFun v`
> with `[] ⊢ M ↓ v`), executing `M` under call-by-name big-step evaluation
> ([BigStep](/BigStep/)) is guaranteed to **halt at a lambda abstraction**.*

## The challenge: a negative-position logical relation

Why can't we prove Adequacy by direct induction on `Denotes`? Because in the
application rule `DElim`, we have `l` evaluating to a lambda `λ b`, and we need
to know that passing argument `m` into `b` *also* halts.

The classic solution is a **value-indexed logical relation** (`𝕍`, `𝔼`, `𝒢`)
defined by structural recursion on the finite `Value` `v`:
- `logVLam Bot e b = type ()`: every lambda closure trivially satisfies `Bot`.
- `logVLam (Arr v w) e b`: for *any* argument closure `(m, d)` satisfying
  `LogE v d m`, evaluating `b` with `(m, d)` pushed onto `e` satisfies
  `LogE w`. (Notice `LogE v` sits in a **negative** position, which is why
  `logVLam` is written as a **large elimination** on `Value`, i.e., an ordinary
  term-to-`Type` Haskell function mutually recursive with `HaltsV` and
  `LogArr`, requiring no `type family` declaration)
- `logVLam (Join u v) e b = type (logVLam u e b, logVLam v e b)`: a pair of proofs.

The chapter proves `decAboveFun`, `logVLam`/`LogE`, full subsumption across all
8 `Sub` constructors (`subLogVLam` and `subLogE`, including `SubDist`), the
Fundamental Lemma (`fundamental`, all 6 `Denotes` rules), and Big-Step Adequacy
(`adequacyBigStep`).

## Imports

```haskell
{-# LANGUAGE AllowAmbiguousTypes, DependentTypes, ListTuplePuns #-}
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
  , HaltsV (..)
  , LogE
  , LogArr (..)
  , logVLam
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
  , adequacy
  , reduceToCbnW
  , reduceToCbn
  , cbnToReduceW
  , cbnToReduce
  , cbnIffReduce
  , adequacyIdApp
  , adequacyDelta
  , omegaNotAboveFun
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void, absurd)
import Data.Nat.Dependent (Nat (..))
import PLFH.Part1.Decidable (Dec (..))
import PLFH.Part1.Isomorphism (Iff (..))
import PLFH.Part1.Negation (Not)
import qualified PLFH.Part2.BigStep as B
import PLFH.Part2.BigStep (CbnTerminates (..), Clos (..), Env (..), EnvLookup (..), EvalBig (..), evalDeterm, omegaDiverges)
import PLFH.Part2.Untyped (BetaSteps (..), Fin (..), OmegaTerm, TermW, UTerm (..), mkTermW)
import PLFH.Part3.Denotational
  ( Den (..)
  , DenEq
  , Denotes (..)
  , Factor (..)
  , SomeArrMem (..)
  , Sub (..)
  , ValEnv (..)
  , ValLookup (..)
  , ValMem (..)
  , ValW (..)
  , Value (..)
  , allFunsMem
  , denotDelta
  , denotIdAppId
  , memToSub
  , subInv
  , unArrW
  , unJoinW
  )
import PLFH.Part3.Soundness (denotEquivStepsW)
```

## Being greater than or equal to a function (`AboveFun`) and its decidability

Because `Join Bot Bot` is syntactically distinct from `Bot` yet semantically
carries no function information, we distinguish non-trivial values using the
predicate **`AboveFun u`**: there exists some arrow `Arr v w` with
`Sub (Arr v w) u`.

Using our checked **`subInv`** theorem from [Denotational](/Denotational/),
we prove `notAboveFunBot` (`Bot` is never above a function), `aboveFunJoin`
(a join is above a function iff one of its branches is), and the full decision
procedure **`decAboveFun :: foreach (v :: Value) -> Dec (AboveFun v)`**.

```haskell
-- | Evidence that value `u` is at least some function entry `v ↦ w`.
data AboveFun (u :: Value) where
  MkAboveFun :: Sub (Arr v w) u -> AboveFun u

aboveFunArr :: AboveFun (Arr v w)
aboveFunArr = MkAboveFun SubRefl

aboveFunJoinL :: AboveFun a -> AboveFun (Join a b)
aboveFunJoinL (MkAboveFun lt) = MkAboveFun (SubJoinR1 lt)

aboveFunJoinR :: AboveFun b -> AboveFun (Join a b)
aboveFunJoinR (MkAboveFun lt) = MkAboveFun (SubJoinR2 lt)

aboveFunFromMem :: ValMem (Arr v w) u -> AboveFun u
aboveFunFromMem m = MkAboveFun (memToSub m)

-- | Upward closure of `AboveFun` under `Sub` (`above-fun-⊑`).
aboveFunSub :: foreach (u :: Value) -> AboveFun u -> Sub u u' -> AboveFun u'
aboveFunSub u (MkAboveFun lt') lt = MkAboveFun (SubTrans u lt' lt)

-- | Bottom is never above a function (`above-fun⊥`), proved via `subInv`!
notAboveFunBot :: Not (AboveFun Bot)
notAboveFunBot (MkAboveFun lt) = case subInv Bot lt MemArr of
  MkFactor u2 f s _ _ -> case allFunsMem u2 f of
    MkSomeArrMem _ _ m -> case s m of {}

-- | If `u ⊔ u'` is above a function, then `u` or `u'` is (`above-fun-⊔`).
aboveFunJoin :: foreach (u :: Value) -> foreach (u' :: Value)
             -> AboveFun (Join u u') -> Either (AboveFun u) (AboveFun u')
aboveFunJoin u u' (MkAboveFun lt) = case subInv (Join u u') lt MemArr of
  MkFactor g f s _ _ -> case allFunsMem g f of
    MkSomeArrMem _ _ m -> case s m of
      MemJoinL x -> Left  (aboveFunFromMem x)
      MemJoinR y -> Right (aboveFunFromMem y)

-- | If neither `u` nor `u'` is above a function, neither is their join.
notAboveFunJoin :: foreach (u :: Value) -> foreach (u' :: Value)
                -> Not (AboveFun u) -> Not (AboveFun u') -> Not (AboveFun (Join u u'))
notAboveFunJoin u u' nu nu' af = case aboveFunJoin u u' af of
  Left  au  -> nu au
  Right au' -> nu' au'

-- | Converse: if `u ⊔ u'` is not above a function, neither component is.
notAboveFunJoinInv :: Not (AboveFun (Join u u')) -> (Not (AboveFun u), Not (AboveFun u'))
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

## The value-indexed logical relation (`logVLam`, `LogE`) and Subsumption (`sub-𝕍`, `sub-𝔼`)

Because every call-by-name big-step evaluation terminates at a lambda closure
(`evalBigIsLam` in [BigStep](/BigStep/)), `HaltsV` directly packages
`EvalBig e m (MkClos (ULam b) d)` with `logVLam v d b`, and `newtype LogArr`
wraps the impredicative `forall k d m` in the `Arr` clause of `logVLam`.

Look closely at **`haltsVJoin`** (which combines `LogE w₁` and `LogE w₂` into
`LogE (Join w₁ w₂)`): when *both* `w₁` and `w₂` are `AboveFun`, we get two
big-step halting derivations `ev1` and `ev2` for the same `(e, m)`, and
**`BigStep.evalDeterm`** unifies their resulting lambda closures (`Refl`) so we
can pair `lv1` and `lv2` on the *exact same* closure.

```haskell
-- | Witness that evaluating `m` in `e` halts at a lambda closure related to `v`.
type HaltsV :: forall (n :: Nat). Env n -> UTerm n -> Value -> Type
data HaltsV e m v where
  MkHaltsV :: EvalBig e m (MkClos (ULam b) d) -> logVLam v d b -> HaltsV e m v

-- | Expression logical relation `𝔼`: if `v` is above a function, `(m, e)` halts in `logVLam`.
type LogE :: forall (k :: Nat). Value -> Env k -> UTerm k -> Type
type LogE v e m = AboveFun v -> HaltsV e m v

-- | Wrapper for the impredicative `forall k d m` in the `Arr` clause of `logVLam`.
newtype LogArr (v :: Value) (w :: Value) (e :: Env n) (b :: UTerm (Succ n)) =
  MkLogArr { runLogArr :: forall (k :: Nat) (d :: Env k) (m :: UTerm k).
                          LogE v d m -> AboveFun w -> HaltsV (ECons (MkClos m d) e) b w }

-- | Value logical relation `𝕍` on lambda closures, written directly as a
-- term-to-`Type` large elimination mutually recursive with `HaltsV` and `LogArr`!
logVLam :: forall (n :: Nat). Value -> Env n -> UTerm (Succ n) -> Type
logVLam Bot        _ _ = type ()
logVLam (Arr v w)  e b = type (LogArr v w e b)
logVLam (Join u v) e b = type (logVLam u e b, logVLam v e b)

logVBotLam :: logVLam Bot e b
logVBotLam = ()

logVJoinLam :: logVLam u e b -> logVLam v e b -> logVLam (Join u v) e b
logVJoinLam u v = (u, v)

-- | Any value not above a function relates trivially to every lambda closure (`not-above-fun-𝕍`).
notAboveFunLogV :: forall (n :: Nat) (e :: Env n) (b :: UTerm (Succ n)).
                   foreach (v :: Value) -> Not (AboveFun v) -> logVLam v e b
notAboveFunLogV Bot        _  = ()
notAboveFunLogV (Arr _ _)  na = absurd (na aboveFunArr)
notAboveFunLogV (Join a c) na =
  ( notAboveFunLogV @n @e @b a (\af -> na (aboveFunJoinL af))
  , notAboveFunLogV @n @e @b c (\af -> na (aboveFunJoinR af)) )

-- | Join introduction for the expression logical relation (`𝔼-⊔`), using
-- `decAboveFun` and `BigStep.evalDeterm`.
haltsVJoin :: forall (n :: Nat) (e :: Env n) (m :: UTerm n).
              foreach (w1 w2 :: Value)
           -> LogE w1 e m
           -> LogE w2 e m
           -> LogE (Join w1 w2) e m
haltsVJoin w1 w2 le1 le2 af = case (decAboveFun w1, decAboveFun w2) of
  (Yes af1, Yes af2) -> case (le1 af1, le2 af2) of
    (MkHaltsV ev1 lv1, MkHaltsV ev2 lv2) -> case evalDeterm ev1 ev2 of
      Refl -> MkHaltsV ev1 (lv1, lv2)
  (Yes af1, No na2) -> case le1 af1 of
    MkHaltsV (ev1 :: EvalBig e m (MkClos (ULam b) (d :: Env k))) lv1 ->
      MkHaltsV ev1 (lv1, notAboveFunLogV @k @d @b w2 na2)
  (No na1, Yes af2) -> case le2 af2 of
    MkHaltsV (ev2 :: EvalBig e m (MkClos (ULam b) (d :: Env k))) lv2 ->
      MkHaltsV ev2 (notAboveFunLogV @k @d @b w1 na1, lv2)
  (No na1, No na2) -> absurd (notAboveFunJoin w1 w2 na1 na2 af)

subDistHelper :: forall (n :: Nat) (e :: Env n) (b :: UTerm (Succ n))
                        (a :: Value) (w1 :: Value) (w2 :: Value).
                 ValW w1 -> ValW w2
              -> (LogArr a w1 e b, LogArr a w2 e b)
              -> LogArr a (Join w1 w2) e b
subDistHelper (MkValW w1) (MkValW w2) (f1, f2) =
  MkLogArr (\le af -> haltsVJoin w1 w2 (runLogArr f1 le) (runLogArr f2 le) af)

-- | Downward closure of `logVLam` under all 8 rules of `Sub` (`sub-𝕍`).
subLogVLam :: forall (n :: Nat) (e :: Env n) (b :: UTerm (Succ n)) (u :: Value) (v :: Value).
              ValW u -> ValW v
           -> Sub u v
           -> logVLam v e b
           -> logVLam u e b
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
    go :: forall (m :: Value). ValW m -> Sub u m -> Sub m v -> logVLam v e b -> logVLam u e b
    go wMid s1 s2 x =
      subLogVLam @n @e @b @u @m wu wMid s1 (subLogVLam @n @e @b @m @v wMid wv s2 x)
subLogVLam wu wv (SubArr l1 l2)     lv = case (unArrW wu, unArrW wv) of
  ((wu1, wu2), (wv1, wv2)) ->
    MkLogArr (\le -> subLogE wu2 wv2 l2 (runLogArr lv (subLogE wv1 wu1 l1 le)))
subLogVLam wu _  SubDist            lv = case unArrW wu of
  (_, wJoin) -> case unJoinW wJoin of
    (ww1, ww2) -> subDistHelper @n @e @b ww1 ww2 lv

-- | Downward closure of `LogE` under `Sub` (`sub-𝔼`).
subLogE :: forall (n :: Nat) (e :: Env n) (m :: UTerm n) (u :: Value) (v :: Value).
           ValW u -> ValW v
        -> Sub u v
        -> LogE v e m
        -> LogE u e m
subLogE wu@(MkValW u) wv lt le af = case le (aboveFunSub u af lt) of
  MkHaltsV (ev :: EvalBig e m (MkClos (ULam b) (d :: Env k))) lv ->
    MkHaltsV ev (subLogVLam @k @d @b wu wv lt lv)
```

## The Fundamental Lemma and Big-Step Adequacy

Every rule of `Denotes` (`DVar`, `DElim`, `DIntro`, `DBot`, `DJoin`, `DSub`)
checks directly in **`fundamental`**, yielding **`adequacyBigStep`**, and we
can execute `adequacyBigStep` on
`denotIdAppId (MkValW Bot)` (`adequacyIdApp`), watching the adequacy proof
actually compute a machine-checked call-by-name halting derivation for
`(λx. x) (λx. x)` at runtime.

```haskell
-- | Pointwise logical relation witness for a variable lookup in `e'`.
data EnvLogHit (e' :: Env n) (x :: Fin n) (v :: Value) where
  MkEnvLogHit :: EnvLookup e' x (MkClos m' d') -> LogE v d' m' -> EnvLogHit e' x v

-- | Environment logical relation (`𝒢`): every variable value in `e` is
-- logically related to its closure in `e'`.
type EnvLog (e' :: Env n) (e :: ValEnv n) =
  forall (x :: Fin n) (v :: Value). ValLookup e x v -> EnvLogHit e' x v

envLogNil :: EnvLog ENil VNil
envLogNil lk = case lk of {}

envLogCons :: LogE v d' m' -> EnvLog e' e -> EnvLog (ECons (MkClos m' d') e') (VCons e v)
envLogCons le _  VLZ      = MkEnvLogHit ELZ le
envLogCons _  el (VLS lk) = case el lk of
  MkEnvLogHit envLk le' -> MkEnvLogHit (ELS envLk) le'

-- | Fundamental Lemma of the logical relation:
-- if `e ⊢ m ↓ v` and `e' 𝒢 e`, then `v 𝔼 (m, e')`.
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
  MkHaltsBig :: EvalBig e m (MkClos (ULam b) d) -> HaltsBig e m

-- | Big-Step Adequacy theorem (`adequacy`):
-- every closed term with a non-trivial function denotation halts at a lambda.
adequacyBigStep :: ValW v -> Denotes VNil m v -> AboveFun v -> HaltsBig ENil m
adequacyBigStep wv d af = case fundamental wv envLogNil d af of
  MkHaltsV ev _ -> MkHaltsBig ev

-- | Denotational adequacy (`adequacy`): any closed term denotationally equal
-- to a lambda abstraction halts under call-by-name big-step evaluation!
adequacy :: DenEq (Den m) (Den (ULam b)) -> HaltsBig ENil m
adequacy eq = case snd (eq (MkValW (Arr Bot Bot))) (MkDen (DIntro DBot)) of
  MkDen d -> adequacyBigStep (MkValW (Arr Bot Bot)) d aboveFunArr

-- | Small-step reduction to a lambda implies big-step termination (`reduce→cbn`)!
reduceToCbnW :: TermW m -> BetaSteps m (ULam b) -> HaltsBig ENil m
reduceToCbnW wm steps = adequacy (denotEquivStepsW wm steps)

reduceToCbn :: foreach (m :: UTerm Zero) -> BetaSteps m (ULam b) -> HaltsBig ENil m
reduceToCbn m steps = reduceToCbnW (mkTermW m) steps

-- | Big-step termination implies small-step reduction to a lambda (`cbn→reduce`)!
cbnToReduceW :: TermW u -> HaltsBig ENil u -> CbnTerminates u
cbnToReduceW wu (MkHaltsBig ev) = B.cbnToReduceW wu ev

cbnToReduce :: foreach (u :: UTerm Zero) -> HaltsBig ENil u -> CbnTerminates u
cbnToReduce u (MkHaltsBig ev) = B.cbnToReduce u ev

-- | Equivalence between call-by-name big-step halting and small-step termination (`cbn↔reduce`).
cbnIffReduce :: foreach (u :: UTerm Zero) -> Iff (HaltsBig ENil u) (CbnTerminates u)
cbnIffReduce u = Iff (cbnToReduce u) (\case MkCbnTerminates steps -> reduceToCbn u steps)

-- | Concrete execution of adequacy: `[] ⊢ id · id ↓ ⊥ ↦ ⊥` produces a real
-- call-by-name halting derivation for `(λx. x) (λx. x)`!
adequacyIdApp :: HaltsBig ENil (UApp (ULam (UVar FZ)) (ULam (UVar FZ)))
adequacyIdApp =
  adequacyBigStep (MkValW (Arr Bot Bot)) (denotIdAppId (MkValW Bot)) aboveFunArr

-- | Adequacy on the self-application combinator Δ = λx. x x: Δ itself halts!
adequacyDelta :: HaltsBig ENil (ULam (UApp (UVar FZ) (UVar FZ)))
adequacyDelta =
  adequacyBigStep
    (MkValW (Arr (Join (Arr Bot Bot) Bot) Bot))
    (denotDelta (MkValW Bot) (MkValW Bot))
    aboveFunArr

-- | Exercise `omega-not-above-fun`: combining `adequacyBigStep` with
-- `BigStep.omegaDiverges` proves in one line that `Ω` cannot denote any
-- value above a function—so `Bot` (and joins of `Bot`) are its only denotations!
omegaNotAboveFun :: ValW v -> Denotes VNil OmegaTerm v -> Not (AboveFun v)
omegaNotAboveFun wv d af = case adequacyBigStep wv d af of
  MkHaltsBig ev -> omegaDiverges ev
```

## Exercises

### Exercise `adequacy-k-omega` (practice)

Construct a `Denotes VNil` derivation showing that
`(λ x y. x) (λ z. z) Ω` denotes `Arr Bot Bot` (which satisfies `AboveFun`), and
apply `adequacy` to derive `Terminates` directly from its denotation without
constructing a manual reduction sequence.

### Exercise `logv-join-proj` (practice)

Prove that `logVLam (Join u v) e b` implies both `logVLam u e b` and
`logVLam v e b` directly from the definition of `logVLam`, and check how
`subLogVLam` uses `SubJoinR1` and `SubJoinR2`.

## Changes from PLFA

- Writes the value logical relation `logVLam` directly as a term-to-`Type` large elimination mutually recursive with `HaltsV` and `LogArr`.
- Proves `fundamental`, `adequacyBigStep`, `adequacy`, `reduceToCbn`, `cbnToReduce`, and `omegaNotAboveFun`.
