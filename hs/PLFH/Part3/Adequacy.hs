-- Generated from content/part3/Adequacy.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE AllowAmbiguousTypes, DataKinds, EmptyCase, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, PolyKinds, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures, TypeApplications, TypeFamilies #-}
{-# LANGUAGE TypeOperators, UndecidableInstances #-}
{-# LINE 16 "content/part3/Adequacy.md" #-}
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
  , EvalDeterm
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
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void, absurd)
import HaskLib.Nat (Nat (..))
import PLFH.Part1.Decidable (Dec (..))
import PLFH.Part1.Negation (Not)
import PLFH.Part2.BigStep (Clos (..), Env (..), EnvLookup (..), EvalBig (..))
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
  , memToSub
  , subInv
  , unArrW
  , unJoinW
  )

{-# LINE 95 "content/part3/Adequacy.md" #-}
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

{-# LINE 163 "content/part3/Adequacy.md" #-}
-- | Weak-head normal form: a lambda abstraction.
type WHNF :: forall (n :: Nat). UTerm n -> Type
data WHNF m where
  WLam :: WHNF ('ULam b)

-- | Determinism of call-by-name big-step evaluation (`⇓-determ`).
-- Parameterized explicitly here while `BigStep.evalDeterm` waits on the R11
-- Desugar Core Lint fix (`R11_MixedKindCoercionCoreLint.hs`, queued in 597).
type EvalDeterm =
  forall (n :: Nat) (e :: Env n) (m :: UTerm n) (c1 :: Clos) (c2 :: Clos).
    EvalBig e m c1 -> EvalBig e m c2 -> c1 :~: c2

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
-- `decAboveFun` and `EvalDeterm` when both components are above a function!
haltsVJoin :: forall (n :: Nat) (e :: Env n) (m :: UTerm n).
              EvalDeterm
           -> foreach (w1 :: Value) -> foreach (w2 :: Value)
           -> LogE w1 e m
           -> LogE w2 e m
           -> LogE ('Join w1 w2) e m
haltsVJoin ed w1 w2 le1 le2 af = case (decAboveFun w1, decAboveFun w2) of
  (Yes af1, Yes af2) -> case (le1 af1, le2 af2) of
    (MkHaltsV ev1 lv1, MkHaltsV ev2 lv2) -> case ed ev1 ev2 of
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
                 EvalDeterm
              -> ValW w1 -> ValW w2
              -> (LogArr a w1 e b, LogArr a w2 e b)
              -> LogArr a ('Join w1 w2) e b
subDistHelper ed (MkValW w1) (MkValW w2) (f1, f2) =
  MkLogArr (\le af -> haltsVJoin ed w1 w2 (runLogArr f1 le) (runLogArr f2 le) af)

-- | Full downward closure of `LogVLam` under all 8 rules of `Sub` (`sub-𝕍`)!
subLogVLam :: forall (n :: Nat) (e :: Env n) (b :: UTerm ('Succ n)) (u :: Value) (v :: Value).
              EvalDeterm
           -> ValW u -> ValW v
           -> Sub u v
           -> LogVLam v e b
           -> LogVLam u e b
subLogVLam _  _  _  SubBot             _  = ()
subLogVLam _  _  _  SubRefl            lv = lv
subLogVLam ed wu wv (SubJoinL l1 l2)   lv = case unJoinW wu of
  (wu1, wu2) -> (subLogVLam @n @e @b ed wu1 wv l1 lv, subLogVLam @n @e @b ed wu2 wv l2 lv)
subLogVLam ed wu wv (SubJoinR1 l1)     lv = case unJoinW wv of
  (wv1, _) -> subLogVLam @n @e @b ed wu wv1 l1 (fst lv)
subLogVLam ed wu wv (SubJoinR2 l2)     lv = case unJoinW wv of
  (_, wv2) -> subLogVLam @n @e @b ed wu wv2 l2 (snd lv)
subLogVLam ed wu wv (SubTrans mid l1 l2) lv = go (MkValW mid) l1 l2 lv
  where
    go :: forall (m :: Value). ValW m -> Sub u m -> Sub m v -> LogVLam v e b -> LogVLam u e b
    go wMid s1 s2 x =
      subLogVLam @n @e @b @u @m ed wu wMid s1 (subLogVLam @n @e @b @m @v ed wMid wv s2 x)
subLogVLam ed wu wv (SubArr l1 l2)     lv = case (unArrW wu, unArrW wv) of
  ((wu1, wu2), (wv1, wv2)) ->
    MkLogArr (\le -> subLogE ed wu2 wv2 l2 (runLogArr lv (subLogE ed wv1 wu1 l1 le)))
subLogVLam ed wu _  SubDist            lv = case unArrW wu of
  (_, wJoin) -> case unJoinW wJoin of
    (ww1, ww2) -> subDistHelper @n @e @b ed ww1 ww2 lv

-- | Full downward closure of `LogE` under `Sub` (`sub-𝔼`)!
subLogE :: forall (n :: Nat) (e :: Env n) (m :: UTerm n) (u :: Value) (v :: Value).
           EvalDeterm
        -> ValW u -> ValW v
        -> Sub u v
        -> LogE v e m
        -> LogE u e m
subLogE ed wu@(MkValW u) wv lt le af = case le (aboveFunSub u af lt) of
  MkHaltsV (ev :: EvalBig e m ('MkClos ('ULam b) (d :: Env k))) lv ->
    MkHaltsV ev (subLogVLam @k @d @b ed wu wv lt lv)

{-# LINE 285 "content/part3/Adequacy.md" #-}
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

-- | Fundamental Lemma of the logical relation:
-- if `e ⊢ m ↓ v` and `e' 𝒢 e`, then `v 𝔼 (m, e')`!
fundamental :: forall (n :: Nat) (e' :: Env n) (e :: ValEnv n) (m :: UTerm n) (v :: Value).
               EvalDeterm
            -> ValW v
            -> EnvLog e' e
            -> Denotes e m v
            -> LogE v e' m
fundamental _  _  el (DVar lk) af = case el lk of
  MkEnvLogHit envLk le -> case le af of
    MkHaltsV ev lv -> MkHaltsV (EVar envLk ev) lv
fundamental ed (MkValW v) el (DElim wArg@(MkValW vArg) d1 d2) af =
  case fundamental ed (MkValW (Arr vArg v)) el d1 aboveFunArr of
    MkHaltsV evL lvL -> case runLogArr lvL (fundamental ed wArg el d2) af of
      MkHaltsV evB lvB -> MkHaltsV (EApp evL evB) lvB
fundamental ed wv el (DIntro dBody) _ = case unArrW wv of
  (_, wv2) -> MkHaltsV ELam (MkLogArr (\le -> fundamental ed wv2 (envLogCons le el) dBody))
fundamental _  _  _  DBot af = absurd (notAboveFunBot af)
fundamental ed _  el (DJoin w1@(MkValW v1) w2@(MkValW v2) d1 d2) af =
  haltsVJoin ed v1 v2 (fundamental ed w1 el d1) (fundamental ed w2 el d2) af
fundamental ed wv el (DSub wSuper d1 lt) af =
  subLogE ed wv wSuper lt (fundamental ed wSuper el d1) af

-- | Big-step termination witness: `(m, e)` evaluates to some lambda closure.
data HaltsBig (e :: Env n) (m :: UTerm n) where
  MkHaltsBig :: EvalBig e m ('MkClos ('ULam b) d) -> HaltsBig e m

-- | Big-step Adequacy theorem (`adequacy`):
-- every closed term with a non-trivial function denotation halts at a lambda!
adequacyBigStep :: EvalDeterm -> ValW v -> Denotes 'VNil m v -> AboveFun v -> HaltsBig 'ENil m
adequacyBigStep ed wv d af = case fundamental ed wv envLogNil d af of
  MkHaltsV ev _ -> MkHaltsBig ev
