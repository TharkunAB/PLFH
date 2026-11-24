-- Generated from content/part3/Adequacy.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE AllowAmbiguousTypes, DataKinds, EmptyCase, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, PolyKinds, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures, TypeApplications, TypeFamilies #-}
{-# LANGUAGE TypeOperators, UndecidableInstances #-}
{-# LINE 17 "content/part3/Adequacy.md" #-}
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

{-# LINE 70 "content/part3/Adequacy.md" #-}
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

{-# LINE 136 "content/part3/Adequacy.md" #-}
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
