-- Generated from content/part3/Denotational.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE AllowAmbiguousTypes, DataKinds, EmptyCase, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, Modifiers, PolyKinds, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving, StandaloneKindSignatures, TypeAbstractions, TypeApplications, TypeOperators #-}
{-# LINE 68 "content/part3/Denotational.md" #-}
module PLFH.Part3.Denotational
  ( Value (..)
  , ValW (..)
  , unJoinW
  , unArrW
  , Sub (..)
  , subRefl
  , joinSubJoin
  , joinArrDist
  , joinSubInvL
  , joinSubInvR
  , ValMem (..)
  , ValSubset
  , memToSub
  , subsetToSub
  , Fun (..)
  , AllFuns
  , notFunBot
  , SomeArrMem (..)
  , allFunsMem
  , dom
  , cod
  , arrMemToSubDom
  , subArrToCodSub
  , Factor (..)
  , subInvTrans
  , subInv
  , arrSubArrInv
  , ValEnv (..)
  , ValLookup (..)
  , LookupSub (..)
  , EnvSub
  , envSubRefl
  , envSubCons
  , envSubConsRefl
  , Denotes (..)
  , denotId
  , denotIdTwo
  , denotIdAppId
  , denotDelta
  , denotOmega
  , envSubMono
  , upEnv
  , Denotation
  , DenEq
  , denEqRefl
  , denEqSym
  , denEqTrans
  , Den (..)
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import Data.Void (absurd)
import GHC.Exts (M)
import HaskLib.Nat (Nat (..))
import PLFH.Part1.Negation (Not)
import PLFH.Part2.Untyped (Fin (..), UTerm (..))

{-# LINE 135 "content/part3/Denotational.md" #-}
-- | Finite function tables (Scott/Plotkin/BCD filter model values),
-- declared directly in GADT syntax!
data Value where
  Bot  :: Value
  Arr  :: Value -> Value -> Value
  Join :: Value -> Value -> Value

deriving instance Show Value

-- | Retained runtime witness for a promoted `Value`, using a single `foreach`
-- field (not a singleton!). Carrying `ValW` in `DElim`, `DJoin`, and `DSub`
-- retains intermediate `Value`s just as Agda's `∀ {v}` retains them at runtime,
-- while letting proofs match GADT equalities before unpacking `foreach`.
data ValW (v :: Value) where
  MkValW :: foreach (v :: Value) -> ValW v

-- | Split a retained witness of a join into witnesses of its two components.
unJoinW :: ValW (Join a b) -> (ValW a, ValW b)
unJoinW (MkValW v) = go v Refl
  where
    go :: foreach (x :: Value) -> x :~: Join a b -> (ValW a, ValW b)
    go Bot        eq = case eq of {}
    go (Arr _ _)  eq = case eq of {}
    go (Join x y) eq = case eq of Refl -> (MkValW x, MkValW y)

-- | Split a retained witness of an arrow into witnesses of its domain and codomain.
unArrW :: ValW (Arr a b) -> (ValW a, ValW b)
unArrW (MkValW v) = go v Refl
  where
    go :: foreach (x :: Value) -> x :~: Arr a b -> (ValW a, ValW b)
    go Bot        eq = case eq of {}
    go (Join _ _) eq = case eq of {}
    go (Arr x y)  eq = case eq of Refl -> (MkValW x, MkValW y)

{-# LINE 186 "content/part3/Denotational.md" #-}
-- | Domain approximation order `u ⊑ v`.
data Sub (u :: Value) (v :: Value) where
  SubBot    :: Sub Bot v
  SubRefl   :: Sub v v
  SubJoinL  :: Sub v u -> Sub w u -> Sub (Join v w) u
  SubJoinR1 :: forall (u :: Value) (v :: Value) (w :: Value). Sub u v -> Sub u (Join v w)
  SubJoinR2 :: forall (u :: Value) (v :: Value) (w :: Value). Sub u w -> Sub u (Join v w)
  SubTrans  :: foreach (v :: Value) -> Sub u v -> Sub v w -> Sub u w
  SubArr    :: Sub v' v -> Sub w w' -> Sub (Arr v w) (Arr v' w')
  SubDist   :: Sub (Arr v (Join w w')) (Join (Arr v w) (Arr v w'))

-- | Reflexivity of `Sub` can also be derived by structural induction on `Value`.
subRefl :: foreach (v :: Value) -> Sub v v
subRefl Bot        = SubBot
subRefl (Arr v w)  = SubArr (subRefl v) (subRefl w)
subRefl (Join v w) = SubJoinL (SubJoinR1 (subRefl v)) (SubJoinR2 (subRefl w))

-- | Monotonicity of `Join` (`⊔⊑⊔`).
joinSubJoin :: Sub v v' -> Sub w w' -> Sub (Join v w) (Join v' w')
joinSubJoin d1 d2 = SubJoinL (SubJoinR1 d1) (SubJoinR2 d2)

-- | Combining two function entries with distinct inputs (`⊔↦⊔-dist`).
joinArrDist :: foreach (v :: Value) -> foreach (v' :: Value)
            -> foreach (w :: Value) -> foreach (w' :: Value)
            -> Sub (Arr (Join v v') (Join w w')) (Join (Arr v w) (Arr v' w'))
joinArrDist v v' w w' =
  SubTrans (Join (Arr (Join v v') w) (Arr (Join v v') w')) SubDist
    (joinSubJoin
      (SubArr (SubJoinR1 (subRefl v)) (subRefl w))
      (SubArr (SubJoinR2 (subRefl v')) (subRefl w')))

-- | Left and right inversion on joins (`⊔⊑-invL`, `⊔⊑-invR`).
joinSubInvL :: Sub (Join u v) w -> Sub u w
joinSubInvL SubRefl            = SubJoinR1 SubRefl
joinSubInvL (SubJoinL lt1 _)   = lt1
joinSubInvL (SubJoinR1 lt)     = SubJoinR1 (joinSubInvL lt)
joinSubInvL (SubJoinR2 lt)     = SubJoinR2 (joinSubInvL lt)
joinSubInvL (SubTrans m l1 l2) = SubTrans m (joinSubInvL l1) l2

joinSubInvR :: Sub (Join u v) w -> Sub v w
joinSubInvR SubRefl            = SubJoinR2 SubRefl
joinSubInvR (SubJoinL _ lt2)   = lt2
joinSubInvR (SubJoinR1 lt)     = SubJoinR1 (joinSubInvR lt)
joinSubInvR (SubJoinR2 lt)     = SubJoinR2 (joinSubInvR lt)
joinSubInvR (SubTrans m l1 l2) = SubTrans m (joinSubInvR l1) l2

{-# LINE 247 "content/part3/Denotational.md" #-}
-- | Membership of a leaf value `u` inside a join-tree `v` (`u ∈ v`).
data ValMem (u :: Value) (v :: Value) where
  MemBot   :: ValMem Bot Bot
  MemArr   :: ValMem (Arr v w) (Arr v w)
  MemJoinL :: ValMem u v -> ValMem u (Join v w)
  MemJoinR :: ValMem u w -> ValMem u (Join v w)

-- | Subset inclusion of join-trees (`v ⊆ w`).
type ValSubset (v :: Value) (w :: Value) = forall (u :: Value). ValMem u v -> ValMem u w

memToSub :: ValMem u v -> Sub u v
memToSub MemBot       = SubBot
memToSub MemArr       = SubRefl
memToSub (MemJoinL m) = SubJoinR1 (memToSub m)
memToSub (MemJoinR m) = SubJoinR2 (memToSub m)

subsetToSub :: foreach (u :: Value) -> ValSubset u v -> Sub u v
subsetToSub Bot        _ = SubBot
subsetToSub (Arr _ _)  s = memToSub (s MemArr)
subsetToSub (Join a b) s =
  SubJoinL (subsetToSub a (\m -> s (MemJoinL m)))
           (subsetToSub b (\m -> s (MemJoinR m)))

-- | Evidence that a value is a function entry `v ↦ w`.
data Fun (u :: Value) where
  IsFun :: Fun (Arr v w)

-- | Every leaf in `v` is a function entry.
type AllFuns (v :: Value) = forall (u :: Value). ValMem u v -> Fun u

notFunBot :: Not (Fun Bot)
notFunBot = \case {}

data SomeArrMem (u :: Value) where
  MkSomeArrMem :: foreach (v :: Value) -> foreach (w :: Value)
               -> ValMem (Arr v w) u -> SomeArrMem u

-- | Every non-empty collection of functions contains at least one function entry.
allFunsMem :: foreach (u :: Value) -> AllFuns u -> SomeArrMem u
allFunsMem Bot        f = absurd (notFunBot (f MemBot))
allFunsMem (Arr v w)  _ = MkSomeArrMem v w MemArr
allFunsMem (Join a _) f =
  case allFunsMem a (\m -> f (MemJoinL m)) of
    MkSomeArrMem v w mem -> MkSomeArrMem v w (MemJoinL mem)

-- | Join of all domains in a table (`dom`), ordinary binary-tree recursion!
dom :: Value -> Value
dom Bot        = Bot
dom (Arr v w)  = v
dom (Join a b) = Join (dom a) (dom b)

-- | Join of all codomains in a table (`cod`), ordinary binary-tree recursion!
cod :: Value -> Value
cod Bot        = Bot
cod (Arr v w)  = w
cod (Join a b) = Join (cod a) (cod b)

-- | If `v ↦ w ∈ u` then `v ⊆ dom u` (`↦∈→⊆dom`).
arrMemToSubDom :: forall (v :: Value) (w :: Value) (x :: Value).
                  foreach (u :: Value) -> ValMem (Arr v w) u -> ValMem x v -> ValMem x (dom u)
arrMemToSubDom Bot        m            _ = case m of {}
arrMemToSubDom (Arr _ _)  MemArr       x = x
arrMemToSubDom (Join a b) (MemJoinL m) x = MemJoinL @x @(dom a) @(dom b) (arrMemToSubDom @v @w @x a m x)
arrMemToSubDom (Join a b) (MemJoinR m) x = MemJoinR @x @(dom b) @(dom a) (arrMemToSubDom @v @w @x b m x)

-- | If `u ⊆ v ↦ w` then `cod u ⊆ w` (`⊆↦→cod⊆`).
subArrToCodSub :: forall (v :: Value) (w :: Value) (x :: Value).
                  foreach (u :: Value) -> ValSubset u (Arr v w) -> ValMem x (cod u) -> ValMem x w
subArrToCodSub Bot        s _            = case s @Bot MemBot of {}
subArrToCodSub (Arr a b)  s x            = case s @(Arr a b) MemArr of { MemArr -> x }
subArrToCodSub (Join a _) s (MemJoinL x) = subArrToCodSub @v @w @x a (\m -> s (MemJoinL m)) x
subArrToCodSub (Join _ b) s (MemJoinR y) = subArrToCodSub @v @w @x b (\m -> s (MemJoinR m)) y

{-# LINE 332 "content/part3/Denotational.md" #-}
-- | Witness that `v ↦ w` factors `u` into a sub-collection of functions `u'`.
data Factor (u :: Value) (v :: Value) (w :: Value) where
  MkFactor :: forall (u :: Value) (v :: Value) (w :: Value).
              foreach (u' :: Value)
           -> AllFuns u'
           -> ValSubset u' u
           -> Sub (dom u') v
           -> Sub w (cod u')
           -> Factor u v w

allFunsArr :: AllFuns (Arr a b)
allFunsArr MemArr = IsFun

allFunsDist :: AllFuns (Join (Arr a b) (Arr a c))
allFunsDist (MemJoinL MemArr) = IsFun
allFunsDist (MemJoinR MemArr) = IsFun

subJoinSelf :: Sub (Join a a) a
subJoinSelf = SubJoinL SubRefl SubRefl

mkJoinFactor :: forall (u2 :: Value) (d1 :: Value) (c1 :: Value) (d2 :: Value) (c2 :: Value).
                Factor u2 d1 c1 -> Factor u2 d2 c2 -> Factor u2 (Join d1 d2) (Join c1 c2)
mkJoinFactor (MkFactor u31 f1 s1 d1 c1) (MkFactor u32 f2 s2 d2 c2) =
  MkFactor @u2 @(Join d1 d2) @(Join c1 c2) (Join u31 u32)
    (\case { MemJoinL m -> f1 m; MemJoinR m -> f2 m })
    (\case { MemJoinL m -> s1 m; MemJoinR m -> s2 m })
    (joinSubJoin d1 d2)
    (joinSubJoin c1 c2)

mkArrFactor :: foreach (a :: Value) -> foreach (b :: Value) -> Factor (Arr a b) a b
mkArrFactor a b = MkFactor @(Arr a b) @a @b (Arr a b) allFunsArr (\z -> z) SubRefl SubRefl

mkArrSubFactor :: forall (v :: Value) (w :: Value).
                  foreach (u21 :: Value) -> foreach (u22 :: Value)
               -> Sub u21 v -> Sub w u22 -> Factor (Arr u21 u22) v w
mkArrSubFactor u21 u22 lt1 lt2 =
  MkFactor @(Arr u21 u22) @v @w (Arr u21 u22) allFunsArr (\z -> z) lt1 lt2

mkDistFactor :: foreach (a :: Value) -> foreach (b :: Value) -> foreach (c :: Value)
             -> Factor (Join (Arr a b) (Arr a c)) a (Join b c)
mkDistFactor a b c =
  MkFactor @(Join (Arr a b) (Arr a c)) @a @(Join b c) (Join (Arr a b) (Arr a c))
    allFunsDist (\z -> z) subJoinSelf SubRefl

-- | Transitivity factoring lemma (`sub-inv-trans`).
subInvTrans :: forall (u :: Value) (u2 :: Value).
               foreach (u' :: Value)
            -> AllFuns u'
            -> ValSubset u' u
            -> (forall (v' :: Value) (w' :: Value). ValMem (Arr v' w') u -> Factor u2 v' w')
            -> Factor u2 (dom u') (cod u')
subInvTrans Bot        fu _    _  = absurd (notFunBot (fu MemBot))
subInvTrans (Arr _ _)  _  subU ih = ih (subU MemArr)
subInvTrans (Join a b) fu subU ih =
  mkJoinFactor @u2 @(dom a) @(cod a) @(dom b) @(cod b)
    (subInvTrans @u @u2 a (\m -> fu (MemJoinL m)) (\m -> subU (MemJoinL m)) ih)
    (subInvTrans @u @u2 b (\m -> fu (MemJoinR m)) (\m -> subU (MemJoinR m)) ih)

mapFactorL :: forall (a :: Value) (b :: Value) (v :: Value) (w :: Value).
              Factor a v w -> Factor (Join a b) v w
mapFactorL (MkFactor u' f s d c) = MkFactor @(Join a b) @v @w u' f (\z -> MemJoinL (s z)) d c

mapFactorR :: forall (a :: Value) (b :: Value) (v :: Value) (w :: Value).
              Factor b v w -> Factor (Join a b) v w
mapFactorR (MkFactor u' f s d c) = MkFactor @(Join a b) @v @w u' f (\z -> MemJoinR (s z)) d c

subInvRefl :: foreach (x :: Value) -> ValMem (Arr v w) x -> Factor x v w
subInvRefl Bot        m            = case m of {}
subInvRefl (Arr a b)  MemArr       = mkArrFactor a b
subInvRefl (Join a _) (MemJoinL m) = mapFactorL (subInvRefl a m)
subInvRefl (Join _ b) (MemJoinR m) = mapFactorR (subInvRefl b m)

subInvJoinR1 :: forall (a :: Value) (b :: Value) (u1 :: Value) (v :: Value) (w :: Value).
                foreach (x :: Value) -> (x :~: Join a b) -> Sub u1 a -> ValMem (Arr v w) u1 -> Factor x v w
subInvJoinR1 Bot        eq _ _ = case eq of {}
subInvJoinR1 (Arr _ _)  eq _ _ = case eq of {}
subInvJoinR1 (Join a _) eq lt1 m = case eq of
  Refl -> mapFactorL (subInv a lt1 m)

subInvJoinR2 :: forall (a :: Value) (b :: Value) (u1 :: Value) (v :: Value) (w :: Value).
                foreach (x :: Value) -> (x :~: Join a b) -> Sub u1 b -> ValMem (Arr v w) u1 -> Factor x v w
subInvJoinR2 Bot        eq _ _ = case eq of {}
subInvJoinR2 (Arr _ _)  eq _ _ = case eq of {}
subInvJoinR2 (Join _ b) eq lt2 m = case eq of
  Refl -> mapFactorR (subInv b lt2 m)

subInvArr :: forall (u21 :: Value) (u22 :: Value) (v :: Value) (w :: Value).
             foreach (x :: Value) -> (x :~: Arr u21 u22) -> Sub u21 v -> Sub w u22 -> Factor x v w
subInvArr Bot        eq _   _   = case eq of {}
subInvArr (Join _ _) eq _   _   = case eq of {}
subInvArr (Arr a b)  eq lt1 lt2 = case eq of
  Refl -> mkArrSubFactor @v @w a b lt1 lt2

subInvDist :: forall (a :: Value) (b :: Value) (c :: Value).
              foreach (x :: Value) -> (x :~: Join (Arr a b) (Arr a c)) -> Factor x a (Join b c)
subInvDist Bot        eq = case eq of {}
subInvDist (Arr _ _)  eq = case eq of {}
subInvDist (Join l r) eq = case l of
  Bot       -> case eq of {}
  Join _ _  -> case eq of {}
  Arr a' b' -> case r of
    Bot      -> case eq of {}
    Join _ _ -> case eq of {}
    Arr _ c' -> case eq of
      Refl -> mkDistFactor a' b' c'

-- | Main inversion theorem for `Sub` (`sub-inv`): if `u1 ⊑ u2` and `v ↦ w ∈ u1`,
-- then `v ↦ w` factors `u2` into a sub-collection of functions.
subInv :: forall (u1 :: Value) (v :: Value) (w :: Value).
          foreach (u2 :: Value) -> Sub u1 u2 -> ValMem (Arr v w) u1 -> Factor u2 v w
subInv u2 lt m = case lt of
  SubBot            -> case m of {}
  SubRefl           -> subInvRefl u2 m
  SubJoinL lt1 lt2  -> case m of
    MemJoinL x -> subInv u2 lt1 x
    MemJoinR y -> subInv u2 lt2 y
  SubJoinR1 @_ @a @b lt1 -> subInvJoinR1 @a @b u2 Refl lt1 m
  SubJoinR2 @_ @a @b lt2 -> subInvJoinR2 @a @b u2 Refl lt2 m
  SubTrans u lt1 lt2 ->
    case subInv u lt1 m of
      MkFactor u' fu' u'sub d1 c1 ->
        case subInvTrans @u @u2 u' fu' u'sub (\m' -> subInv u2 lt2 m') of
          MkFactor u3 fu3 u3sub d2 c2 ->
            MkFactor @u2 @v @w u3 fu3 u3sub (SubTrans (dom u') d2 d1) (SubTrans (cod u') c1 c2)
  SubArr lt1 lt2    -> case m of
    MemArr -> subInvArr u2 Refl lt1 lt2
  SubDist           -> case m of
    MemArr -> subInvDist u2 Refl

finishArrSubInv :: forall (v :: Value) (w :: Value) (v' :: Value) (w' :: Value).
                   Factor (Arr v' w') v w -> (Sub v' v, Sub w w')
finishArrSubInv (MkFactor g f s db cc) = case allFunsMem g f of
  MkSomeArrMem u u' m -> case s @(Arr u u') m of
    MemArr ->
      ( SubTrans (dom g) (subsetToSub @(dom g) u (\x -> arrMemToSubDom @u @u' g m x)) db
      , SubTrans (cod g) cc (subsetToSub @w' (cod g) (\x -> subArrToCodSub @v' @w' g s x)) )

-- | Function subtyping inversion (`↦⊑↦-inv`): if `v ↦ w ⊑ v' ↦ w'` then `v' ⊑ v` and `w ⊑ w'`.
arrSubArrInv :: forall (v :: Value) (w :: Value).
                foreach (v' :: Value) -> foreach (w' :: Value)
             -> Sub (Arr v w) (Arr v' w') -> (Sub v' v, Sub w w')
arrSubArrInv v' w' lt = finishArrSubInv (subInv (Arr v' w') lt MemArr)

{-# LINE 499 "content/part3/Denotational.md" #-}
-- | Value environment of scope depth `n`.
data ValEnv (n :: Nat) where
  VNil  :: ValEnv Zero
  VCons :: ValEnv n -> Value -> ValEnv (Succ n)

-- | Relational variable lookup in a value environment.
type ValLookup :: forall (n :: Nat). ValEnv n -> Fin n -> Value -> Type
data ValLookup e x v where
  VLZ :: ValLookup (VCons e v) FZ v
  VLS :: ValLookup e x v -> ValLookup (VCons e w) (FS x) v

-- | Witness that variable `x` in `e2` has a value at least `v1`.
data LookupSub (e2 :: ValEnv n) (x :: Fin n) (v1 :: Value) where
  LSRefl :: ValLookup e2 x v1 -> LookupSub e2 x v1
  LSSub  :: ValW v2 -> ValLookup e2 x v2 -> Sub v1 v2 -> LookupSub e2 x v1

-- | Pointwise environment approximation (`e1 ⊑ e2`).
type EnvSub (e1 :: ValEnv n) (e2 :: ValEnv n) =
  forall (x :: Fin n) (v1 :: Value). ValLookup e1 x v1 -> LookupSub e2 x v1

envSubRefl :: EnvSub e e
envSubRefl lk = LSRefl lk

envSubCons :: ValW v2 -> EnvSub e1 e2 -> Sub v1 v2 -> EnvSub (VCons e1 v1) (VCons e2 v2)
envSubCons wv2 _  lt VLZ      = LSSub wv2 VLZ lt
envSubCons _   es _  (VLS lk) = case es lk of
  LSRefl lk2       -> LSRefl (VLS lk2)
  LSSub wv2 lk2 lt -> LSSub wv2 (VLS lk2) lt

envSubConsRefl :: EnvSub e1 e2 -> EnvSub (VCons e1 v) (VCons e2 v)
envSubConsRefl _  VLZ      = LSRefl VLZ
envSubConsRefl es (VLS lk) = case es lk of
  LSRefl lk2       -> LSRefl (VLS lk2)
  LSSub wv2 lk2 lt -> LSSub wv2 (VLS lk2) lt

-- | Denotational semantics judgment: `e ⊢ m ↓ v`.
-- `DElim`, `DJoin`, and `DSub` carry `ValW` witnesses for their intermediate
-- `Value`s, matching Agda's retained `∀ {v}` arguments and enabling both
-- application inversion (`Compositional`) and the Fundamental Lemma (`Adequacy`).
type Denotes :: forall (n :: Nat). ValEnv n -> UTerm n -> Value -> Type
data Denotes e m v where
  DVar   :: ValLookup e x v -> Denotes e (UVar x) v
  DElim  :: ValW v -> Denotes e l (Arr v w) -> Denotes e m v -> Denotes e (UApp l m) w
  DIntro :: Denotes (VCons e v) b w -> Denotes e (ULam b) (Arr v w)
  DBot   :: Denotes e m Bot
  DJoin  :: ValW v -> ValW w -> Denotes e m v -> Denotes e m w -> Denotes e m (Join v w)
  DSub   :: ValW v -> Denotes e m v -> Sub w v -> Denotes e m w

-- | Identity function: `e ⊢ λx. x ↓ v ↦ v`.
denotId :: Denotes e (ULam (UVar FZ)) (Arr v v)
denotId = DIntro (DVar VLZ)

-- | Two-row table for identity: `e ⊢ λx. x ↓ (v ↦ v) ⊔ (w ↦ w)`.
denotIdTwo :: ValW v -> ValW w -> Denotes e (ULam (UVar FZ)) (Join (Arr v v) (Arr w w))
denotIdTwo (MkValW v) (MkValW w) =
  DJoin (MkValW (Arr v v)) (MkValW (Arr w w)) denotId denotId

-- | Self-application of identity: `[] ⊢ id · id ↓ u ↦ u`.
denotIdAppId :: ValW u -> Denotes VNil (UApp (ULam (UVar FZ)) (ULam (UVar FZ))) (Arr u u)
denotIdAppId (MkValW u) = DElim (MkValW (Arr u u)) denotId denotId

-- | Self-application combinator Δ = λx. x x: `[] ⊢ Δ ↓ ((v ↦ w) ⊔ v) ↦ w`.
denotDelta :: ValW v -> ValW w
           -> Denotes VNil (ULam (UApp (UVar FZ) (UVar FZ))) (Arr (Join (Arr v w) v) w)
denotDelta wv@(MkValW v) (MkValW w) =
  let wTable = MkValW (Join (Arr v w) v)
  in DIntro (DElim wv (DSub wTable (DVar VLZ) (SubJoinR1 SubRefl))
                      (DSub wTable (DVar VLZ) (SubJoinR2 SubRefl)))

-- | Diverging term Ω = Δ · Δ derives ⊥ (both via `DElim` and trivially via `DBot`).
denotOmega :: Denotes VNil
                (UApp (ULam (UApp (UVar FZ) (UVar FZ)))
                      (ULam (UApp (UVar FZ) (UVar FZ))))
                Bot
denotOmega =
  DElim (MkValW (Join (Arr Bot Bot) Bot))
        (denotDelta (MkValW Bot) (MkValW Bot))
        (DJoin (MkValW (Arr Bot Bot)) (MkValW Bot) (DIntro DBot) DBot)

-- | Environment monotonicity (`⊑-env`): enlarging an environment preserves denotations!
envSubMono :: EnvSub e1 e2 -> Denotes e1 m v -> Denotes e2 m v
envSubMono es (DVar lk)         = case es lk of
  LSRefl lk2       -> DVar lk2
  LSSub wv2 lk2 lt -> DSub wv2 (DVar lk2) lt
envSubMono es (DElim wv d1 d2)  = DElim wv (envSubMono es d1) (envSubMono es d2)
envSubMono es (DIntro d)        = DIntro (envSubMono (envSubConsRefl es) d)
envSubMono _  DBot              = DBot
envSubMono es (DJoin w1 w2 d1 d2) = DJoin w1 w2 (envSubMono es d1) (envSubMono es d2)
envSubMono es (DSub wv d lt)    = DSub wv (envSubMono es d) lt

-- | Enlarging the most recently bound variable (`up-env`).
upEnv :: ValW u2 -> Denotes (VCons e u1) m v -> Sub u1 u2 -> Denotes (VCons e u2) m v
upEnv wu2 d lt = envSubMono (envSubCons wu2 envSubRefl lt) d

{-# LINE 603 "content/part3/Denotational.md" #-}
-- | A denotation in scope depth `n` relates environments to values (matchable arrows `%M`).
type Denotation (n :: Nat) = ValEnv n %M -> Value %M -> Type

-- | Denotational equivalence (`D1 ≃ D2`), parameterized by retained value witness `ValW v`.
type DenEq (d1 :: Denotation n) (d2 :: Denotation n) =
  forall (e :: ValEnv n) (v :: Value). ValW v -> (d1 e v -> d2 e v, d2 e v -> d1 e v)

denEqRefl :: DenEq d d
denEqRefl _ = (\x -> x, \x -> x)

denEqSym :: DenEq d1 d2 -> DenEq d2 d1
denEqSym eq wv = case eq wv of { (f, g) -> (g, f) }

denEqTrans :: DenEq d1 d2 -> DenEq d2 d3 -> DenEq d1 d3
denEqTrans eq1 eq2 wv =
  case (eq1 wv, eq2 wv) of
    ((f1, g1), (f2, g2)) -> (\x -> f2 (f1 x), \y -> g1 (g2 y))

-- | `Den m` is the denotation `ℰ m` of term `m`, wrapping `Denotes e m v`.
newtype Den (m :: UTerm n) (e :: ValEnv n) (v :: Value) = MkDen { unDen :: Denotes e m v }
