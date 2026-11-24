---
title: "Soundness: Soundness of reduction with respect to denotational semantics"
prev: /Compositional/
next: /Adequacy/
src: content/part3/Soundness.md
module: PLFH.Part3.Soundness
plfaChapter: https://plfa.inf.ed.ac.uk/Soundness/
plfaAuthors: "Philip Wadler, Wen Kokke, and Jeremy G. Siek"
---

```haskell
{-# LANGUAGE AllowAmbiguousTypes, DataKinds, EmptyCase, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
module PLFH.Part3.Soundness
  ( InsertEnv (..)
  , denotShift
  , denotUnshift
  , denotSubst
  , SubstReflRes (..)
  , denotSubstReflect
  , betaPres
  , betaReflect
  , denotPreserve
  , denotPreserveMulti
  , denotReflect
  , denotReflectMulti
  , denotEquivSteps
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..))
import PLFH.Part2.Untyped
  ( BetaStep (..)
  , BetaSteps (..)
  , BumpFin (..)
  , Fin (..)
  , RemoveFin (..)
  , ShiftU (..)
  , SubstAtU (..)
  , UTerm (..)
  )
import PLFH.Part3.Compositional (lamInversion)
import PLFH.Part3.Denotational
  ( Den (..)
  , DenEq
  , Denotes (..)
  , EnvSub
  , Sub (..)
  , ValEnv (..)
  , ValLookup (..)
  , ValW (..)
  , Value (..)
  , envSubCons
  , envSubConsRefl
  , envSubMono
  , envSubRefl
  , unArrW
  )
```

In PLFA's **Soundness** chapter, we prove that full β-reduction both
**preserves** (`denotPreserve`, `denotPreserveMulti`) and **reflects**
(`denotReflect`, `denotReflectMulti`) denotations: if `M —↠ N`, then
`ℰ M ≃ ℰ N` (`denotEquivSteps`)!

Because `BetaStep` in [Untyped](/Untyped/) uses our deterministic relational
substitution `SubstAtU`, **every single lemma in this chapter—weakening
(`denotShift`), strengthening (`denotUnshift`), forward substitution
(`denotSubst`), backward substitution expansion (`denotSubstReflect`), forward
preservation (`denotPreserve`), backward subject expansion (`denotReflect`),
and full soundness (`denotEquivSteps`)—proves 100% unconditionally** with
`-dcore-lint -dstg-lint`!

## Environment insertion, weakening (`denotShift`), and strengthening (`denotUnshift`)

To track the variable position `c` across `ShiftU` and `SubstAtU`, we define
`InsertEnv c e u e'`, witnessing that `e'` is obtained by inserting value `u`
at index `c` into `e`:

```haskell
-- | Inserting a single value `u` at de Bruijn index `c` into `e` yields `e'`.
type InsertEnv :: forall (n :: Nat). Fin ('Succ n) -> ValEnv n -> Value -> ValEnv ('Succ n) -> Type
data InsertEnv c e u e' where
  IEZ :: InsertEnv 'FZ e u ('VCons e u)
  IES :: InsertEnv c e u e' -> InsertEnv ('FS c) ('VCons e w) u ('VCons e' w)

lookupBump :: InsertEnv c e u e' -> BumpFin c x y -> ValLookup e x v -> ValLookup e' y v
lookupBump IEZ      BumpZ       lk       = VLS lk
lookupBump (IES _)  BumpSZ      VLZ      = VLZ
lookupBump (IES ie) (BumpSS bf) (VLS lk) = VLS (lookupBump ie bf lk)

lookupUnbump :: InsertEnv c e u e' -> BumpFin c x y -> ValLookup e' y v -> ValLookup e x v
lookupUnbump IEZ      BumpZ       (VLS lk) = lk
lookupUnbump (IES _)  BumpSZ      VLZ      = VLZ
lookupUnbump (IES ie) (BumpSS bf) (VLS lk) = VLS (lookupUnbump ie bf lk)

lookupAtInsert :: InsertEnv c e u e' -> ValLookup e' c v -> v :~: u
lookupAtInsert IEZ      VLZ      = Refl
lookupAtInsert (IES ie) (VLS lk) = lookupAtInsert ie lk

lookupRemove :: InsertEnv c e u e' -> RemoveFin c x y -> ValLookup e' x v -> ValLookup e y v
lookupRemove IEZ      RemGt       (VLS lk) = lk
lookupRemove (IES _)  RemLt       VLZ      = VLZ
lookupRemove (IES ie) (RemSS rf)  (VLS lk) = VLS (lookupRemove ie rf lk)

insertLookupAt :: InsertEnv c e u e' -> ValLookup e' c u
insertLookupAt IEZ      = VLZ
insertLookupAt (IES ie) = VLS (insertLookupAt ie)

insertLookupOther :: InsertEnv c e u e' -> RemoveFin c x y -> ValLookup e y v -> ValLookup e' x v
insertLookupOther IEZ      RemGt      lk       = VLS lk
insertLookupOther (IES _)  RemLt      VLZ      = VLZ
insertLookupOther (IES ie) (RemSS rf) (VLS lk) = VLS (insertLookupOther ie rf lk)

-- | Weakening of denotations under shifting (`rename-pres`).
denotShift :: ShiftU c m m' -> InsertEnv c e u e' -> Denotes e m v -> Denotes e' m' v
denotShift (ShiftVar bf)      ie (DVar lk)          = DVar (lookupBump ie bf lk)
denotShift (ShiftApp sh1 sh2) ie (DElim wv d1 d2)   = DElim wv (denotShift sh1 ie d1) (denotShift sh2 ie d2)
denotShift (ShiftLam shB)     ie (DIntro d)         = DIntro (denotShift shB (IES ie) d)
denotShift _                  _  DBot               = DBot
denotShift sh                 ie (DJoin w1 w2 d1 d2) = DJoin w1 w2 (denotShift sh ie d1) (denotShift sh ie d2)
denotShift sh                 ie (DSub wv d lt)     = DSub wv (denotShift sh ie d) lt

-- | Strengthening of denotations under unshifting (`rename-reflect`).
denotUnshift :: ShiftU c m m' -> InsertEnv c e u e' -> Denotes e' m' v -> Denotes e m v
denotUnshift (ShiftVar bf)      ie (DVar lk)          = DVar (lookupUnbump ie bf lk)
denotUnshift (ShiftApp sh1 sh2) ie (DElim wv d1 d2)   = DElim wv (denotUnshift sh1 ie d1) (denotUnshift sh2 ie d2)
denotUnshift (ShiftLam shB)     ie (DIntro d)         = DIntro (denotUnshift shB (IES ie) d)
denotUnshift _                  _  DBot               = DBot
denotUnshift sh                 ie (DJoin w1 w2 d1 d2) = DJoin w1 w2 (denotUnshift sh ie d1) (denotUnshift sh ie d2)
denotUnshift sh                 ie (DSub wv d lt)     = DSub wv (denotUnshift sh ie d) lt
```

## Substitution preservation (`denotSubst`) and expansion (`denotSubstReflect`)

Both directions of single-variable substitution follow directly by structural
induction on `Denotes` and `SubstAtU`, using environment monotonicity
(`envSubMono`) to join argument values when an application or join needs two
different approximations of the substituted term `w`:

```haskell
-- | Forward single-variable substitution lemma (`subst-pres`).
denotSubst :: SubstAtU c w m m'
           -> InsertEnv c e u e'
           -> Denotes e w u
           -> Denotes e' m v
           -> Denotes e m' v
denotSubst SUEq            ie dw (DVar lk)          = case lookupAtInsert ie lk of Refl -> dw
denotSubst (SUNeq rf)      ie _  (DVar lk)          = DVar (lookupRemove ie rf lk)
denotSubst (SUApp s1 s2)   ie dw (DElim wv d1 d2)   = DElim wv (denotSubst s1 ie dw d1) (denotSubst s2 ie dw d2)
denotSubst (SULam shW sB)  ie dw (DIntro d)         = DIntro (denotSubst sB (IES ie) (denotShift shW IEZ dw) d)
denotSubst _               _  _  DBot               = DBot
denotSubst sub             ie dw (DJoin w1 w2 d1 d2) = DJoin w1 w2 (denotSubst sub ie dw d1) (denotSubst sub ie dw d2)
denotSubst sub             ie dw (DSub wv d lt)     = DSub wv (denotSubst sub ie dw d) lt

-- | Existential result of backward substitution expansion: an argument value `u`,
-- an extended environment `e'`, a denotation `e ⊢ w ↓ u`, and `e' ⊢ m ↓ v`.
data SubstReflRes (c :: Fin ('Succ n)) (e :: ValEnv n) (w :: UTerm n) (m :: UTerm ('Succ n)) (v :: Value) where
  MkSubstRefl :: forall (n :: Nat) (c :: Fin ('Succ n)) (e :: ValEnv n) (w :: UTerm n)
                        (m :: UTerm ('Succ n)) (v :: Value) (u :: Value) (e' :: ValEnv ('Succ n)).
                 ValW u
              -> InsertEnv c e u e'
              -> Denotes e w u
              -> Denotes e' m v
              -> SubstReflRes c e w m v

data RebindInsert (c :: Fin ('Succ n)) (e :: ValEnv n) (u :: Value) where
  MkRebindInsert :: InsertEnv c e u e' -> RebindInsert c e u

rebindInsert :: InsertEnv c e u1 e1 -> RebindInsert c e u2
rebindInsert IEZ      = MkRebindInsert IEZ
rebindInsert (IES ie) = case rebindInsert ie of
  MkRebindInsert ie' -> MkRebindInsert (IES ie')

data JoinInsertRes (c :: Fin ('Succ n)) (e :: ValEnv n) (u1 :: Value) (u2 :: Value)
                   (e1 :: ValEnv ('Succ n)) (e2 :: ValEnv ('Succ n)) where
  MkJoinInsert :: InsertEnv c e ('Join u1 u2) e3
               -> EnvSub e1 e3
               -> EnvSub e2 e3
               -> JoinInsertRes c e u1 u2 e1 e2

joinInsert :: ValW u1 -> ValW u2
           -> InsertEnv c e u1 e1
           -> InsertEnv c e u2 e2
           -> JoinInsertRes c e u1 u2 e1 e2
joinInsert (MkValW u1) (MkValW u2) IEZ IEZ =
  let wu = MkValW (Join u1 u2)
  in MkJoinInsert IEZ
       (envSubCons wu envSubRefl (SubJoinR1 SubRefl))
       (envSubCons wu envSubRefl (SubJoinR2 SubRefl))
joinInsert wu1 wu2 (IES ie1) (IES ie2) = case joinInsert wu1 wu2 ie1 ie2 of
  MkJoinInsert ie3 es1 es2 ->
    MkJoinInsert (IES ie3) (envSubConsRefl es1) (envSubConsRefl es2)

unLamSubstRefl
  :: forall (n :: Nat) (c :: Fin ('Succ n)) (e :: ValEnv n) (a :: Value)
            (w :: UTerm n) (w' :: UTerm ('Succ n)) (b :: UTerm ('Succ ('Succ n))) (r :: Value).
     ShiftU 'FZ w w'
  -> SubstReflRes ('FS c) ('VCons e a) w' b r
  -> SubstReflRes c e w ('ULam b) ('Arr a r)
unLamSubstRefl shW (MkSubstRefl wu (IES ie) dwShifted db) =
  MkSubstRefl wu ie (denotUnshift shW IEZ dwShifted) (DIntro db)

-- | Backward single-variable substitution expansion (`subst-reflect`)!
denotSubstReflect
  :: forall (n :: Nat) (c :: Fin ('Succ n)) (e :: ValEnv n) (eBot :: ValEnv ('Succ n))
            (w :: UTerm n) (m :: UTerm ('Succ n)) (m' :: UTerm n) (v :: Value).
     ValW v
  -> SubstAtU c w m m'
  -> InsertEnv c e 'Bot eBot
  -> Denotes e m' v
  -> SubstReflRes c e w m v
denotSubstReflect _  _   ieBot DBot = MkSubstRefl (MkValW Bot) ieBot DBot DBot
denotSubstReflect _  sub ieBot (DJoin w1 w2 d1 d2) =
  case (denotSubstReflect w1 sub ieBot d1, denotSubstReflect w2 sub ieBot d2) of
    (MkSubstRefl wu1@(MkValW u1) ie1 dw1 dm1, MkSubstRefl wu2@(MkValW u2) ie2 dw2 dm2) ->
      case joinInsert wu1 wu2 ie1 ie2 of
        MkJoinInsert ie3 es1 es2 ->
          MkSubstRefl (MkValW (Join u1 u2)) ie3
            (DJoin wu1 wu2 dw1 dw2)
            (DJoin w1 w2 (envSubMono es1 dm1) (envSubMono es2 dm2))
denotSubstReflect _  sub ieBot (DSub wSuper d lt) =
  case denotSubstReflect wSuper sub ieBot d of
    MkSubstRefl wu ie dw dm -> MkSubstRefl wu ie dw (DSub wSuper dm lt)
denotSubstReflect wv SUEq ieBot d =
  case rebindInsert ieBot of
    MkRebindInsert ie -> MkSubstRefl wv ie d (DVar (insertLookupAt ie))
denotSubstReflect _  (SUNeq rf) ieBot (DVar lk) =
  MkSubstRefl (MkValW Bot) ieBot DBot (DVar (insertLookupOther ieBot rf lk))
denotSubstReflect (MkValW v) (SUApp s1 s2) ieBot (DElim wArg@(MkValW vArg) d1 d2) =
  case ( denotSubstReflect (MkValW (Arr vArg v)) s1 ieBot d1
       , denotSubstReflect wArg s2 ieBot d2 ) of
    (MkSubstRefl wu1@(MkValW u1) ie1 dw1 dl, MkSubstRefl wu2@(MkValW u2) ie2 dw2 dr) ->
      case joinInsert wu1 wu2 ie1 ie2 of
        MkJoinInsert ie3 es1 es2 ->
          MkSubstRefl (MkValW (Join u1 u2)) ie3
            (DJoin wu1 wu2 dw1 dw2)
            (DElim wArg (envSubMono es1 dl) (envSubMono es2 dr))
denotSubstReflect wv (SULam shW sB) ieBot (DIntro dBody) =
  case unArrW wv of
    (_, wCod) -> unLamSubstRefl shW (denotSubstReflect wCod sB (IES ieBot) dBody)

-- | Unconditional β-redex preservation.
betaPres :: SubstAtU 'FZ w b r -> Denotes ('VCons e u) b v -> Denotes e w u -> Denotes e r v
betaPres sub db dw = denotSubst sub IEZ dw db

-- | Unconditional β-redex subject expansion.
betaReflect :: ValW v -> SubstAtU 'FZ w b r -> Denotes e r v -> Denotes e ('UApp ('ULam b) w) v
betaReflect wv sub dr = case denotSubstReflect wv sub IEZ dr of
  MkSubstRefl wu IEZ dw db -> DElim wu (DIntro db) dw
```

<div class="wip-notice">
<strong>[WIP NOTICE — Desugar Core Lint on inline existential <code>IES</code> match inside GADT branch (R11)]</strong>
Notice that <code>unLamSubstRefl</code> is factored out as a top-level helper
with an explicit <code>SubstReflRes ('FS c) ('VCons e a) ...</code> signature.
Inlining the exact same <code>MkSubstRefl wu (IES ie) dwShifted db</code> match
directly inside the <code>SULam</code>/<code>DIntro</code> branch of
<code>denotSubstReflect</code> typechecks and then fails Desugar Core Lint
with <code>R11 mixed-kind coercion binder: 'VCons e1 w1 ~# 'VCons e a</code>.
Isolated as a 50-line minimal reproducer in
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R11_ExistentialNestedGadtCoreLint.hs"><code>reproducers/R11_ExistentialNestedGadtCoreLint.hs</code></a>.
</div>

## Unconditional Soundness (`denotPreserve`, `denotReflect`, `denotEquivSteps`)

Putting `betaPres` and `betaReflect` together with `lamInversion` from
[Compositional](/Compositional/), full β-reduction induces denotational
equivalence **`ℰ m ≃ ℰ m'`** unconditionally:

```haskell
-- | Unconditional forward preservation under a single β-step (`preserve`).
denotPreserve :: ValW v -> Denotes e m v -> BetaStep m m' -> Denotes e m' v
denotPreserve _ (DVar _) step = case step of {}
denotPreserve (MkValW v) (DElim wArg@(MkValW vArg) d1 d2) step = case step of
  XiApp1 r -> DElim wArg (denotPreserve (MkValW (Arr vArg v)) d1 r) d2
  XiApp2 r -> DElim wArg d1 (denotPreserve wArg d2 r)
  Beta sub -> betaPres sub (lamInversion (MkValW (Arr vArg v)) d1) d2
denotPreserve wv (DIntro d) step = case step of
  XiLam r -> case unArrW wv of
    (_, wv2) -> DIntro (denotPreserve wv2 d r)
denotPreserve _ DBot _ = DBot
denotPreserve _ (DJoin w1 w2 d1 d2) r =
  DJoin w1 w2 (denotPreserve w1 d1 r) (denotPreserve w2 d2 r)
denotPreserve _ (DSub wSuper d lt) r =
  DSub wSuper (denotPreserve wSuper d r) lt

-- | Multi-step β-reduction preserves denotations unconditionally.
denotPreserveMulti :: ValW v -> Denotes e m v -> BetaSteps m m' -> Denotes e m' v
denotPreserveMulti _  d BRefl       = d
denotPreserveMulti wv d (BCons s r) = denotPreserveMulti wv (denotPreserve wv d s) r

-- | Unconditional backward subject expansion under a single β-step (`reflect`)!
denotReflect :: ValW v -> BetaStep m m' -> Denotes e m' v -> Denotes e m v
denotReflect wv (Beta sub)   d                   = betaReflect wv sub d
denotReflect _  (XiApp1 _)   DBot                = DBot
denotReflect (MkValW v) (XiApp1 r) (DElim wArg@(MkValW vArg) d1 d2) =
  DElim wArg (denotReflect (MkValW (Arr vArg v)) r d1) d2
denotReflect _  s@(XiApp1 _) (DJoin w1 w2 d1 d2) =
  DJoin w1 w2 (denotReflect w1 s d1) (denotReflect w2 s d2)
denotReflect _  s@(XiApp1 _) (DSub wSuper d lt)  = DSub wSuper (denotReflect wSuper s d) lt
denotReflect _  (XiApp2 _)   DBot                = DBot
denotReflect _  (XiApp2 r)   (DElim wArg d1 d2)  = DElim wArg d1 (denotReflect wArg r d2)
denotReflect _  s@(XiApp2 _) (DJoin w1 w2 d1 d2) =
  DJoin w1 w2 (denotReflect w1 s d1) (denotReflect w2 s d2)
denotReflect _  s@(XiApp2 _) (DSub wSuper d lt)  = DSub wSuper (denotReflect wSuper s d) lt
denotReflect _  (XiLam _)    DBot                = DBot
denotReflect wv (XiLam r)    (DIntro d)          = case unArrW wv of
  (_, wv2) -> DIntro (denotReflect wv2 r d)
denotReflect _  s@(XiLam _)  (DJoin w1 w2 d1 d2) =
  DJoin w1 w2 (denotReflect w1 s d1) (denotReflect w2 s d2)
denotReflect _  s@(XiLam _)  (DSub wSuper d lt)  = DSub wSuper (denotReflect wSuper s d) lt

-- | Multi-step β-reduction reflects denotations unconditionally.
denotReflectMulti :: ValW v -> BetaSteps m m' -> Denotes e m' v -> Denotes e m v
denotReflectMulti _  BRefl       d = d
denotReflectMulti wv (BCons s r) d = denotReflect wv s (denotReflectMulti wv r d)

-- | Full unconditional Soundness theorem (`soundness`):
-- multi-step β-reduction induces `ℰ m ≃ ℰ m'`!
denotEquivSteps :: BetaSteps m m' -> DenEq (Den m) (Den m')
denotEquivSteps steps wv =
  ( \(MkDen d) -> MkDen (denotPreserveMulti wv d steps)
  , \(MkDen d) -> MkDen (denotReflectMulti wv steps d)
  )
```

## Changes from PLFA

- Adapted from [Soundness](https://plfa.inf.ed.ac.uk/Soundness/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part3/Soundness.lagda.md))
  by Philip Wadler, Wen Kokke, and Jeremy G. Siek (CC BY 4.0).
- **100% unconditional proofs** passing `-dcore-lint -dstg-lint` over sound
  relational `SubstAtU`/`BetaStep`: `InsertEnv`, `denotShift` (weakening),
  `denotUnshift` (strengthening), `denotSubst` (forward substitution),
  `denotSubstReflect` (backward substitution expansion), `betaPres`,
  `betaReflect`, `denotPreserve`, `denotPreserveMulti`, `denotReflect`,
  `denotReflectMulti`, and **`denotEquivSteps :: BetaSteps m m' -> DenEq (Den m) (Den m')`**!
- Uses single-variable relational `SubstAtU` rather than functional simultaneous
  `substU` (tracked separately in `R13_SubstSingleUOpenEq.hs`).
