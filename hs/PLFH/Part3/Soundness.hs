-- Generated from content/part3/Soundness.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE AllowAmbiguousTypes, DependentTypes #-}
{-# LINE 42 "content/part3/Soundness.md" #-}
module PLFH.Part3.Soundness
  ( EnvRen
  , extEnvRen
  , denotRename
  , EnvRenBack
  , shiftEnvRenBack
  , extEnvRenBack
  , denotRenameReflect
  , EnvSubst
  , extEnvSubst
  , denotSubst
  , InsertEnv (..)
  , SingleSubAt (..)
  , SubstReflRes (..)
  , denotSubstReflect
  , betaPres
  , betaReflect
  , denotPreserve
  , denotPreserveMulti
  , denotReflectW
  , denotReflect
  , denotReflectMultiW
  , denotEquivStepsW
  , denotEquivSteps
  ) where

import Data.Kind (Type)
import HaskLib.Nat (Nat (..))
import PLFH.Part2.Confluence (betaTargetW)
import PLFH.Part2.Substitution
  ( HasFin (..)
  , RenW
  , Rename
  , Subst
  , extRenW
  , finWToHas
  , shiftW
  )
import PLFH.Part2.Untyped
  ( BetaStep (..)
  , BetaSteps (..)
  , Fin (..)
  , FinW (..)
  , TermW (..)
  , UTerm (..)
  , extU
  , extsU
  , mkFinW
  , mkTermW
  , renameU
  , shiftFin
  , singleSubstU
  , substSingleU
  , substU
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

{-# LINE 127 "content/part3/Soundness.md" #-}
-- | A renaming `r` preserves value lookups from `e1` into `e2`.
type EnvRen (e1 :: ValEnv m) (e2 :: ValEnv n) (r :: Rename m n) =
  forall (x :: Fin m) (v :: Value). ValLookup e1 x v -> ValLookup e2 (r x) v

shiftEnvRen :: EnvRen e (VCons e u) shiftFin
shiftEnvRen = VLS

extEnvRen :: EnvRen e1 e2 r -> EnvRen (VCons e1 u) (VCons e2 u) (extU r)
extEnvRen _  VLZ      = VLZ
extEnvRen er (VLS lk) = VLS (er lk)

-- | Forward weakening of denotations under simultaneous renaming (`rename-pres`).
denotRename :: forall (m n :: Nat) (e1 :: ValEnv m) (e2 :: ValEnv n) (r :: Rename m n) (t :: UTerm m) (v :: Value).
               EnvRen e1 e2 r -> Denotes e1 t v -> Denotes e2 (renameU r t) v
denotRename er (DVar lk)           = DVar (er lk)
denotRename er (DElim wv d1 d2)    = DElim wv (denotRename er d1) (denotRename er d2)
denotRename er (DIntro d)          = DIntro (denotRename (extEnvRen er) d)
denotRename _  DBot                = DBot
denotRename er (DJoin w1 w2 d1 d2) = DJoin w1 w2 (denotRename er d1) (denotRename er d2)
denotRename er (DSub wv d lt)      = DSub wv (denotRename er d) lt

-- | Backward lookup reflection along a renaming `r`.
type EnvRenBack (e1 :: ValEnv m) (e2 :: ValEnv n) (r :: Rename m n) =
  forall (x :: Fin m) (v :: Value). FinW x -> ValLookup e2 (r x) v -> ValLookup e1 x v

shiftEnvRenBack :: EnvRenBack e (VCons e u) shiftFin
shiftEnvRenBack _ (VLS lk) = lk

extEnvRenBack :: EnvRenBack e1 e2 r -> EnvRenBack (VCons e1 u) (VCons e2 u) (extU r)
extEnvRenBack _  WFZ      VLZ      = VLZ
extEnvRenBack eb (WFS fx) (VLS lk) = VLS (eb fx lk)

-- | Strengthening of denotations under simultaneous renaming (`rename-reflect`).
denotRenameReflect :: forall (m n :: Nat) (e1 :: ValEnv m) (e2 :: ValEnv n) (r :: Rename m n) (t :: UTerm m) (v :: Value).
                      EnvRenBack e1 e2 r -> TermW t -> Denotes e2 (renameU r t) v -> Denotes e1 t v
denotRenameReflect _  _            DBot                = DBot
denotRenameReflect eb wt           (DJoin w1 w2 d1 d2) =
  DJoin w1 w2 (denotRenameReflect @m @n @e1 @e2 @r eb wt d1) (denotRenameReflect @m @n @e1 @e2 @r eb wt d2)
denotRenameReflect eb wt           (DSub wSuper d lt)  =
  DSub wSuper (denotRenameReflect @m @n @e1 @e2 @r eb wt d) lt
denotRenameReflect eb (WVar fx)    (DVar lk)           = DVar (eb fx lk)
denotRenameReflect eb (WApp wl wr) (DElim wArg d1 d2)  =
  DElim wArg (denotRenameReflect @m @n @e1 @e2 @r eb wl d1) (denotRenameReflect @m @n @e1 @e2 @r eb wr d2)
denotRenameReflect eb (WLam wb)    (DIntro d)          =
  DIntro (denotRenameReflect @(Succ m) @(Succ n) @_ @_ @(extU r) (extEnvRenBack eb) wb d)

{-# LINE 188 "content/part3/Soundness.md" #-}
-- | A simultaneous substitution `p` respects environments `e1` and `e2`.
type EnvSubst (e1 :: ValEnv m) (e2 :: ValEnv n) (p :: Subst m n) =
  forall (x :: Fin m) (v :: Value). ValLookup e1 x v -> Denotes e2 (p x) v

extEnvSubst :: EnvSubst e1 e2 p -> EnvSubst (VCons e1 u) (VCons e2 u) (extsU p)
extEnvSubst _  VLZ      = DVar VLZ
extEnvSubst es (VLS lk) = denotRename shiftEnvRen (es lk)

-- | Forward simultaneous substitution lemma (`subst-pres`).
denotSubst :: forall (m n :: Nat) (e1 :: ValEnv m) (e2 :: ValEnv n) (p :: Subst m n) (t :: UTerm m) (v :: Value).
              EnvSubst e1 e2 p -> Denotes e1 t v -> Denotes e2 (substU p t) v
denotSubst es (DVar lk)           = es lk
denotSubst es (DElim wv d1 d2)    = DElim wv (denotSubst es d1) (denotSubst es d2)
denotSubst es (DIntro d)          = DIntro (denotSubst (extEnvSubst es) d)
denotSubst _  DBot                = DBot
denotSubst es (DJoin w1 w2 d1 d2) = DJoin w1 w2 (denotSubst es d1) (denotSubst es d2)
denotSubst es (DSub wv d lt)      = DSub wv (denotSubst es d) lt

singleEnvSubst :: Denotes e w u -> EnvSubst (VCons e u) e (singleSubstU w)
singleEnvSubst dw VLZ      = dw
singleEnvSubst _  (VLS lk) = DVar lk

-- | Unconditional β-redex preservation.
betaPres :: Denotes (VCons e u) b v -> Denotes e w u -> Denotes e (substSingleU b w) v
betaPres db dw = denotSubst (singleEnvSubst dw) db

renameFinW :: forall m n (r :: Rename m n) (x :: Fin m).
              RenW @m @n r -> FinW x -> FinW (r x)
renameFinW rw fx = case finWToHas fx of
  MkHasFin x -> case rw x of MkHasFin y -> mkFinW y

renameTermW :: forall m n (r :: Rename m n) (t :: UTerm m).
               RenW @m @n r -> TermW t -> TermW (renameU r t)
renameTermW rw (WVar fx)    = WVar (renameFinW @m @n @r rw fx)
renameTermW rw (WLam wb)    = WLam (renameTermW @(Succ m) @(Succ n) @(extU r) (extRenW @m @n @r rw) wb)
renameTermW rw (WApp wl wm) = WApp (renameTermW @m @n @r rw wl) (renameTermW @m @n @r rw wm)

shiftTermW :: forall (n :: Nat) (t :: UTerm n). TermW t -> TermW (renameU shiftFin t)
shiftTermW = renameTermW @n @(Succ n) @shiftFin (shiftW @n)

-- | Inserting a single value `u` at de Bruijn index `c` into `e` yields `e'`.
type InsertEnv :: forall (n :: Nat). Fin (Succ n) -> ValEnv n -> Value -> ValEnv (Succ n) -> Type
data InsertEnv c e u e' where
  IEZ :: InsertEnv FZ e u (VCons e u)
  IES :: InsertEnv c e u e' -> InsertEnv (FS c) (VCons e w) u (VCons e' w)

-- | Witness that `p` is `singleSubstU w` lifted under binders to cutoff `c`.
type SingleSubAt :: forall (n :: Nat). Fin (Succ n) -> UTerm n -> Subst (Succ n) n -> Type
data SingleSubAt c w p where
  SSZ :: TermW w -> SingleSubAt FZ w (singleSubstU w)
  SSS :: forall (n :: Nat) (c :: Fin (Succ n)) (w :: UTerm n) (p :: Subst (Succ n) n).
         SingleSubAt c w p -> SingleSubAt (FS c) (renameU shiftFin w) (extsU p)

singleSubW :: forall (n :: Nat) (c :: Fin (Succ n)) (w :: UTerm n) (p :: Subst (Succ n) n).
              SingleSubAt c w p -> TermW w
singleSubW (SSZ ww) = ww
singleSubW (SSS ss) = shiftTermW (singleSubW ss)

evalSingleSubAt :: forall (n :: Nat) (c :: Fin (Succ n)) (w :: UTerm n) (p :: Subst (Succ n) n) (x :: Fin (Succ n)).
                   SingleSubAt c w p -> FinW x -> TermW (p x)
evalSingleSubAt (SSZ ww) WFZ      = ww
evalSingleSubAt (SSZ _)  (WFS fy) = WVar fy
evalSingleSubAt (SSS _)  WFZ      = WVar WFZ
evalSingleSubAt (SSS ss) (WFS fy) = shiftTermW (evalSingleSubAt ss fy)

-- | Existential result of backward substitution expansion: an argument value `u`,
-- an extended environment `e'`, a denotation `e ⊢ w ↓ u`, and `e' ⊢ m ↓ v`.
data SubstReflRes (c :: Fin (Succ n)) (e :: ValEnv n) (w :: UTerm n) (m :: UTerm (Succ n)) (v :: Value) where
  MkSubstRefl :: forall (n :: Nat) (c :: Fin (Succ n)) (e :: ValEnv n) (w :: UTerm n)
                        (m :: UTerm (Succ n)) (v :: Value) (u :: Value) (e' :: ValEnv (Succ n)).
                 ValW u
              -> InsertEnv c e u e'
              -> Denotes e w u
              -> Denotes e' m v
              -> SubstReflRes c e w m v

data JoinInsertRes (c :: Fin (Succ n)) (e :: ValEnv n) (u1 :: Value) (u2 :: Value)
                   (e1 :: ValEnv (Succ n)) (e2 :: ValEnv (Succ n)) where
  MkJoinInsert :: InsertEnv c e (Join u1 u2) e3
               -> EnvSub e1 e3
               -> EnvSub e2 e3
               -> JoinInsertRes c e u1 u2 e1 e2

joinInsert :: forall (n :: Nat) (c :: Fin (Succ n)) (e :: ValEnv n) (u1 u2 :: Value)
                     (e1 e2 :: ValEnv (Succ n)).
              ValW u1 -> ValW u2
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

singleSubAtVar
  :: forall (n :: Nat) (c :: Fin (Succ n)) (e :: ValEnv n) (eBot :: ValEnv (Succ n))
            (w :: UTerm n) (p :: Subst (Succ n) n) (x :: Fin (Succ n)) (v :: Value).
     ValW v
  -> SingleSubAt c w p
  -> FinW x
  -> InsertEnv c e Bot eBot
  -> Denotes e (p x) v
  -> SubstReflRes c e w (UVar x) v
singleSubAtVar _  _  _  ieBot DBot = MkSubstRefl (MkValW Bot) ieBot DBot DBot
singleSubAtVar _  ss fx ieBot (DJoin w1 w2 d1 d2) =
  case (singleSubAtVar w1 ss fx ieBot d1, singleSubAtVar w2 ss fx ieBot d2) of
    (MkSubstRefl wu1@(MkValW u1) ie1 dw1 dm1, MkSubstRefl wu2@(MkValW u2) ie2 dw2 dm2) ->
      case joinInsert wu1 wu2 ie1 ie2 of
        MkJoinInsert ie3 es1 es2 ->
          MkSubstRefl (MkValW (Join u1 u2)) ie3
            (DJoin wu1 wu2 dw1 dw2)
            (DJoin w1 w2 (envSubMono es1 dm1) (envSubMono es2 dm2))
singleSubAtVar _  ss fx ieBot (DSub wSuper d lt) =
  case singleSubAtVar wSuper ss fx ieBot d of
    MkSubstRefl wu ie dw dm -> MkSubstRefl wu ie dw (DSub wSuper dm lt)
singleSubAtVar wv (SSZ _)  WFZ      IEZ        d          =
  MkSubstRefl wv IEZ d (DVar VLZ)
singleSubAtVar _  (SSZ _)  (WFS _)  IEZ        (DVar lk)  =
  MkSubstRefl (MkValW Bot) IEZ DBot (DVar (VLS lk))
singleSubAtVar _  (SSS _)  WFZ      (IES ie)   (DVar VLZ) =
  MkSubstRefl (MkValW Bot) (IES ie) DBot (DVar VLZ)
singleSubAtVar wv (SSS ss) (WFS fy) (IES ie)   d          =
  case singleSubAtVar wv ss fy ie (denotRenameReflect @_ @_ @_ @_ @shiftFin shiftEnvRenBack (evalSingleSubAt ss fy) d) of
    MkSubstRefl wu ie' dw0 dm0 ->
      MkSubstRefl wu (IES ie')
        (denotRename @_ @_ @_ @_ @shiftFin shiftEnvRen dw0)
        (denotRename @_ @_ @_ @_ @shiftFin shiftEnvRen dm0)

-- | Backward single-variable substitution expansion (`subst-reflect`)!
denotSubstReflect
  :: forall (n :: Nat) (c :: Fin (Succ n)) (e :: ValEnv n) (eBot :: ValEnv (Succ n))
            (w :: UTerm n) (p :: Subst (Succ n) n) (m :: UTerm (Succ n)) (v :: Value).
     ValW v
  -> SingleSubAt c w p
  -> TermW m
  -> InsertEnv c e Bot eBot
  -> Denotes e (substU p m) v
  -> SubstReflRes c e w m v
denotSubstReflect wv ss (WVar fx) ieBot d = singleSubAtVar wv ss fx ieBot d
denotSubstReflect _  _  _         ieBot DBot = MkSubstRefl (MkValW Bot) ieBot DBot DBot
denotSubstReflect _  ss wm        ieBot (DJoin w1 w2 d1 d2) =
  case (denotSubstReflect w1 ss wm ieBot d1, denotSubstReflect w2 ss wm ieBot d2) of
    (MkSubstRefl wu1@(MkValW u1) ie1 dw1 dm1, MkSubstRefl wu2@(MkValW u2) ie2 dw2 dm2) ->
      case joinInsert wu1 wu2 ie1 ie2 of
        MkJoinInsert ie3 es1 es2 ->
          MkSubstRefl (MkValW (Join u1 u2)) ie3
            (DJoin wu1 wu2 dw1 dw2)
            (DJoin w1 w2 (envSubMono es1 dm1) (envSubMono es2 dm2))
denotSubstReflect _  ss wm        ieBot (DSub wSuper d lt) =
  case denotSubstReflect wSuper ss wm ieBot d of
    MkSubstRefl wu ie dw dm -> MkSubstRefl wu ie dw (DSub wSuper dm lt)
denotSubstReflect (MkValW v) ss (WApp wl wr) ieBot (DElim wArg@(MkValW vArg) d1 d2) =
  case ( denotSubstReflect (MkValW (Arr vArg v)) ss wl ieBot d1
       , denotSubstReflect wArg ss wr ieBot d2 ) of
    (MkSubstRefl wu1@(MkValW u1) ie1 dw1 dl, MkSubstRefl wu2@(MkValW u2) ie2 dw2 dr) ->
      case joinInsert wu1 wu2 ie1 ie2 of
        MkJoinInsert ie3 es1 es2 ->
          MkSubstRefl (MkValW (Join u1 u2)) ie3
            (DJoin wu1 wu2 dw1 dw2)
            (DElim wArg (envSubMono es1 dl) (envSubMono es2 dr))
denotSubstReflect wv ss (WLam wb) ieBot (DIntro dBody) =
  case unArrW wv of
    (_, wCod) -> case denotSubstReflect wCod (SSS ss) wb (IES ieBot) dBody of
      MkSubstRefl wu (IES ie) dwShifted db ->
        MkSubstRefl wu ie
          (denotRenameReflect @_ @_ @_ @_ @shiftFin shiftEnvRenBack (singleSubW ss) dwShifted)
          (DIntro db)

-- | Unconditional β-redex subject expansion.
betaReflect :: ValW v -> TermW b -> TermW w
            -> Denotes e (substSingleU b w) v
            -> Denotes e (UApp (ULam b) w) v
betaReflect wv wb ww dr = case denotSubstReflect wv (SSZ ww) wb IEZ dr of
  MkSubstRefl wu IEZ dw db -> DElim wu (DIntro db) dw

{-# LINE 375 "content/part3/Soundness.md" #-}
-- | Unconditional forward preservation under a single β-step (`preserve`).
denotPreserve :: forall (n :: Nat) (e :: ValEnv n) (m m' :: UTerm n) (v :: Value).
                 ValW v -> Denotes e m v -> BetaStep m m' -> Denotes e m' v
denotPreserve _ (DVar _) step = case step of {}
denotPreserve (MkValW v) (DElim wArg@(MkValW vArg) d1 d2) step = case step of
  XiApp1 r -> DElim wArg (denotPreserve (MkValW (Arr vArg v)) d1 r) d2
  XiApp2 r -> DElim wArg d1 (denotPreserve wArg d2 r)
  Beta     -> betaPres (lamInversion (MkValW (Arr vArg v)) d1) d2
denotPreserve wv (DIntro d) step = case step of
  XiLam r -> case unArrW wv of
    (_, wv2) -> DIntro (denotPreserve wv2 d r)
denotPreserve _ DBot _ = DBot
denotPreserve _ (DJoin w1 w2 d1 d2) r =
  DJoin w1 w2 (denotPreserve w1 d1 r) (denotPreserve w2 d2 r)
denotPreserve _ (DSub wSuper d lt) r =
  DSub wSuper (denotPreserve wSuper d r) lt

-- | Multi-step β-reduction preserves denotations unconditionally.
denotPreserveMulti :: forall (n :: Nat) (e :: ValEnv n) (m m' :: UTerm n) (v :: Value).
                      ValW v -> Denotes e m v -> BetaSteps m m' -> Denotes e m' v
denotPreserveMulti _  d BRefl       = d
denotPreserveMulti wv d (BCons s r) = denotPreserveMulti wv (denotPreserve wv d s) r

-- | Unconditional backward subject expansion under a single β-step (`reflect`)!
denotReflectW :: forall (n :: Nat) (e :: ValEnv n) (m m' :: UTerm n) (v :: Value).
                 ValW v -> TermW m -> BetaStep m m' -> Denotes e m' v -> Denotes e m v
denotReflectW wv (WApp (WLam wb) ww) Beta d = betaReflect wv wb ww d
denotReflectW _  _ (XiApp1 _) DBot = DBot
denotReflectW (MkValW v) (WApp wl _) (XiApp1 r) (DElim wArg@(MkValW vArg) d1 d2) =
  DElim wArg (denotReflectW (MkValW (Arr vArg v)) wl r d1) d2
denotReflectW _ wm s@(XiApp1 _) (DJoin w1 w2 d1 d2) =
  DJoin w1 w2 (denotReflectW w1 wm s d1) (denotReflectW w2 wm s d2)
denotReflectW _ wm s@(XiApp1 _) (DSub wSuper d lt) =
  DSub wSuper (denotReflectW wSuper wm s d) lt
denotReflectW _  _ (XiApp2 _) DBot = DBot
denotReflectW _ (WApp _ wr) (XiApp2 r) (DElim wArg d1 d2) =
  DElim wArg d1 (denotReflectW wArg wr r d2)
denotReflectW _ wm s@(XiApp2 _) (DJoin w1 w2 d1 d2) =
  DJoin w1 w2 (denotReflectW w1 wm s d1) (denotReflectW w2 wm s d2)
denotReflectW _ wm s@(XiApp2 _) (DSub wSuper d lt) =
  DSub wSuper (denotReflectW wSuper wm s d) lt
denotReflectW _  _ (XiLam _) DBot = DBot
denotReflectW wv (WLam wb) (XiLam r) (DIntro d) = case unArrW wv of
  (_, wv2) -> DIntro (denotReflectW wv2 wb r d)
denotReflectW _ wm s@(XiLam _) (DJoin w1 w2 d1 d2) =
  DJoin w1 w2 (denotReflectW w1 wm s d1) (denotReflectW w2 wm s d2)
denotReflectW _ wm s@(XiLam _) (DSub wSuper d lt) =
  DSub wSuper (denotReflectW wSuper wm s d) lt

denotReflect :: forall (n :: Nat) (e :: ValEnv n) (m' :: UTerm n) (v :: Value).
                ValW v -> foreach (m :: UTerm n) -> BetaStep m m' -> Denotes e m' v -> Denotes e m v
denotReflect wv m step d = denotReflectW wv (mkTermW m) step d

-- | Multi-step β-reduction reflects denotations unconditionally.
denotReflectMultiW :: ValW v -> TermW m -> BetaSteps m m' -> Denotes e m' v -> Denotes e m v
denotReflectMultiW _  _  BRefl       d = d
denotReflectMultiW wv wm (BCons s r) d =
  denotReflectW wv wm s (denotReflectMultiW wv (betaTargetW s wm) r d)

-- | Full unconditional Soundness theorem (`soundness`):
-- multi-step β-reduction induces `ℰ m ≃ ℰ m'`!
denotEquivStepsW :: TermW m -> BetaSteps m m' -> DenEq (Den m) (Den m')
denotEquivStepsW wm steps wv =
  ( \(MkDen d) -> MkDen (denotPreserveMulti wv d steps)
  , \(MkDen d) -> MkDen (denotReflectMultiW wv wm steps d)
  )

denotEquivSteps :: forall (n :: Nat) (m' :: UTerm n).
                   foreach (m :: UTerm n) -> BetaSteps m m' -> DenEq (Den m) (Den m')
denotEquivSteps m steps = denotEquivStepsW (mkTermW m) steps
