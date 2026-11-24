-- Generated from content/part3/Compositional.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE AllowAmbiguousTypes, DataKinds, EmptyCase, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, Modifiers, PolyKinds, RankNTypes, StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LINE 16 "content/part3/Compositional.md" #-}
module PLFH.Part3.Compositional
  ( LamDen (..)
  , subLamDen
  , denLamToF
  , lamInversion
  , fToDenLam
  , lamEquiv
  , lamDenCong
  , lamCong
  , AppDen (..)
  , appDenToDenApp
  , appDenCong
  , UCtx (..)
  , plug
  ) where

import Data.Kind (Type)
import HaskLib.Size (Size (..))
import PLFH.Part2.Untyped (UTerm (..))
import PLFH.Part3.Denotational
  ( Den (..)
  , DenEq
  , Denotation
  , Denotes (..)
  , Sub (..)
  , ValEnv (..)
  , Value (..)
  , denEqSym
  , denEqTrans
  , upEnv
  )

{-# LINE 62 "content/part3/Compositional.md" #-}
-- | Semantic curry operator `ℱ`: lifts a body denotation to a lambda denotation.
type LamDen :: forall (n :: Size). Denotation ('Succ n) -> ValEnv n -> Value -> Type
data LamDen d e v where
  LDIntro :: d ('VCons e v) w -> LamDen d e ('Arr v w)
  LDBot   :: LamDen d e 'Bot
  LDJoin  :: LamDen d e u -> LamDen d e v -> LamDen d e ('Join u v)

-- | Downward closure of `LamDen` under `Sub` (`sub-ℱ`).
subLamDen :: LamDen (Den b) e v -> Sub u v -> LamDen (Den b) e u
subLamDen _                     SubBot              = LDBot
subLamDen d                     SubRefl             = d
subLamDen d                     (SubJoinL l1 l2)    = LDJoin (subLamDen d l1) (subLamDen d l2)
subLamDen (LDJoin d1 _)         (SubJoinR1 lt)      = subLamDen d1 lt
subLamDen (LDJoin _ d2)         (SubJoinR2 lt)      = subLamDen d2 lt
subLamDen d                     (SubTrans _ l1 l2)  = subLamDen (subLamDen d l2) l1
subLamDen (LDIntro (MkDen d))   (SubArr lt1 lt2)    = LDIntro (MkDen (DSub (upEnv d lt1) lt2))
subLamDen (LDJoin (LDIntro (MkDen d1)) (LDIntro (MkDen d2))) SubDist =
  LDIntro (MkDen (DJoin d1 d2))

-- | Forward direction (`ℰƛ→ℱℰ`).
denLamToF :: Den ('ULam b) e v -> LamDen (Den b) e v
denLamToF (MkDen (DIntro d))    = LDIntro (MkDen d)
denLamToF (MkDen DBot)          = LDBot
denLamToF (MkDen (DJoin d1 d2)) = LDJoin (denLamToF (MkDen d1)) (denLamToF (MkDen d2))
denLamToF (MkDen (DSub d lt))   = subLamDen (denLamToF (MkDen d)) lt

-- | Lambda inversion lemma (`lambda-inversion`): if `e ⊢ λb ↓ v1 ↦ v2` then `(e, v1) ⊢ b ↓ v2`.
lamInversion :: Denotes e ('ULam b) ('Arr v1 v2) -> Denotes ('VCons e v1) b v2
lamInversion d = case denLamToF (MkDen d) of
  LDIntro (MkDen db) -> db

-- | Backward direction (`ℱℰ→ℰƛ`).
fToDenLam :: LamDen (Den b) e v -> Den ('ULam b) e v
fToDenLam (LDIntro (MkDen d)) = MkDen (DIntro d)
fToDenLam LDBot               = MkDen DBot
fToDenLam (LDJoin d1 d2)      = MkDen (DJoin (unDen (fToDenLam d1)) (unDen (fToDenLam d2)))

-- | Compositional semantic equation for lambda: `ℰ (λb) ≃ ℱ (ℰ b)`.
lamEquiv :: DenEq (Den ('ULam b)) (LamDen (Den b))
lamEquiv = (denLamToF, fToDenLam)

-- | `LamDen` respects denotational equivalence (`ℱ-cong`).
lamDenCong :: DenEq d1 d2 -> DenEq (LamDen d1) (LamDen d2)
lamDenCong eq = (go eq, go (denEqSym eq))
  where
    go :: DenEq a b -> LamDen a e v -> LamDen b e v
    go eq' (LDIntro d)    = LDIntro (fst eq' d)
    go _   LDBot          = LDBot
    go eq' (LDJoin d1 d2) = LDJoin (go eq' d1) (go eq' d2)

-- | Congruence for lambda abstraction (`lam-cong`): `ℰ b ≃ ℰ b'` implies `ℰ (λb) ≃ ℰ (λb')`.
lamCong :: DenEq (Den b) (Den b') -> DenEq (Den ('ULam b)) (Den ('ULam b'))
lamCong eq = denEqTrans lamEquiv (denEqTrans (lamDenCong eq) (denEqSym lamEquiv))

{-# LINE 120 "content/part3/Compositional.md" #-}
-- | Semantic application operator (`D1 ● D2`).
type AppDen :: forall (n :: Size). Denotation n -> Denotation n -> ValEnv n -> Value -> Type
data AppDen d1 d2 e w where
  ADBot :: Sub w 'Bot -> AppDen d1 d2 e w
  ADApp :: d1 e ('Arr v w) -> d2 e v -> AppDen d1 d2 e w

-- | Backward direction for application (`●ℰ→ℰ·`).
appDenToDenApp :: AppDen (Den l) (Den m) e v -> Den ('UApp l m) e v
appDenToDenApp (ADBot lt)                      = MkDen (DSub DBot lt)
appDenToDenApp (ADApp (MkDen d1) (MkDen d2))   = MkDen (DElim d1 d2)

-- | `AppDen` respects denotational equivalence (`●-cong`).
appDenCong :: DenEq d1 d1' -> DenEq d2 d2' -> DenEq (AppDen d1 d2) (AppDen d1' d2')
appDenCong e1 e2 = (go e1 e2, go (denEqSym e1) (denEqSym e2))
  where
    go :: DenEq a a' -> DenEq b b' -> AppDen a b e v -> AppDen a' b' e v
    go _   _   (ADBot lt)    = ADBot lt
    go e1' e2' (ADApp d1 d2) = ADApp (fst e1' d1) (fst e2' d2)

-- | One-hole term contexts taking a hole of depth `m` to a term of depth `n`.
data UCtx (m :: Size) (n :: Size) where
  CHole :: UCtx n n
  CLam  :: UCtx ('Succ m) ('Succ n) -> UCtx ('Succ m) n
  CAppL :: UCtx m n -> UTerm n -> UCtx m n
  CAppR :: UTerm n -> UCtx m n -> UCtx m n

-- | Plugging a term into a one-hole context.
plug :: UCtx m n -> UTerm m -> UTerm n
plug CHole       t = t
plug (CLam c)    t = ULam (plug c t)
plug (CAppL c r) t = UApp (plug c t) r
plug (CAppR l c) t = UApp l (plug c t)
