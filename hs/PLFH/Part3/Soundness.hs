-- Generated from content/part3/Soundness.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE AllowAmbiguousTypes, DataKinds, EmptyCase, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
{-# LINE 15 "content/part3/Soundness.md" #-}
module PLFH.Part3.Soundness
  ( BetaPres
  , denotPreserve
  , denotPreserveMulti
  , BetaReflect
  , denotReflect
  , denotReflectMulti
  , denotEquivSteps
  ) where

import HaskLib.Nat (Nat (..))
import PLFH.Part2.Untyped (BetaStep (..), BetaSteps (..), UTerm (..))
import PLFH.Part3.Compositional (lamInversion)
import PLFH.Part3.Denotational
  ( Den (..)
  , DenEq
  , Denotes (..)
  , ValEnv (..)
  , ValW (..)
  , Value (..)
  , unArrW
  )

{-# LINE 54 "content/part3/Soundness.md" #-}
-- | Hypothesis: contracting a β-redex preserves denotations when its body and
-- argument have matching denotations (i.e. single-variable substitution).
type BetaPres =
  forall (n :: Nat) (e :: ValEnv n) (b :: UTerm ('Succ n)) (w :: UTerm n)
         (m' :: UTerm n) (u :: Value) (v :: Value).
    BetaStep ('UApp ('ULam b) w) m'
  -> Denotes ('VCons e u) b v
  -> Denotes e w u
  -> Denotes e m' v

-- | Forward preservation under a single β-step (given `BetaPres`).
denotPreserve :: BetaPres
              -> ValW v
              -> Denotes e m v
              -> BetaStep m m'
              -> Denotes e m' v
denotPreserve _  _ (DVar _)      step = case step of {}
denotPreserve bp wv@(MkValW v) (DElim wArg@(MkValW vArg) d1 d2) step = case step of
  XiApp1 r -> DElim wArg (denotPreserve bp (MkValW (Arr vArg v)) d1 r) d2
  XiApp2 r -> DElim wArg d1 (denotPreserve bp wArg d2 r)
  Beta sub -> bp (Beta sub) (lamInversion (MkValW (Arr vArg v)) d1) d2
denotPreserve bp wv (DIntro d) step = case step of
  XiLam r -> case unArrW wv of
    (_, wv2) -> DIntro (denotPreserve bp wv2 d r)
denotPreserve _  _ DBot          _    = DBot
denotPreserve bp _ (DJoin w1 w2 d1 d2) r =
  DJoin w1 w2 (denotPreserve bp w1 d1 r) (denotPreserve bp w2 d2 r)
denotPreserve bp _ (DSub wSuper d lt) r =
  DSub wSuper (denotPreserve bp wSuper d r) lt

-- | Multi-step β-reduction preserves denotations (given `BetaPres`).
denotPreserveMulti :: BetaPres
                   -> ValW v
                   -> Denotes e m v
                   -> BetaSteps m m'
                   -> Denotes e m' v
denotPreserveMulti _  _  d BRefl       = d
denotPreserveMulti bp wv d (BCons s r) = denotPreserveMulti bp wv (denotPreserve bp wv d s) r

-- | Hypothesis: expanding a β-redex reflects denotations (single-substitution expansion).
type BetaReflect =
  forall (n :: Nat) (e :: ValEnv n) (b :: UTerm ('Succ n)) (w :: UTerm n)
         (m' :: UTerm n) (v :: Value).
    BetaStep ('UApp ('ULam b) w) m'
  -> Denotes e m' v
  -> Denotes e ('UApp ('ULam b) w) v

-- | Backward subject expansion under a single β-step (given `BetaReflect`)!
denotReflect :: BetaReflect -> BetaStep m m' -> Denotes e m' v -> Denotes e m v
denotReflect br (Beta sub)   d                   = br (Beta sub) d
denotReflect _  (XiApp1 _)   DBot                = DBot
denotReflect br (XiApp1 r)   (DElim wArg d1 d2)  = DElim wArg (denotReflect br r d1) d2
denotReflect br s@(XiApp1 _) (DJoin w1 w2 d1 d2) =
  DJoin w1 w2 (denotReflect br s d1) (denotReflect br s d2)
denotReflect br s@(XiApp1 _) (DSub wSuper d lt)  = DSub wSuper (denotReflect br s d) lt
denotReflect _  (XiApp2 _)   DBot                = DBot
denotReflect br (XiApp2 r)   (DElim wArg d1 d2)  = DElim wArg d1 (denotReflect br r d2)
denotReflect br s@(XiApp2 _) (DJoin w1 w2 d1 d2) =
  DJoin w1 w2 (denotReflect br s d1) (denotReflect br s d2)
denotReflect br s@(XiApp2 _) (DSub wSuper d lt)  = DSub wSuper (denotReflect br s d) lt
denotReflect _  (XiLam _)    DBot                = DBot
denotReflect br (XiLam r)    (DIntro d)          = DIntro (denotReflect br r d)
denotReflect br s@(XiLam _)  (DJoin w1 w2 d1 d2) =
  DJoin w1 w2 (denotReflect br s d1) (denotReflect br s d2)
denotReflect br s@(XiLam _)  (DSub wSuper d lt)  = DSub wSuper (denotReflect br s d) lt

-- | Multi-step β-reduction reflects denotations (given `BetaReflect`).
denotReflectMulti :: BetaReflect -> BetaSteps m m' -> Denotes e m' v -> Denotes e m v
denotReflectMulti _  BRefl       d = d
denotReflectMulti br (BCons s r) d = denotReflect br s (denotReflectMulti br r d)

-- | Full Soundness corollary: multi-step β-reduction induces `ℰ m ≃ ℰ m'`!
denotEquivSteps :: BetaPres -> BetaReflect -> BetaSteps m m' -> DenEq (Den m) (Den m')
denotEquivSteps bp br steps wv =
  ( \(MkDen d) -> MkDen (denotPreserveMulti bp wv d steps)
  , \(MkDen d) -> MkDen (denotReflectMulti br steps d)
  )
