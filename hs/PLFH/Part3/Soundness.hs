-- Generated from content/part3/Soundness.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE AllowAmbiguousTypes, DataKinds, EmptyCase, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
{-# LINE 15 "content/part3/Soundness.md" #-}
module PLFH.Part3.Soundness
  ( BetaPres
  , denotPreserve
  , denotPreserveMulti
  ) where

import HaskLib.Nat (Nat (..))
import PLFH.Part2.Untyped (BetaStep (..), BetaSteps (..), UTerm (..))
import PLFH.Part3.Compositional (lamInversion)
import PLFH.Part3.Denotational (Denotes (..), ValEnv (..), Value (..))

{-# LINE 43 "content/part3/Soundness.md" #-}
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
              -> Denotes e m v
              -> BetaStep m m'
              -> Denotes e m' v
denotPreserve _  (DVar _)      step = case step of {}
denotPreserve bp (DElim d1 d2) step = case step of
  XiApp1 r -> DElim (denotPreserve bp d1 r) d2
  XiApp2 r -> DElim d1 (denotPreserve bp d2 r)
  Beta     -> bp Beta (lamInversion d1) d2
denotPreserve bp (DIntro d)    step = case step of
  XiLam r -> DIntro (denotPreserve bp d r)
denotPreserve _  DBot          _    = DBot
denotPreserve bp (DJoin d1 d2) r    = DJoin (denotPreserve bp d1 r) (denotPreserve bp d2 r)
denotPreserve bp (DSub d lt)   r    = DSub (denotPreserve bp d r) lt

-- | Multi-step β-reduction preserves denotations (given `BetaPres`).
denotPreserveMulti :: BetaPres
                   -> Denotes e m v
                   -> BetaSteps m m'
                   -> Denotes e m' v
denotPreserveMulti _  d BRefl       = d
denotPreserveMulti bp d (BCons s r) = denotPreserveMulti bp (denotPreserve bp d s) r
