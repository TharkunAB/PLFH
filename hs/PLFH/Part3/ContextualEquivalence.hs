-- Generated from content/part3/ContextualEquivalence.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE AllowAmbiguousTypes, DataKinds, EmptyCase, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
{-# LINE 43 "content/part3/ContextualEquivalence.md" #-}
module PLFH.Part3.ContextualEquivalence
  ( Terminates (..)
  , terminatesLam
  , terminatesStep
  , SoundnessProp
  , AdequacyProp
  , denotEqualTerminates
  , denotEqualCtxEquiv
  , denotEqualCtxEquivFromSoundness
  , betaCtxEquiv
  ) where

import Data.Kind (Type)
import HaskLib.Nat (Nat (..))
import PLFH.Part2.Untyped (BetaStep (..), BetaSteps (..), UTerm (..))
import PLFH.Part3.Denotational (Den (..), DenEq, denEqSym, denEqTrans)
import PLFH.Part3.Soundness (denotEquivSteps)

{-# LINE 71 "content/part3/ContextualEquivalence.md" #-}
-- | A term terminates if full β-reduction reaches a lambda abstraction.
type Terminates :: forall (n :: Nat). UTerm n -> Type
data Terminates m where
  MkTerminates :: BetaSteps m (ULam b) -> Terminates m

-- | Every lambda abstraction terminates immediately in zero steps.
terminatesLam :: forall (n :: Nat) (b :: UTerm (Succ n)). Terminates (ULam b)
terminatesLam = MkTerminates BRefl

-- | Termination is closed under backward β-reduction.
terminatesStep :: forall (n :: Nat) (m :: UTerm n) (m' :: UTerm n).
                  BetaStep m m' -> Terminates m' -> Terminates m
terminatesStep s (MkTerminates steps) = MkTerminates (BCons s steps)

-- | Soundness property: multi-step β-reduction preserves and reflects denotations.
type SoundnessProp =
  forall (n :: Nat) (t :: UTerm n) (t' :: UTerm n).
    BetaSteps t t' -> DenEq (Den t) (Den t')

-- | Adequacy property: a closed term denotationally equal to a lambda terminates.
type AdequacyProp =
  forall (u :: UTerm Zero) (b :: UTerm (Succ Zero)).
    DenEq (Den u) (Den (ULam b)) -> Terminates u

-- | One direction (`denot-equal-terminates`): if `ℰ (C[M]) ≃ ℰ (C[N])` and
-- `C[M]` terminates (for closed plugged programs `cm`, `cn`), then `C[N]` terminates.
denotEqualTerminates
  :: forall (cm :: UTerm Zero) (cn :: UTerm Zero).
     SoundnessProp
  -> AdequacyProp
  -> DenEq (Den cm) (Den cn)
  -> Terminates cm
  -> Terminates cn
denotEqualTerminates soundness adequacy eqC (MkTerminates cmToLam) =
  adequacy (denEqTrans (denEqSym eqC) (soundness cmToLam))

-- | Both directions (`denot-equal-contex-equal`): denotational equality of
-- closed plugged contexts implies mutual termination (contextual equivalence).
denotEqualCtxEquiv
  :: forall (cm :: UTerm Zero) (cn :: UTerm Zero).
     SoundnessProp
  -> AdequacyProp
  -> DenEq (Den cm) (Den cn)
  -> (Terminates cm -> Terminates cn, Terminates cn -> Terminates cm)
denotEqualCtxEquiv soundness adequacy eqC =
  ( denotEqualTerminates soundness adequacy eqC
  , denotEqualTerminates soundness adequacy (denEqSym eqC)
  )

-- | Instantiate `SoundnessProp` unconditionally via `Soundness.denotEquivSteps`!
denotEqualCtxEquivFromSoundness
  :: forall (cm :: UTerm Zero) (cn :: UTerm Zero).
     AdequacyProp
  -> DenEq (Den cm) (Den cn)
  -> (Terminates cm -> Terminates cn, Terminates cn -> Terminates cm)
denotEqualCtxEquivFromSoundness = denotEqualCtxEquiv denotEquivSteps

-- | Corollary (`beta-ctx-equiv`): multi-step β-equivalent closed terms
-- terminate identically under any `AdequacyProp`.
betaCtxEquiv
  :: forall (cm :: UTerm Zero) (cn :: UTerm Zero).
     AdequacyProp
  -> BetaSteps cm cn
  -> (Terminates cm -> Terminates cn, Terminates cn -> Terminates cm)
betaCtxEquiv adequacy steps =
  denotEqualCtxEquivFromSoundness adequacy (denotEquivSteps steps)
