-- Generated from content/part3/ContextualEquivalence.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE AllowAmbiguousTypes, DataKinds, EmptyCase, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
{-# LINE 15 "content/part3/ContextualEquivalence.md" #-}
module PLFH.Part3.ContextualEquivalence
  ( Terminates (..)
  , SoundnessProp
  , AdequacyProp
  , denotEqualTerminates
  , denotEqualCtxEquiv
  ) where

import Data.Kind (Type)
import HaskLib.Size (Size (..))
import PLFH.Part2.Untyped (BetaSteps (..), UTerm (..))
import PLFH.Part3.Denotational (Den (..), DenEq, denEqSym, denEqTrans)

{-# LINE 45 "content/part3/ContextualEquivalence.md" #-}
-- | A term terminates if full β-reduction reaches a lambda abstraction.
type Terminates :: forall (n :: Size). UTerm n -> Type
data Terminates m where
  MkTerminates :: BetaSteps m ('ULam b) -> Terminates m

-- | Soundness property: multi-step β-reduction preserves and reflects denotations.
type SoundnessProp =
  forall (n :: Size) (t :: UTerm n) (t' :: UTerm n).
    BetaSteps t t' -> DenEq (Den t) (Den t')

-- | Adequacy property: a closed term denotationally equal to a lambda terminates.
type AdequacyProp =
  forall (u :: UTerm 'Zero) (b :: UTerm ('Succ 'Zero)).
    DenEq (Den u) (Den ('ULam b)) -> Terminates u

-- | One direction (`denot-equal-terminates`): if `ℰ (C[M]) ≃ ℰ (C[N])` and
-- `C[M]` terminates (for closed plugged programs `cm`, `cn`), then `C[N]` terminates.
denotEqualTerminates
  :: forall (cm :: UTerm 'Zero) (cn :: UTerm 'Zero).
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
  :: forall (cm :: UTerm 'Zero) (cn :: UTerm 'Zero).
     SoundnessProp
  -> AdequacyProp
  -> DenEq (Den cm) (Den cn)
  -> (Terminates cm -> Terminates cn, Terminates cn -> Terminates cm)
denotEqualCtxEquiv soundness adequacy eqC =
  ( denotEqualTerminates soundness adequacy eqC
  , denotEqualTerminates soundness adequacy (denEqSym eqC)
  )
