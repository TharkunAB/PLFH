-- Generated from content/part3/ContextualEquivalence.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE AllowAmbiguousTypes, DependentTypes, ListTuplePuns #-}
{-# LINE 42 "content/part3/ContextualEquivalence.md" #-}
module PLFH.Part3.ContextualEquivalence
  ( Terminates (..)
  , terminatesLam
  , terminatesStep
  , CtxEquiv
  , CbnToReduce
  , denotEqualCtxBigStep
  , denotEqualCtxEquiv
  , betaCtxBigStep
  , betaCtxEquiv
  ) where

import Data.Kind (Type)
import HaskLib.Nat (Nat (..))
import PLFH.Part2.BigStep (Env (..))
import PLFH.Part2.Untyped (BetaStep (..), BetaSteps (..), UTerm (..))
import PLFH.Part3.Adequacy (HaltsBig (..), adequacy)
import qualified PLFH.Part3.Compositional as C
import PLFH.Part3.Compositional (UCtx (..))
import PLFH.Part3.CompositionalPlug (compositionality)
import PLFH.Part3.Denotational (Den (..), DenEq, denEqSym, denEqTrans)
import PLFH.Part3.Soundness (denotEquivSteps)

{-# LINE 77 "content/part3/ContextualEquivalence.md" #-}
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

-- | Open-term contextual equivalence (`M ≅ N`): for every closing one-hole
-- context `c :: UCtx k Zero`, `plug c m` terminates iff `plug c n` terminates!
type CtxEquiv (m :: UTerm k) (n :: UTerm k) =
  foreach (c :: UCtx k Zero) ->
    ( Terminates (C.plug c m) -> Terminates (C.plug c n)
    , Terminates (C.plug c n) -> Terminates (C.plug c m)
    )

-- | Closed-term helper composing Soundness and Big-Step Adequacy directly.
denotEqualClosedBigStep
  :: forall (cm :: UTerm Zero) (cn :: UTerm Zero).
     DenEq (Den cm) (Den cn)
  -> Terminates cm
  -> HaltsBig ENil cn
denotEqualClosedBigStep eqC (MkTerminates cmToLam) =
  adequacy (denEqTrans (denEqSym eqC) (denotEquivSteps cmToLam))

-- | Unconditional big-step contextual termination across all closing contexts `UCtx k Zero`:
-- composes Compositionality + Soundness + Big-Step Adequacy in one line!
denotEqualCtxBigStep
  :: forall (k :: Nat) (m :: UTerm k) (n :: UTerm k).
     foreach (c :: UCtx k Zero)
  -> DenEq (Den m) (Den n)
  -> Terminates (C.plug c m)
  -> HaltsBig ENil (C.plug c n)
denotEqualCtxBigStep c eqM =
  denotEqualClosedBigStep @(C.plug c m) @(C.plug c n)
    (compositionality @k @Zero @m @n c eqM)

-- | Big-step to small-step termination bridge (`cbn→reduce` from BigStep).
type CbnToReduce =
  forall (u :: UTerm Zero). HaltsBig ENil u -> Terminates u

-- | Open-term Contextual Equivalence (`denot-equal-contex-equal`):
-- `ℰ M ≃ ℰ N` implies `M ≅ N` across every closing context `c :: UCtx k Zero`!
denotEqualCtxEquiv
  :: forall (k :: Nat) (m :: UTerm k) (n :: UTerm k).
     CbnToReduce
  -> DenEq (Den m) (Den n)
  -> CtxEquiv m n
denotEqualCtxEquiv cbnToRed eqM c =
  let stepFwd :: Terminates (C.plug c m) -> HaltsBig ENil (C.plug c n)
      stepFwd = denotEqualCtxBigStep @k @m @n c eqM
      stepBwd :: Terminates (C.plug c n) -> HaltsBig ENil (C.plug c m)
      stepBwd = denotEqualCtxBigStep @k @n @m c (denEqSym eqM)
  in (\tm -> cbnToRed (stepFwd tm), \tn -> cbnToRed (stepBwd tn))

-- | Unconditional corollary (`beta-ctx-bigstep`): if `m —↠ n` (even for open terms!),
-- then for any closing context `c`, `plug c m` terminating implies `plug c n` halts
-- under call-by-name big-step evaluation!
betaCtxBigStep
  :: forall (k :: Nat) (m :: UTerm k) (n :: UTerm k).
     foreach (c :: UCtx k Zero)
  -> BetaSteps m n
  -> Terminates (C.plug c m)
  -> HaltsBig ENil (C.plug c n)
betaCtxBigStep c steps = denotEqualCtxBigStep @k @m @n c (denotEquivSteps steps)

-- | Corollary (`beta-ctx-equiv`): multi-step β-equivalent open terms are
-- contextually equivalent across all closing contexts `UCtx k Zero`!
betaCtxEquiv
  :: forall (k :: Nat) (m :: UTerm k) (n :: UTerm k).
     CbnToReduce
  -> BetaSteps m n
  -> CtxEquiv m n
betaCtxEquiv cbnToRed steps =
  denotEqualCtxEquiv @k @m @n cbnToRed (denotEquivSteps steps)
