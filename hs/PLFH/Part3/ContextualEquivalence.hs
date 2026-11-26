-- Generated from content/part3/ContextualEquivalence.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DependentTypes, ListTuplePuns #-}
{-# LINE 42 "content/part3/ContextualEquivalence.md" #-}
module PLFH.Part3.ContextualEquivalence
  ( Terminates (..)
  , terminatesLam
  , terminatesStep
  , CtxEquiv
  , plugTermW
  , denotEqualCtxBigStepW
  , denotEqualCtxBigStep
  , denotEqualCtxEquivW
  , denotEqualCtxEquiv
  , betaCtxBigStepW
  , betaCtxBigStep
  , betaCtxEquiv
  ) where

import Data.Kind (Type)
import Data.Nat.Dependent (Nat (..))
import PLFH.Part2.BigStep (CbnTerminates (..), Env (..))
import PLFH.Part2.Untyped (BetaStep (..), BetaSteps (..), TermW (..), UTerm (..), mkTermW)
import PLFH.Part3.Adequacy (HaltsBig (..), adequacy, cbnToReduceW)
import qualified PLFH.Part3.Compositional as C
import PLFH.Part3.Compositional (UCtx (..), compositionality)
import PLFH.Part3.Denotational (Den (..), DenEq, denEqSym, denEqTrans)
import PLFH.Part3.Soundness (denotEquivStepsW)

{-# LINE 78 "content/part3/ContextualEquivalence.md" #-}
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

-- | Plugging a witnessed term into a retained context yields a witnessed term.
plugTermW :: forall (m n :: Nat) (t :: UTerm m).
             foreach (c :: UCtx m n) -> TermW t -> TermW (C.plug c t)
plugTermW CHole       wt = wt
plugTermW (CLam c)    wt = WLam (plugTermW c wt)
plugTermW (CAppL c r) wt = WApp (plugTermW c wt) (mkTermW r)
plugTermW (CAppR l c) wt = WApp (mkTermW l) (plugTermW c wt)

-- | Closed-term helper composing Soundness and Big-Step Adequacy directly.
denotEqualClosedBigStep
  :: forall (cm :: UTerm Zero) (cn :: UTerm Zero).
     TermW cm
  -> DenEq (Den cm) (Den cn)
  -> Terminates cm
  -> HaltsBig ENil cn
denotEqualClosedBigStep wcm eqC (MkTerminates cmToLam) =
  adequacy (denEqTrans (denEqSym eqC) (denotEquivStepsW wcm cmToLam))

-- | Big-step contextual termination across all closing contexts `UCtx k Zero`:
-- composes Compositionality + Soundness + Big-Step Adequacy in one line.
denotEqualCtxBigStepW
  :: forall (k :: Nat) (m :: UTerm k) (n :: UTerm k).
     TermW m
  -> foreach (c :: UCtx k Zero)
  -> DenEq (Den m) (Den n)
  -> Terminates (C.plug c m)
  -> HaltsBig ENil (C.plug c n)
denotEqualCtxBigStepW wm c eqM =
  denotEqualClosedBigStep (plugTermW c wm) (compositionality c eqM)

denotEqualCtxBigStep
  :: forall (k :: Nat) (n :: UTerm k).
     foreach (m :: UTerm k)
  -> foreach (c :: UCtx k Zero)
  -> DenEq (Den m) (Den n)
  -> Terminates (C.plug c m)
  -> HaltsBig ENil (C.plug c n)
denotEqualCtxBigStep m c eqM tm = denotEqualCtxBigStepW (mkTermW m) c eqM tm

-- | Open-Term Contextual Equivalence (`denot-equal-contex-equal`):
-- `ℰ M ≃ ℰ N` implies `M ≅ N` across every closing context `c :: UCtx k Zero`.
denotEqualCtxEquivW
  :: forall (k :: Nat) (m :: UTerm k) (n :: UTerm k).
     TermW m -> TermW n
  -> DenEq (Den m) (Den n)
  -> CtxEquiv m n
denotEqualCtxEquivW wm wn eqM c =
  let stepFwd :: Terminates (C.plug c m) -> Terminates (C.plug c n)
      stepFwd tm = case cbnToReduceW (plugTermW c wn)
                          (denotEqualCtxBigStepW wm c eqM tm) of
        MkCbnTerminates steps -> MkTerminates steps
      stepBwd :: Terminates (C.plug c n) -> Terminates (C.plug c m)
      stepBwd tn = case cbnToReduceW (plugTermW c wm)
                          (denotEqualCtxBigStepW @k @n @m wn c (denEqSym eqM) tn) of
        MkCbnTerminates steps -> MkTerminates steps
  in (stepFwd, stepBwd)

denotEqualCtxEquiv
  :: forall (k :: Nat).
     foreach (m n :: UTerm k)
  -> DenEq (Den m) (Den n)
  -> CtxEquiv m n
denotEqualCtxEquiv m n eqM = denotEqualCtxEquivW @k @m @n (mkTermW m) (mkTermW n) eqM

-- | Corollary (`beta-ctx-bigstep`): if `m —↠ n` (even for open terms),
-- then for any closing context `c`, `plug c m` terminating implies `plug c n` halts
-- under call-by-name big-step evaluation!
betaCtxBigStepW
  :: forall (k :: Nat) (m :: UTerm k) (n :: UTerm k).
     TermW m
  -> foreach (c :: UCtx k Zero)
  -> BetaSteps m n
  -> Terminates (C.plug c m)
  -> HaltsBig ENil (C.plug c n)
betaCtxBigStepW wm c steps = denotEqualCtxBigStepW wm c (denotEquivStepsW wm steps)

betaCtxBigStep
  :: forall (k :: Nat) (n :: UTerm k).
     foreach (m :: UTerm k)
  -> foreach (c :: UCtx k Zero)
  -> BetaSteps m n
  -> Terminates (C.plug c m)
  -> HaltsBig ENil (C.plug c n)
betaCtxBigStep m c steps tm = betaCtxBigStepW (mkTermW m) c steps tm

-- | Corollary (`beta-ctx-equiv`): multi-step β-equivalent open
-- terms are contextually equivalent across all closing contexts `UCtx k Zero`.
betaCtxEquivW
  :: forall (k :: Nat) (m :: UTerm k) (n :: UTerm k).
     TermW m -> TermW n -> BetaSteps m n -> CtxEquiv m n
betaCtxEquivW wm wn steps = denotEqualCtxEquivW wm wn (denotEquivStepsW wm steps)

betaCtxEquiv
  :: forall (k :: Nat).
     foreach (m n :: UTerm k)
  -> BetaSteps m n
  -> CtxEquiv m n
betaCtxEquiv m n steps = betaCtxEquivW (mkTermW m) (mkTermW n) steps
