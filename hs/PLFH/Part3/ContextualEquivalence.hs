-- Generated from content/part3/ContextualEquivalence.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE AllowAmbiguousTypes, DependentTypes, ListTuplePuns #-}
{-# LINE 42 "content/part3/ContextualEquivalence.md" #-}
module PLFH.Part3.ContextualEquivalence
  ( Terminates (..)
  , terminatesLam
  , terminatesStep
  , CtxEquiv
  , plugTermW
  , denotEqualCtxBigStep
  , denotEqualCtxEquivW
  , denotEqualCtxEquiv
  , betaCtxBigStep
  , betaCtxEquiv
  ) where

import Data.Kind (Type)
import HaskLib.Nat (Nat (..))
import PLFH.Part2.BigStep (CbnTerminates (..), Env (..))
import PLFH.Part2.Confluence (TermW (..), mkTermW)
import PLFH.Part2.Untyped (BetaStep (..), BetaSteps (..), UTerm (..))
import PLFH.Part3.Adequacy (HaltsBig (..), adequacy, cbnToReduceW)
import qualified PLFH.Part3.Compositional as C
import PLFH.Part3.Compositional (UCtx (..))
import PLFH.Part3.CompositionalPlug (compositionality)
import PLFH.Part3.Denotational (Den (..), DenEq, denEqSym, denEqTrans)
import PLFH.Part3.Soundness (denotEquivSteps)

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

-- | Plugging a witnessed term into a retained context yields a witnessed term.
plugTermW :: forall (m n :: Nat) (t :: UTerm m).
             foreach (c :: UCtx m n) -> TermW t -> TermW (C.plug c t)
plugTermW CHole       = \wt -> wt
plugTermW (CLam c)    = \wt -> WLam (plugTermW @m @(Succ n) @t c wt)
plugTermW (CAppL c r) = \wt -> WApp (plugTermW @m @n @t c wt) (mkTermW r)
plugTermW (CAppR l c) = \wt -> WApp (mkTermW l) (plugTermW @m @n @t c wt)

-- | Unconditional Open-Term Contextual Equivalence (`denot-equal-contex-equal`):
-- `ℰ M ≃ ℰ N` implies `M ≅ N` across every closing context `c :: UCtx k Zero`!
denotEqualCtxEquivW
  :: forall (k :: Nat) (m :: UTerm k) (n :: UTerm k).
     TermW m -> TermW n
  -> DenEq (Den m) (Den n)
  -> CtxEquiv m n
denotEqualCtxEquivW wm wn eqM c =
  let stepFwd :: Terminates (C.plug c m) -> Terminates (C.plug c n)
      stepFwd tm = case cbnToReduceW (plugTermW @k @Zero @n c wn)
                          (denotEqualCtxBigStep @k @m @n c eqM tm) of
        MkCbnTerminates steps -> MkTerminates steps
      stepBwd :: Terminates (C.plug c n) -> Terminates (C.plug c m)
      stepBwd tn = case cbnToReduceW (plugTermW @k @Zero @m c wm)
                          (denotEqualCtxBigStep @k @n @m c (denEqSym eqM) tn) of
        MkCbnTerminates steps -> MkTerminates steps
  in (stepFwd, stepBwd)

denotEqualCtxEquiv
  :: forall (k :: Nat).
     foreach (m n :: UTerm k)
  -> DenEq (Den m) (Den n)
  -> CtxEquiv m n
denotEqualCtxEquiv m n eqM = denotEqualCtxEquivW @k @m @n (mkTermW m) (mkTermW n) eqM

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

-- | Unconditional Corollary (`beta-ctx-equiv`): multi-step β-equivalent open
-- terms are contextually equivalent across all closing contexts `UCtx k Zero`!
betaCtxEquivW
  :: forall (k :: Nat) (m :: UTerm k) (n :: UTerm k).
     TermW m -> TermW n -> BetaSteps m n -> CtxEquiv m n
betaCtxEquivW wm wn steps = denotEqualCtxEquivW wm wn (denotEquivSteps steps)

betaCtxEquiv
  :: forall (k :: Nat).
     foreach (m n :: UTerm k)
  -> BetaSteps m n
  -> CtxEquiv m n
betaCtxEquiv m n steps = betaCtxEquivW @k @m @n (mkTermW m) (mkTermW n) steps
