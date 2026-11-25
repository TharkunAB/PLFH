---
title: "ContextualEquivalence: Denotational equality implies contextual equivalence"
prev: /Adequacy/
next: /Status/
src: content/part3/ContextualEquivalence.md
module: PLFH.Part3.ContextualEquivalence
plfaChapter: https://plfa.inf.ed.ac.uk/ContextualEquivalence/
plfaAuthors: "Philip Wadler, Wen Kokke, and Jeremy G. Siek"
---

When should a compiler optimization—such as replacing an expression `M` with an
optimized expression `N`—be considered **behaviorally valid**?

James H. Morris (1968) and Gordon Plotkin gave the gold-standard operational
definition: **contextual equivalence** (`M ≃ᶜᵗˣ N`). Two terms `M` and `N` are
contextually equivalent if, for **every** closing program context `C[_]` into
which we can plug them, `C[M]` terminates if and only if `C[N]` terminates!

### Why proving contextual equivalence directly is hard—and why Part 3 makes it easy

Proving `M ≃ᶜᵗˣ N` directly from operational semantics is notoriously difficult
because of the universal quantification over **all possible contexts `C`**.
Yet once we have our three pillars from Part 3—**Compositionality**,
**Soundness**, and **Adequacy**—the proof that **denotational equality implies
contextual equivalence** (`ℰ M ≃ ℰ N` implies `M ≃ᶜᵗˣ N`) takes only **one
line**!

Suppose `ℰ M ≃ ℰ N` and `C[M]` terminates at some lambda `λ b` (`C[M] —↠ λ b`):
1. By **Compositionality** ([Compositional](/Compositional/)), `ℰ (C[M]) ≃ ℰ (C[N])`.
2. By **Soundness** ([Soundness](/Soundness/)), `C[M] —↠ λ b` implies
   `ℰ (C[M]) ≃ ℰ (λ b)`.
3. By symmetry and transitivity of `≃`, `ℰ (C[N]) ≃ ℰ (λ b)`.
4. By **Adequacy** ([Adequacy](/Adequacy/)), since `λ b` has a non-trivial
   function denotation (`⊥ ↦ ⊥`), `C[N]` must also terminate!

And by symmetry, if `C[N]` terminates then `C[M]` terminates too!

## Imports

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
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
import PLFH.Part3.Compositional (UCtx (..), compositionality)
import PLFH.Part3.Denotational (Den (..), DenEq, denEqSym, denEqTrans)
import PLFH.Part3.Soundness (denotEquivSteps)
```

## Termination and the contextual equivalence theorem

With all four core pillars of Part 3—**`Compositional.compositionality`**
(over arbitrary one-hole contexts `UCtx k Zero` and `C.plug`),
**`Soundness.denotEquivSteps`**, **`Adequacy.adequacy`**, and
**`BigStep.cbnToReduce`**—proved **unconditionally**, **`denotEqualCtxEquiv`**
and **`betaCtxEquiv`** establish full open-term contextual equivalence
`CtxEquiv m n` (`M ≅ N`) with **zero remaining hypotheses**:

```haskell
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
  denotEqualClosedBigStep (compositionality c eqM)

-- | Plugging a witnessed term into a retained context yields a witnessed term.
plugTermW :: forall (m n :: Nat) (t :: UTerm m).
             foreach (c :: UCtx m n) -> TermW t -> TermW (C.plug c t)
plugTermW CHole       wt = wt
plugTermW (CLam c)    wt = WLam (plugTermW c wt)
plugTermW (CAppL c r) wt = WApp (plugTermW c wt) (mkTermW r)
plugTermW (CAppR l c) wt = WApp (mkTermW l) (plugTermW c wt)

-- | Unconditional Open-Term Contextual Equivalence (`denot-equal-contex-equal`):
-- `ℰ M ≃ ℰ N` implies `M ≅ N` across every closing context `c :: UCtx k Zero`!
denotEqualCtxEquivW
  :: forall (k :: Nat) (m :: UTerm k) (n :: UTerm k).
     TermW m -> TermW n
  -> DenEq (Den m) (Den n)
  -> CtxEquiv m n
denotEqualCtxEquivW wm wn eqM c =
  let stepFwd :: Terminates (C.plug c m) -> Terminates (C.plug c n)
      stepFwd tm = case cbnToReduceW (plugTermW c wn)
                          (denotEqualCtxBigStep c eqM tm) of
        MkCbnTerminates steps -> MkTerminates steps
      stepBwd :: Terminates (C.plug c n) -> Terminates (C.plug c m)
      stepBwd tn = case cbnToReduceW (plugTermW c wm)
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
betaCtxBigStep c steps = denotEqualCtxBigStep c (denotEquivSteps steps)

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
betaCtxEquiv m n steps = betaCtxEquivW (mkTermW m) (mkTermW n) steps
```

## Exercises

#### Exercise `beta-ctx-equiv` (practice)

Using `denotEquivSteps` from [Soundness](/Soundness/) together with
`denotEqualCtxBigStep`, trace how `betaCtxBigStep` proves unconditionally that
for any open terms `m —↠ n` and any closing context `c :: UCtx k Zero`,
termination of `plug c m` implies big-step halting of `plug c n`!

#### Exercise `full-abstraction` (stretch)

Our theorem proves *soundness* of denotational equality for contextual
equivalence: `ℰ M ≃ ℰ N` implies `M ≅ N`. Think about the converse
(**full abstraction**): if `M ≅ N`, must `ℰ M ≃ ℰ N`? (Hint: consider
Plotkin's famous *parallel-or* question—is there a finite table in `Value` that
no sequential λ-term can define, distinguishing two contextually equivalent terms?)

## Changes from PLFA

- Adapted from [ContextualEquivalence](https://plfa.inf.ed.ac.uk/ContextualEquivalence/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part3/ContextualEquivalence.lagda.md))
  by Philip Wadler, Wen Kokke, and Jeremy G. Siek (CC BY 4.0).
- Checked direct ports of `Terminates`, open-term `CtxEquiv` (`M ≅ N` over
  `foreach (c :: UCtx k Zero)` and `C.plug`), `plugTermW`, and **100%
  unconditional** `denotEqualCtxBigStep`, `denotEqualCtxEquiv`, `betaCtxBigStep`,
  and `betaCtxEquiv` (discharging Compositionality, Soundness, Adequacy, and
  `BigStep.cbnToReduce` with zero remaining hypotheses, zero promoted-constructor
  ticks, and zero `[WIP NOTICE]` boxes).
