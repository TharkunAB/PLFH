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
{-# LANGUAGE AllowAmbiguousTypes, DependentTypes, ListTuplePuns #-}
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
```

## Termination and the contextual equivalence theorem

With all three core pillars of Part 3—**`Compositional.compositionality`**
(over arbitrary one-hole contexts `UCtx k Zero` and `C.plug`),
**`Soundness.denotEquivSteps`**, and **`Adequacy.adequacy`**—proved
**unconditionally**, **`denotEqualCtxBigStep`** composes all three in **one
line** with zero unproved premises! Then **`denotEqualCtxEquiv`** derives full
open-term contextual equivalence `CtxEquiv m n` (`M ≅ N`) parameterized only by
`CbnToReduce` (`cbn→reduce` from [BigStep](/BigStep/)):

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
```

<div class="wip-notice">
<strong>[WIP NOTICE — Discharging <code>CbnToReduce</code> (<code>cbn→reduce</code>)]</strong>
All three Part 3 pillars—<code>Compositional.compositionality</code> over
arbitrary <code>UCtx k Zero</code> / <code>plug</code>,
<code>Soundness.denotEquivSteps</code>, and <code>Adequacy.adequacy</code>—are
discharged <strong>unconditionally</strong> in <code>denotEqualCtxBigStep</code>
and <code>denotEqualCtxEquiv</code>! Only the single big-step → small-step
bridge <code>CbnToReduce</code> (<code>BigStep.cbn→reduce</code>) remains
parameterized until the simultaneous σ-calculus substitution laws in
<a href="/Substitution/">Substitution</a> are completed.
</div>

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
  `foreach (c :: UCtx k Zero)` and `C.plug`), unconditional
  `denotEqualCtxBigStep` & `betaCtxBigStep` (discharging Compositionality,
  Soundness, and Big-Step Adequacy unconditionally), and `denotEqualCtxEquiv`
  (parameterized only by `CbnToReduce`), with zero promoted-constructor ticks.
