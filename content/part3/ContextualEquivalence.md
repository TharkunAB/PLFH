---
title: "ContextualEquivalence: Denotational equality implies contextual equivalence"
prev: /Adequacy/
next: /Status/
src: content/part3/ContextualEquivalence.md
module: PLFH.Part3.ContextualEquivalence
plfaChapter: https://plfa.inf.ed.ac.uk/ContextualEquivalence/
plfaAuthors: "Philip Wadler, Wen Kokke, and Jeremy G. Siek"
---

```haskell
{-# LANGUAGE AllowAmbiguousTypes, DataKinds, EmptyCase, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
module PLFH.Part3.ContextualEquivalence
  ( Terminates (..)
  , SoundnessProp
  , AdequacyProp
  , denotEqualTerminates
  , denotEqualCtxEquiv
  , denotEqualCtxEquivFromSoundness
  ) where

import Data.Kind (Type)
import HaskLib.Nat (Nat (..))
import PLFH.Part2.Untyped (BetaSteps (..), UTerm (..))
import PLFH.Part3.Denotational (Den (..), DenEq, denEqSym, denEqTrans)
import PLFH.Part3.Soundness (denotEquivSteps)
```

In PLFA's final Part 3 chapter, **ContextualEquivalence**, we combine
**Compositionality**, **Soundness**, and **Adequacy** to prove that
denotationally equal terms are *contextually equivalent*: plugging them into
any closing context `C` produces programs that either both terminate or both
diverge.

## Termination and the contextual equivalence corollary

Now that [Soundness](/Soundness/) (`denotEquivSteps`) and big-step
[Adequacy](/Adequacy/) (`adequacyBigStep`) are both proved **unconditionally**,
`denotEqualCtxEquivFromSoundness` instantiates `SoundnessProp` directly with
`Soundness.denotEquivSteps` (parameterized only by the small-step `AdequacyProp`
bridge while big-step → small-step and `UCtx`/`plug` compositionality await
our tracked R03/R13 blockers):

```haskell
-- | A term terminates if full β-reduction reaches a lambda abstraction.
type Terminates :: forall (n :: Nat). UTerm n -> Type
data Terminates m where
  MkTerminates :: BetaSteps m ('ULam b) -> Terminates m

-- | Soundness property: multi-step β-reduction preserves and reflects denotations.
type SoundnessProp =
  forall (n :: Nat) (t :: UTerm n) (t' :: UTerm n).
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

-- | Instantiate `SoundnessProp` unconditionally via `Soundness.denotEquivSteps`!
denotEqualCtxEquivFromSoundness
  :: forall (cm :: UTerm 'Zero) (cn :: UTerm 'Zero).
     AdequacyProp
  -> DenEq (Den cm) (Den cn)
  -> (Terminates cm -> Terminates cn, Terminates cn -> Terminates cm)
denotEqualCtxEquivFromSoundness = denotEqualCtxEquiv denotEquivSteps
```

<div class="wip-notice">
<strong>[WIP NOTICE — Unconditional Contextual Equivalence over <code>UCtx</code> / <code>plug</code>]</strong>
The checked theorems above prove the exact logical reduction from
compositionality, soundness, and adequacy to contextual equivalence. Obtaining
the unconditional theorem quantified over arbitrary <code>UCtx m 'Zero</code>
with <code>plug c m</code> awaits the remaining theorem blockers tracked in
<a href="/Compositional/">Compositional</a>, <a href="/Soundness/">Soundness</a>,
<a href="/Adequacy/">Adequacy</a>, and <a href="/BigStep/">BigStep</a>.
</div>

## Changes from PLFA

- Adapted from [ContextualEquivalence](https://plfa.inf.ed.ac.uk/ContextualEquivalence/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part3/ContextualEquivalence.lagda.md))
  by Philip Wadler, Wen Kokke, and Jeremy G. Siek (CC BY 4.0).
- Checked direct ports of `Terminates`, `denotEqualTerminates`, and
  `denotEqualCtxEquiv` (explicitly parameterized by `SoundnessProp` and
  `AdequacyProp` while those upstream Part 3 theorem blockers remain open).
