---
title: "Soundness: Soundness of reduction with respect to denotational semantics"
prev: /Compositional/
next: /Adequacy/
src: content/part3/Soundness.md
module: PLFH.Part3.Soundness
plfaChapter: https://plfa.inf.ed.ac.uk/22.08/Soundness/
plfaEdition: "PLFA v22.08"
plfaAuthors: "Philip Wadler, Wen Kokke, and Jeremy G. Siek"
---

```haskell
{-# LANGUAGE AllowAmbiguousTypes, DataKinds, EmptyCase, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
module PLFH.Part3.Soundness
  ( BetaPres
  , denotPreserve
  , denotPreserveMulti
  ) where

import HaskLib.Size (Size (..))
import PLFH.Part2.Untyped (BetaStep (..), BetaSteps (..), UTerm (..))
import PLFH.Part3.Compositional (lamInversion)
import PLFH.Part3.Denotational (Denotes (..), ValEnv (..), Value (..))
```

In PLFA's **Soundness** chapter, we prove that full β-reduction preserves
(and reflects) denotations: if `M —↠ N`, then `ℰ M ≃ ℰ N`.

## Forward preservation of denotations under β-reduction

The core structural induction `preserve` (forward soundness of single-step
and multi-step β-reduction) ports directly over promoted `UTerm n`, using our
checked **`lamInversion`** theorem from [Compositional](/Compositional/) in the
`Beta` case! Because proving the single-substitution lemma `substSinglePres`
directly over `substSingleU` currently waits on R13 open equations for
GADT-indexed `substU`, we parameterize `denotPreserve` explicitly by
`BetaPres` (the β-redex substitution case) so every single structural case
(`XiApp1`, `XiApp2`, `XiLam`, `Beta`, `DBot`, `DJoin`, `DSub`, and impossible
`DVar`) is verified by GHC right now:

```haskell
-- | Hypothesis: contracting a β-redex preserves denotations when its body and
-- argument have matching denotations (i.e. single-variable substitution).
type BetaPres =
  forall (n :: Size) (e :: ValEnv n) (b :: UTerm ('Succ n)) (w :: UTerm n)
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
```

<div class="wip-notice">
<strong>[WIP NOTICE — Substitution preservation &amp; Subject expansion (R03/R13)]</strong>
Discharging <code>BetaPres</code> (via <code>substPres</code>) and
proving the reverse direction (subject expansion: <code>renameReflect</code>,
<code>substReflect</code>, and <code>reflect</code>) require:
<ul>
  <li><strong>R03:</strong> <code>foreach</code> binders and pattern refinement
      over indexed GADT terms <code>UTerm n</code> and <code>Fin n</code>
      (<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R03_ForEachGadtEquations.hs"><code>R03_ForEachGadtEquations.hs</code></a>).</li>
  <li><strong>R13/R16:</strong> Open checked equations for higher-order
      GADT-indexed <code>renameU</code> and <code>substU</code>
      (<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_LookupEnvOpenEq.hs"><code>R13_LookupEnvOpenEq.hs</code></a>,
      <a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_SubstTermOpenEq.hs"><code>R13_SubstTermOpenEq.hs</code></a>).</li>
</ul>
</div>

## Changes from PLFA `v22.08`

- Adapted from [Soundness (v22.08)](https://plfa.inf.ed.ac.uk/22.08/Soundness/)
  ([source](https://github.com/plfa/plfa.github.io/blob/e2d545f3df0db4d4206c5448735665abde02d81f/src/plfa/part3/Soundness.lagda.md))
  by Philip Wadler, Wen Kokke, and Jeremy G. Siek (CC BY 4.0).
- Checked direct structural proofs of `denotPreserve` and `denotPreserveMulti`
  (explicitly parameterized by `BetaPres`, using `lamInversion` in the `Beta`
  case).
- Marked `substPres` and subject expansion (`renameReflect`, `substReflect`,
  `reflect`) with `[WIP NOTICE]`.
