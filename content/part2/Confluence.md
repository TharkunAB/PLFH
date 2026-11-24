---
title: "Confluence: Parallel reduction and Church-Rosser confluence"
prev: /Substitution/
next: /Status/
src: content/part2/Confluence.md
module: PLFH.Part2.Confluence
plfaChapter: https://plfa.inf.ed.ac.uk/19.08/Confluence/
---

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures, TypeOperators #-}
module PLFH.Part2.Confluence
  ( bsTrans
  , bsApp1
  , bsApp2
  , bsLam
  , Par (..)
  , ParSteps (..)
  , psTrans
  , parToBetas
  , parsToBetas
  , Joinable (..)
  , strip
  , parConfluence
  ) where

import Data.Kind (Type)
import HaskLib.Size (Size (..))
import PLFH.Part2.Untyped
  ( BetaStep (..)
  , BetaSteps (..)
  , UTerm (..)
  , substSingleU
  )
```

In PLFA's **Confluence** chapter, we prove the **Church-Rosser theorem** for
the untyped lambda calculus via Tait and Martin-Löf's **parallel reduction**
(`_⇛_`):

1. Define parallel reduction `Par` (`_⇛_`) and its reflexive-transitive
   closure `ParSteps` (`_⇛*_`).
2. Prove that every parallel step simulates into multi-step β-reduction
   (`parToBetas`, `parsToBetas`).
3. Prove the **Strip Lemma** (`strip`) and **Confluence of parallel
   reduction** (`parConfluence`) from the diamond property!

Every one of those structural proofs compiles cleanly with `-dcore-lint -dstg-lint`
over the promoted indexed GADT `UTerm n`!

## Multi-step β-reduction congruence lemmas

```haskell
-- | Transitivity of multi-step β-reduction.
bsTrans :: BetaSteps s t -> BetaSteps t u -> BetaSteps s u
bsTrans BRefl       q = q
bsTrans (BCons s p) q = BCons s (bsTrans p q)

-- | Congruence of multi-step β-reduction in function, argument, and lambda body.
bsApp1 :: BetaSteps l l' -> BetaSteps ('UApp l m) ('UApp l' m)
bsApp1 BRefl       = BRefl
bsApp1 (BCons s p) = BCons (XiApp1 s) (bsApp1 p)

bsApp2 :: BetaSteps m m' -> BetaSteps ('UApp l m) ('UApp l m')
bsApp2 BRefl       = BRefl
bsApp2 (BCons s p) = BCons (XiApp2 s) (bsApp2 p)

bsLam :: BetaSteps b b' -> BetaSteps ('ULam b) ('ULam b')
bsLam BRefl       = BRefl
bsLam (BCons s p) = BCons (XiLam s) (bsLam p)
```

## Parallel reduction (`_⇛_`) and embedding into `_—↠_`

```haskell
-- | Parallel β-reduction: contract any subset of redexes simultaneously.
type Par :: forall (n :: Size). UTerm n -> UTerm n -> Type
data Par t t' where
  PVar  :: Par ('UVar x) ('UVar x)
  PLam  :: Par b b' -> Par ('ULam b) ('ULam b')
  PApp  :: Par l l' -> Par m m' -> Par ('UApp l m) ('UApp l' m')
  PBeta :: Par b b' -> Par w w' -> Par ('UApp ('ULam b) w) (substSingleU b' w')

-- | Reflexive-transitive closure of parallel reduction (`_⇛*_`).
type ParSteps :: forall (n :: Size). UTerm n -> UTerm n -> Type
data ParSteps t t' where
  PSRefl :: ParSteps t t
  PSCons :: Par s t -> ParSteps t u -> ParSteps s u

psTrans :: ParSteps x y -> ParSteps y z -> ParSteps x z
psTrans PSRefl        ys = ys
psTrans (PSCons x xs) ys = PSCons x (psTrans xs ys)

-- | Every parallel reduction step is simulated by zero or more β-steps!
parToBetas :: Par m n -> BetaSteps m n
parToBetas PVar          = BRefl
parToBetas (PLam p)      = bsLam (parToBetas p)
parToBetas (PApp pl pm)  = bsTrans (bsApp1 (parToBetas pl)) (bsApp2 (parToBetas pm))
parToBetas (PBeta pb pw) =
  bsTrans (bsApp1 (bsLam (parToBetas pb)))
    (bsTrans (bsApp2 (parToBetas pw)) (BCons Beta BRefl))

-- | Multi-step parallel reduction embeds into multi-step β-reduction.
parsToBetas :: ParSteps m n -> BetaSteps m n
parsToBetas PSRefl       = BRefl
parsToBetas (PSCons p q) = bsTrans (parToBetas p) (parsToBetas q)
```

## Joinability, Strip Lemma, and Confluence from Diamond

```haskell
-- | Two terms `m1` and `m2` are joinable under `rel` if they share a common reduct `n`.
type Joinable :: forall (n :: Size). (UTerm n -> UTerm n -> Type) -> UTerm n -> UTerm n -> Type
data Joinable rel m1 m2 where
  Join :: rel m1 k -> rel m2 k -> Joinable rel m1 m2

-- | Strip Lemma: given the diamond property for `Par`, one `Par` step commutes
-- with any sequence of `ParSteps`!
strip :: forall (n :: Size) (m :: UTerm n) (n1 :: UTerm n) (n2 :: UTerm n).
         (forall (a :: UTerm n) (b :: UTerm n) (c :: UTerm n).
            Par a b -> Par a c -> Joinable Par b c)
      -> Par m n1 -> ParSteps m n2 -> Joinable ParSteps n1 n2
strip _       p1 PSRefl         = Join PSRefl (PSCons p1 PSRefl)
strip diamond p1 (PSCons p2 ps) = case diamond p1 p2 of
  Join q1 q2 -> case strip diamond q2 ps of
    Join r1 r2 -> Join (PSCons q1 r1) r2

-- | Confluence of parallel reduction from the diamond property!
parConfluence :: forall (n :: Size) (l :: UTerm n) (m1 :: UTerm n) (m2 :: UTerm n).
                 (forall (a :: UTerm n) (b :: UTerm n) (c :: UTerm n).
                    Par a b -> Par a c -> Joinable Par b c)
              -> ParSteps l m1 -> ParSteps l m2 -> Joinable ParSteps m1 m2
parConfluence _       PSRefl         ps2 = Join ps2 PSRefl
parConfluence diamond (PSCons p1 q1) ps2 = case strip diamond p1 ps2 of
  Join r1 r2 -> case parConfluence diamond q1 r1 of
    Join s1 s2 -> Join s1 (psTrans r2 s2)
```

## Remaining Church-Rosser ingredients (`par-refl`, `beta-par`, `par-diamond`)

<div class="wip-notice">
<strong>[WIP NOTICE — Reflexivity &amp; Diamond of Parallel Reduction (R03/R11/R13)]</strong>
Three final ingredients connect <code>parConfluence</code> to unconditional
Church-Rosser confluence for <code>BetaSteps</code>:
<ul>
  <li><code>parRefl :: foreach (m :: UTerm n) -&gt; Par m m</code> (and
      <code>betaToPar :: BetaStep m n -&gt; Par m n</code>, which calls
      <code>parRefl</code> on the unreduced side of <code>XiApp1</code>/<code>XiApp2</code>):
      blocked by <strong>R03</strong> (<code>foreach</code> over indexed GADT
      <code>UTerm n</code>, same frontier as <a href="/DeBruijn/">DeBruijn</a>).</li>
  <li><code>substCommute</code> &amp; <code>parDiamond</code> (Takahashi's
      complete development and substitution commutation for <code>substSingleU</code>):
      blocked by <strong>R13/R16</strong> (open equations for GADT-indexed
      substitution <code>substU</code>) and <strong>R11</strong> (homogeneous
      coercions when matching two GADTs indexed by promoted <code>UTerm</code>,
      same frontier as <a href="/Bisimulation/">Bisimulation</a>).</li>
</ul>
</div>

## Changes from PLFA `v19.08`

- Adapted from [Confluence (v19.08)](https://plfa.inf.ed.ac.uk/19.08/Confluence/)
  ([source](https://github.com/plfa/plfa.github.io/blob/63fcbbe25ec3686ff4c6df2c5b58a96b3a2054f3/src/plfa/part2/Confluence.lagda.md)).
- Checked direct ports of `bsTrans`/`bsApp1`/`bsApp2`/`bsLam`, `Par`,
  `ParSteps`, `parToBetas`, `parsToBetas`, `Joinable`, `strip`, and
  `parConfluence` over promoted `UTerm n`.
- Marked `parRefl`, `betaToPar`, and `parDiamond` with `[WIP NOTICE]` tracing
  directly back to our tracked R03, R11, and R13 reproducers.
