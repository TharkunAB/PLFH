---
title: "Confluence: Parallel reduction and Church-Rosser confluence"
prev: /Substitution/
next: /Denotational/
src: content/part2/Confluence.md
module: PLFH.Part2.Confluence
plfaChapter: https://plfa.inf.ed.ac.uk/Confluence/
plfaAuthors: "Philip Wadler, Wen Kokke, and Jeremy G. Siek"
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
  , omegaPar
  , Joinable (..)
  , strip
  , parConfluence
  , betasToPars
  , churchRosser
  ) where

import Data.Kind (Type)
import HaskLib.Nat (Nat (..))
import PLFH.Part2.Untyped
  ( BetaStep (..)
  , BetaSteps (..)
  , Fin (..)
  , OmegaTerm
  , SubstAtU (..)
  , UTerm (..)
  )
```

In PLFA's **Confluence** chapter, we prove the **Church-Rosser theorem** for
the untyped lambda calculus via Tait and Martin-Löf's **parallel reduction**
(`_⇛_`):

1. Define parallel reduction `Par` (`_⇛_`) and its reflexive-transitive
   closure `ParSteps` (`_⇛*_`).
2. Prove that every parallel step simulates into multi-step β-reduction
   (`parToBetas`, `parsToBetas`).
3. Prove the **Strip Lemma** (`strip`) and that **Diamond implies Confluence**
   for parallel reduction (`parConfluence`, taking the one-step diamond proof as
   an explicit premise; the unconditional one-step diamond proof remains tracked
   in `[WIP NOTICE]` below).

Every one of those structural proofs compiles cleanly with `-dcore-lint -dstg-lint`
over the promoted indexed GADT `UTerm n` and passes our `.hi` interface
soundness audit!

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

As in [Untyped](/Untyped/), `PBeta` uses deterministic relational substitution
`SubstAtU 'FZ w' b' r` with explicit `forall` binders so no unconstrained
substitution function variable can slip into the interface:

```haskell
-- | Parallel β-reduction: contract any subset of redexes simultaneously.
type Par :: forall (n :: Nat). UTerm n -> UTerm n -> Type
data Par t t' where
  PVar  :: Par ('UVar x) ('UVar x)
  PLam  :: Par b b' -> Par ('ULam b) ('ULam b')
  PApp  :: Par l l' -> Par m m' -> Par ('UApp l m) ('UApp l' m')
  PBeta :: forall (n :: Nat) (b :: UTerm ('Succ n)) (b' :: UTerm ('Succ n))
                  (w :: UTerm n) (w' :: UTerm n) (r :: UTerm n).
           Par b b' -> Par w w' -> SubstAtU 'FZ w' b' r
        -> Par ('UApp ('ULam b) w) r

-- | Reflexive-transitive closure of parallel reduction (`_⇛*_`).
type ParSteps :: forall (n :: Nat). UTerm n -> UTerm n -> Type
data ParSteps t t' where
  PSRefl :: ParSteps t t
  PSCons :: Par s t -> ParSteps t u -> ParSteps s u

psTrans :: ParSteps x y -> ParSteps y z -> ParSteps x z
psTrans PSRefl        ys = ys
psTrans (PSCons x xs) ys = PSCons x (psTrans xs ys)

-- | Every parallel reduction step is simulated by zero or more β-steps!
parToBetas :: Par m n -> BetaSteps m n
parToBetas PVar              = BRefl
parToBetas (PLam p)          = bsLam (parToBetas p)
parToBetas (PApp pl pm)      = bsTrans (bsApp1 (parToBetas pl)) (bsApp2 (parToBetas pm))
parToBetas (PBeta pb pw sub) =
  bsTrans (bsApp1 (bsLam (parToBetas pb)))
    (bsTrans (bsApp2 (parToBetas pw)) (BCons (Beta sub) BRefl))

-- | Multi-step parallel reduction embeds into multi-step β-reduction.
parsToBetas :: ParSteps m n -> BetaSteps m n
parsToBetas PSRefl       = BRefl
parsToBetas (PSCons p q) = bsTrans (parToBetas p) (parsToBetas q)

-- | Concrete parallel reduction step: Ω ⇛ Ω.
omegaPar :: Par OmegaTerm OmegaTerm
omegaPar = PBeta (PApp PVar PVar) (PLam (PApp PVar PVar)) (SUApp SUEq SUEq)
```

## Joinability, Strip Lemma, and Confluence from Diamond

```haskell
-- | Two terms `m1` and `m2` are joinable under `rel` if they share a common reduct `n`.
type Joinable :: forall (n :: Nat). (UTerm n -> UTerm n -> Type) -> UTerm n -> UTerm n -> Type
data Joinable rel m1 m2 where
  Join :: rel m1 k -> rel m2 k -> Joinable rel m1 m2

-- | Strip Lemma: given the diamond property for `Par`, one `Par` step commutes
-- with any sequence of `ParSteps`!
strip :: forall (n :: Nat) (m :: UTerm n) (n1 :: UTerm n) (n2 :: UTerm n).
         (forall (a :: UTerm n) (b :: UTerm n) (c :: UTerm n).
            Par a b -> Par a c -> Joinable Par b c)
      -> Par m n1 -> ParSteps m n2 -> Joinable ParSteps n1 n2
strip _       p1 PSRefl         = Join PSRefl (PSCons p1 PSRefl)
strip diamond p1 (PSCons p2 ps) = case diamond p1 p2 of
  Join q1 q2 -> case strip diamond q2 ps of
    Join r1 r2 -> Join (PSCons q1 r1) r2

-- | Confluence of parallel reduction from the diamond property!
parConfluence :: forall (n :: Nat) (l :: UTerm n) (m1 :: UTerm n) (m2 :: UTerm n).
                 (forall (a :: UTerm n) (b :: UTerm n) (c :: UTerm n).
                    Par a b -> Par a c -> Joinable Par b c)
              -> ParSteps l m1 -> ParSteps l m2 -> Joinable ParSteps m1 m2
parConfluence _       PSRefl         ps2 = Join ps2 PSRefl
parConfluence diamond (PSCons p1 q1) ps2 = case strip diamond p1 ps2 of
  Join r1 r2 -> case parConfluence diamond q1 r1 of
    Join s1 s2 -> Join s1 (psTrans r2 s2)

-- | Lift a one-step embedding `BetaStep -> Par` to multi-step reduction.
betasToPars :: forall (n :: Nat) (m1 :: UTerm n) (m2 :: UTerm n).
               (forall (a :: UTerm n) (b :: UTerm n). BetaStep a b -> Par a b)
            -> BetaSteps m1 m2 -> ParSteps m1 m2
betasToPars _   BRefl        = PSRefl
betasToPars b2p (BCons s bs) = PSCons (b2p s) (betasToPars b2p bs)

-- | Church-Rosser Confluence for full β-reduction (`_—↠_`),
-- given `betaToPar` and the one-step diamond property for `Par`!
churchRosser :: forall (n :: Nat) (l :: UTerm n) (m1 :: UTerm n) (m2 :: UTerm n).
                (forall (a :: UTerm n) (b :: UTerm n). BetaStep a b -> Par a b)
             -> (forall (a :: UTerm n) (b :: UTerm n) (c :: UTerm n).
                   Par a b -> Par a c -> Joinable Par b c)
             -> BetaSteps l m1 -> BetaSteps l m2 -> Joinable BetaSteps m1 m2
churchRosser b2p diamond bs1 bs2 =
  case parConfluence diamond (betasToPars b2p bs1) (betasToPars b2p bs2) of
    Join ps1 ps2 -> Join (parsToBetas ps1) (parsToBetas ps2)
```

## Remaining Church-Rosser ingredients (`par-refl`, `beta-par`, `par-diamond`)

```{.haskell .wip}
-- Intended reflexivity & β-embedding over retained `UTerm n`:
parRefl :: forall (n :: Nat). foreach (m :: UTerm n) -> Par m m
parRefl (UVar _)   = PVar
parRefl (ULam b)   = PLam (parRefl b)
parRefl (UApp l m) = PApp (parRefl l) (parRefl m)
```

<div class="wip-notice">
<strong>[WIP NOTICE — Reflexivity &amp; Diamond of Parallel Reduction (R03/R11/R13)]</strong>
Three final ingredients connect <code>parConfluence</code> to unconditional
Church-Rosser confluence for <code>BetaSteps</code>:
<ul>
  <li><code>parRefl :: foreach (m :: UTerm n) -&gt; Par m m</code> (and
      <code>betaToPar</code>): while indexed GADTs whose constructors refine a
      return index (like <code>DeBruijn.Term</code>) now support retained
      <code>foreach</code> matching, the non-uniform nested datatype
      <code>UTerm n</code> (where every constructor returns uniform
      <code>UTerm n</code> and <code>ULam :: UTerm ('Succ n) -&gt; UTerm n</code>
      shifts the parameter) fails both <code>case m of</code>
      (<code>GHC-83865</code>) and direct equations (<code>GHC-83605</code>).
      See <a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R03_NestedDatatypeForEach.hs"><code>reproducers/R03_NestedDatatypeForEach.hs</code></a>.</li>
  <li><code>substCommute</code> &amp; <code>parDiamond</code> (Takahashi's
      complete development and substitution commutation): wait on
      <strong>R13/R16</strong>
      (<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_SubstSingleUOpenEq.hs"><code>R13_SubstSingleUOpenEq.hs</code></a>)
      and <strong>R11</strong>
      (<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R11_ExistentialNestedGadtCoreLint.hs"><code>R11_ExistentialNestedGadtCoreLint.hs</code></a>).</li>
</ul>
</div>

## Changes from PLFA

- Adapted from [Confluence](https://plfa.inf.ed.ac.uk/Confluence/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/Confluence.lagda.md))
  by Philip Wadler, Wen Kokke, and Jeremy G. Siek (CC BY 4.0).
- Checked direct ports of `bsTrans`/`bsApp1`/`bsApp2`/`bsLam`, `Par`,
  `ParSteps`, `parToBetas`, `parsToBetas`, `omegaPar`, `Joinable`, `strip`,
  `parConfluence`, and `churchRosser` over promoted `UTerm n`.
- Uses deterministic relational `SubstAtU` in `PBeta` (matching
  `Untyped.BetaStep.Beta`) so no unconstrained `substSingleU` type variable is
  introduced in `Confluence.hi`.
- Marked `parRefl`, `betaToPar`, and the unconditional one-step `parDiamond`
  proof with `[WIP NOTICE]` tracing directly back to our tracked R03, R11, and
  R13 reproducers.
