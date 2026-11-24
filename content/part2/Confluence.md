---
title: "Confluence: Parallel reduction and Church-Rosser confluence"
prev: /Substitution/
next: /Denotational/
src: content/part2/Confluence.md
module: PLFH.Part2.Confluence
plfaChapter: https://plfa.inf.ed.ac.uk/Confluence/
plfaAuthors: "Philip Wadler, Wen Kokke, and Jeremy G. Siek"
---

Because full β-reduction (`BetaStep` in [Untyped](/Untyped/)) can contract
redexes in any order, a single term `L` can reduce along many different paths:

```text
          L
        /   \
       *     *
      v       v
     M₁       M₂
      \       /
       *     *
        v   v
          N
```

The celebrated **Church–Rosser Theorem** (Alonzo Church and J. Barkley Rosser,
1936) guarantees that the order of reduction **never changes the final answer**:
if `L —↠ M₁` and `L —↠ M₂`, there always exists a common reduct `N` such that
`M₁ —↠ N` and `M₂ —↠ N`! As an immediate corollary, every term has **at most
one** normal form.

### Why ordinary β-reduction fails the Diamond Property

A natural first attempt is to prove the one-step **Diamond Property** directly
for `BetaStep` (`L —→ M₁` and `L —→ M₂` implies `M₁ —→ N` and `M₂ —→ N`), and
tile one-step diamonds into a big multi-step diamond. Unfortunately, **ordinary
β-reduction does *not* satisfy the one-step diamond property!**

Consider `(λ x. x x) ((λ y. y) z)`:
- Contracting the **outer** redex first duplicates the argument, producing
  `((λ y. y) z) ((λ y. y) z)`—which now needs **two** β-steps to reach `z z`!
- Contracting the **inner** redex first produces `(λ x. x x) z`, which reaches
  `z z` in just **one** β-step.

### Tait and Martin-Löf's solution: Parallel Reduction (`_⇛_`)

William Tait and Per Martin-Löf found an extraordinarily elegant way around the
duplication problem: introduce **parallel reduction** `Par` (`M ⇛ N`), which
allows contracting **any subset** (zero, one, or many!) of existing β-redexes
simultaneously in a single step! Because parallel reduction can contract both
copies of `(λ y. y) z` at once:

1. Single-step β-reduction sits inside parallel reduction (`BetaStep ⊆ Par`),
   and every parallel step decomposes into zero or more β-steps
   (`parToBetas :: Par m n -> BetaSteps m n`), so their reflexive-transitive
   closures coincide (`BetaSteps` ↔ `ParSteps`).
2. Parallel reduction **does** satisfy the one-step Diamond Property!
3. By the **Strip Lemma** (`strip`), the Diamond Property implies **Confluence**
   for `ParSteps` (`parConfluence`)—and hence full **Church–Rosser Confluence**
   for `BetaSteps` (`churchRosser`)!

## Imports

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

## Multi-step β-reduction congruence lemmas

First we establish transitivity (`bsTrans`) and structural congruence
(`bsApp1`, `bsApp2`, `bsLam`) for multi-step full β-reduction (`BetaSteps`):

```haskell
-- | Transitivity of multi-step β-reduction.
bsTrans :: BetaSteps s t -> BetaSteps t u -> BetaSteps s u
bsTrans BRefl       q = q
bsTrans (BCons s p) q = BCons s (bsTrans p q)

-- | Congruence of multi-step β-reduction in function, argument, and lambda body.
bsApp1 :: BetaSteps l l' -> BetaSteps (UApp l m) (UApp l' m)
bsApp1 BRefl       = BRefl
bsApp1 (BCons s p) = BCons (XiApp1 s) (bsApp1 p)

bsApp2 :: BetaSteps m m' -> BetaSteps (UApp l m) (UApp l m')
bsApp2 BRefl       = BRefl
bsApp2 (BCons s p) = BCons (XiApp2 s) (bsApp2 p)

bsLam :: BetaSteps b b' -> BetaSteps (ULam b) (ULam b')
bsLam BRefl       = BRefl
bsLam (BCons s p) = BCons (XiLam s) (bsLam p)
```

## Parallel reduction (`_⇛_`) and embedding into `_—↠_`

Look closely at the four constructors of `Par`:
- `PVar`: a variable reduces in parallel to itself.
- `PLam`: reduce inside a lambda body in parallel.
- `PApp`: reduce *both* function and argument in parallel.
- `PBeta`: reduce the body `b ⇛ b'` **and** the argument `w ⇛ w'` in parallel,
  and simultaneously contract the outer β-redex via `SubstAtU FZ w' b' r`!

Because `PBeta` uses deterministic relational substitution `SubstAtU FZ w' b' r`
with explicit `forall` binders, no unconstrained substitution type variable can
enter `Confluence.hi`, and `parToBetas` simulates any parallel step into a
sequence of ordinary `BetaSteps` by structural induction!

```haskell
-- | Parallel β-reduction: contract any subset of redexes simultaneously.
type Par :: forall (n :: Nat). UTerm n -> UTerm n -> Type
data Par t t' where
  PVar  :: Par (UVar x) (UVar x)
  PLam  :: Par b b' -> Par (ULam b) (ULam b')
  PApp  :: Par l l' -> Par m m' -> Par (UApp l m) (UApp l' m')
  PBeta :: forall (n :: Nat) (b :: UTerm (Succ n)) (b' :: UTerm (Succ n))
                  (w :: UTerm n) (w' :: UTerm n) (r :: UTerm n).
           Par b b' -> Par w w' -> SubstAtU FZ w' b' r
        -> Par (UApp (ULam b) w) r

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

## Joinability, Strip Lemma, and Church–Rosser Confluence

Two terms `m1` and `m2` are **joinable** under a relation `rel` (`Joinable rel m1 m2`)
if there exists a common target `k` with `rel m1 k` and `rel m2 k`.

Using this abstract definition:
1. **`strip`** (the Strip Lemma): given a one-step diamond proof for `Par`, a
   single step `Par m n1` commutes with any multi-step reduction `ParSteps m n2`
   by pasting one-step diamonds along a horizontal strip!
2. **`parConfluence`**: pasting vertical strips together via `strip` proves
   confluence for `ParSteps`!
3. **`churchRosser`**: embedding `BetaSteps` into `ParSteps` via `betasToPars`,
   joining via `parConfluence`, and translating back via `parsToBetas` proves
   Church–Rosser Confluence for full β-reduction!

```haskell
-- | Two terms `m1` and `m2` are joinable under `rel` if they share a common reduct `k`.
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

## Remaining Church–Rosser ingredients (`par-refl`, `beta-par`, `par-diamond`)

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
Church–Rosser confluence for <code>BetaSteps</code>:
<ul>
  <li><code>parRefl :: foreach (m :: UTerm n) -&gt; Par m m</code> (and
      <code>betaToPar</code>): while indexed GADTs whose constructors refine a
      return index (like <code>DeBruijn.Term</code>) support retained
      <code>foreach</code> matching, the non-uniform nested datatype
      <code>UTerm n</code> (where every constructor returns uniform
      <code>UTerm n</code> and <code>ULam :: UTerm (Succ n) -&gt; UTerm n</code>
      shifts the parameter) fails both <code>case m of</code>
      (<code>GHC-83865</code>) and direct equations (<code>GHC-83605</code>).
      See <a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R03_NestedDatatypeForEach.hs"><code>reproducers/R03_NestedDatatypeForEach.hs</code></a>.</li>
  <li><code>substCommute</code> &amp; <code>parDiamond</code> (Takahashi's
      complete development and substitution commutation): wait on
      <strong>R13/R16</strong>
      (<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_SubstSingleUOpenEq.hs"><code>R13_SubstSingleUOpenEq.hs</code></a>).</li>
</ul>
</div>

## Exercises

#### Exercise `unique-normal-form` (recommended)

Assuming `Normal m` implies `Not (BetaStep m n)` (normal forms do not reduce),
use `churchRosser` to prove that if `BetaSteps l m1` and `BetaSteps l m2` with
both `Normal m1` and `Normal m2`, then `m1 :~: m2`!

#### Exercise `join-sym` (practice)

Prove that `Joinable rel` is symmetric (`joinSym :: Joinable rel m1 m2 -> Joinable rel m2 m1`)
for any binary relation `rel`.

## Changes from PLFA

- Adapted from [Confluence](https://plfa.inf.ed.ac.uk/Confluence/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/Confluence.lagda.md))
  by Philip Wadler, Wen Kokke, and Jeremy G. Siek (CC BY 4.0).
- Checked direct ports of `bsTrans`/`bsApp1`/`bsApp2`/`bsLam`, `Par`,
  `ParSteps`, `parToBetas`, `parsToBetas`, `omegaPar`, `Joinable`, `strip`,
  `parConfluence`, `betasToPars`, and `churchRosser` over promoted `UTerm n`
  with zero promoted-constructor ticks.
- Uses deterministic relational `SubstAtU` in `PBeta` (matching
  `Untyped.BetaStep.Beta`) so no unconstrained `substSingleU` type variable is
  introduced in `Confluence.hi`.
- Marked `parRefl`, `betaToPar`, and the unconditional one-step `parDiamond`
  proof with `[WIP NOTICE]` tracing directly back to our tracked R03 and R13
  reproducers.
