---
title: "Confluence: Parallel reduction and Church-Rosser confluence"
prev: /bigstep/
next: /denotational/
src: content/part2/Confluence.md
module: PLFH.Part2.Confluence
plfaChapter: https://plfa.inf.ed.ac.uk/Confluence/
---

Because full β-reduction (`BetaStep` in [Untyped](/untyped/)) can contract
redexes in any order, a single term `L` can reduce along many different paths:

<figure class="plfh-diagram">
  <svg viewBox="0 0 260 190" width="260" height="190" role="img" aria-label="Church-Rosser diamond diagram">
    <defs>
      <marker id="cr-arrow" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
        <path d="M 0 1 L 10 5 L 0 9 z" fill="#1e293b"/>
      </marker>
    </defs>
    <text x="130" y="24" text-anchor="middle" font-family="Iosevka, monospace" font-size="16" font-weight="600" fill="#0f172a">L</text>
    <line x1="118" y1="34" x2="62" y2="80" stroke="#1e293b" stroke-width="1.6" marker-end="url(#cr-arrow)"/>
    <line x1="142" y1="34" x2="198" y2="80" stroke="#1e293b" stroke-width="1.6" marker-end="url(#cr-arrow)"/>
    <text x="76" y="54" text-anchor="middle" font-family="Iosevka, monospace" font-size="13" fill="#475569">*</text>
    <text x="184" y="54" text-anchor="middle" font-family="Iosevka, monospace" font-size="13" fill="#475569">*</text>
    <text x="48" y="100" text-anchor="middle" font-family="Iosevka, monospace" font-size="16" font-weight="600" fill="#0f172a">M₁</text>
    <text x="212" y="100" text-anchor="middle" font-family="Iosevka, monospace" font-size="16" font-weight="600" fill="#0f172a">M₂</text>
    <line x1="62" y1="112" x2="118" y2="158" stroke="#1d62c1" stroke-width="1.6" stroke-dasharray="4 3" marker-end="url(#cr-arrow)"/>
    <line x1="198" y1="112" x2="142" y2="158" stroke="#1d62c1" stroke-width="1.6" stroke-dasharray="4 3" marker-end="url(#cr-arrow)"/>
    <text x="76" y="144" text-anchor="middle" font-family="Iosevka, monospace" font-size="13" fill="#1d62c1">*</text>
    <text x="184" y="144" text-anchor="middle" font-family="Iosevka, monospace" font-size="13" fill="#1d62c1">*</text>
    <text x="130" y="178" text-anchor="middle" font-family="Iosevka, monospace" font-size="16" font-weight="600" fill="#1d62c1">N</text>
  </svg>
  <figcaption>Church-Rosser confluence: any two reduction paths from L rejoin at a common reduct N.</figcaption>
</figure>

The celebrated **Church–Rosser Theorem** (Alonzo Church and J. Barkley Rosser,
1936) guarantees that the order of reduction **never changes the final answer**:
if `L —↠ M₁` and `L —↠ M₂`, there always exists a common reduct `N` such that
`M₁ —↠ N` and `M₂ —↠ N`. As an immediate corollary, every term has **at most
one** normal form.

## Why ordinary β-reduction fails the Diamond Property

A natural first attempt is to prove the one-step **Diamond Property** directly
for `BetaStep` (`L —→ M₁` and `L —→ M₂` implies `M₁ —→ N` and `M₂ —→ N`), and
tile one-step diamonds into a big multi-step diamond. Unfortunately, **ordinary
β-reduction does *not* satisfy the one-step diamond property.**

Consider `(λ x. x x) ((λ y. y) z)`:
- Contracting the **outer** redex first duplicates the argument, producing
  `((λ y. y) z) ((λ y. y) z)`, which now needs **two** β-steps to reach `z z`.
- Contracting the **inner** redex first produces `(λ x. x x) z`, which reaches
  `z z` in just **one** β-step.

### Tait and Martin-Löf's solution: Parallel Reduction (`_⇛_`)

William Tait and Per Martin-Löf found an extraordinarily elegant way around the
duplication problem: introduce **parallel reduction** `Par` (`M ⇛ N`), which
allows contracting **any subset** (zero, one, or many) of existing β-redexes
simultaneously in a single step. Because parallel reduction can contract both
copies of `(λ y. y) z` at once:

1. Single-step β-reduction sits inside parallel reduction (`BetaStep ⊆ Par`),
   and every parallel step decomposes into zero or more β-steps
   (`parToBetas :: Par m n -> BetaSteps m n`), so their reflexive-transitive
   closures coincide (`BetaSteps` ↔ `ParSteps`).
2. Parallel reduction **does** satisfy the one-step Diamond Property.
3. By the **Strip Lemma** (`strip`), the Diamond Property implies **Confluence**
   for `ParSteps` (`parConfluence`), and hence full **Church–Rosser Confluence**
   for `BetaSteps` (`churchRosser`).

## Imports

```haskell
{-# LANGUAGE AllowAmbiguousTypes, DependentTypes #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
module PLFH.Part2.Confluence
  ( bsTrans
  , bsApp1
  , bsApp2
  , bsLam
  , Par (..)
  , FinW (..)
  , TermW (..)
  , mkFinW
  , mkTermW
  , betaTargetW
  , parRefl
  , betaToPar
  , ParSteps (..)
  , psTrans
  , parToBetas
  , parsToBetas
  , omegaPar
  , Joinable (..)
  , joinSym
  , parRename
  , ParSub
  , parSubst
  , parSubstSingle
  , parDiamondW
  , parDiamond
  , stripW
  , strip
  , parConfluenceW
  , parConfluence
  , betasToParsW
  , betasToPars
  , churchRosser
  , neutralNoBetaStep
  , normalNoBetaStep
  , normalNoBetaSteps
  , neutralPar
  , normalPar
  , normalParSteps
  , uniqueNormalForm
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import Data.Void (absurd)
import Data.Nat.Dependent (Nat (..))
import PLFH.Part1.Decidable (Not)
import PLFH.Part2.Substitution
  ( HasFin (..)
  , HasTerm (..)
  , RenW
  , Rename
  , SubW
  , Subst
  , evalSubst
  , extRenW
  , extsW
  , finWToHas
  , hasToTermW
  , renCommute
  , shiftW
  , singleW
  , substCommute
  , termWToHas
  )
import PLFH.Part2.Untyped
  ( BetaStep (..)
  , BetaSteps (..)
  , Fin (..)
  , FinW (..)
  , Neutral (..)
  , Normal (..)
  , OmegaTerm
  , TermW (..)
  , UTerm (..)
  , bsApp1
  , bsApp2
  , bsLam
  , bsTrans
  , extU
  , extsU
  , mkFinW
  , mkTermW
  , renameU
  , shiftFin
  , singleSubstU
  , substSingleU
  , substU
  )
```

## Parallel reduction (`_⇛_`) and embedding into `_—↠_`

Look closely at the four constructors of `Par`:
- `PVar`: a variable reduces in parallel to itself.
- `PLam`: reduce inside a lambda body in parallel.
- `PApp`: reduce *both* function and argument in parallel.
- `PBeta`: reduce the body `b ⇛ b'` **and** the argument `w ⇛ w'` in parallel,
  and simultaneously contract the outer β-redex directly via `substSingleU b' w'`.

Because `PBeta` uses the exact same functional `substSingleU` as `Untyped.Beta`,
`parToBetas` simulates any parallel step into a sequence of ordinary `BetaSteps`
by direct structural induction.

<div class="rule-group">
  <div class="inference-rule">
    <div class="premises">&nbsp;</div>
    <div class="conclusion">x ⇛ x</div>
    <div class="rule-name">(PVar)</div>
  </div>
  <div class="inference-rule">
    <div class="premises"><span>b ⇛ b'</span></div>
    <div class="conclusion">λ b ⇛ λ b'</div>
    <div class="rule-name">(PLam)</div>
  </div>
  <div class="inference-rule">
    <div class="premises"><span>L ⇛ L'</span><span>M ⇛ M'</span></div>
    <div class="conclusion">L · M ⇛ L' · M'</div>
    <div class="rule-name">(PApp)</div>
  </div>
  <div class="inference-rule">
    <div class="premises"><span>b ⇛ b'</span><span>W ⇛ W'</span></div>
    <div class="conclusion">(λ b) · W ⇛ b' [ W' ]</div>
    <div class="rule-name">(PBeta)</div>
  </div>
</div>

```haskell
-- | Parallel β-reduction: contract any subset of redexes simultaneously.
type Par :: forall (n :: Nat). UTerm n -> UTerm n -> Type
data Par t t' where
  PVar  :: Par (UVar x) (UVar x)
  PLam  :: Par b b' -> Par (ULam b) (ULam b')
  PApp  :: Par l l' -> Par m m' -> Par (UApp l m) (UApp l' m')
  PBeta :: forall (n :: Nat) (b b' :: UTerm (Succ n)) (w w' :: UTerm n).
           Par b b' -> Par w w' -> Par (UApp (ULam b) w) (substSingleU b' w')

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

-- | Concrete parallel reduction step: Ω ⇛ Ω.
omegaPar :: Par OmegaTerm OmegaTerm
omegaPar = PBeta (PApp PVar PVar) (PLam (PApp PVar PVar))
```

## Structural witnesses, reflexivity (`parRefl`), and β-embedding (`betaToPar`)

Every well-scoped untyped term `m :: UTerm n` reduces to itself in one parallel
step (`parRefl`), and every single β-reduction step embeds into parallel
reduction (`betaToPar`). Using `Untyped.TermW` and `Substitution.evalSubst`,
we transport structural witnesses across single β-steps (`betaTargetW`) and
parallel steps (`parTargetW`):

```haskell
substSingleW :: forall (n :: Nat) (b :: UTerm (Succ n)) (w :: UTerm n).
                TermW b -> TermW w -> TermW (substSingleU b w)
substSingleW wb ww = case (termWToHas wb, termWToHas ww) of
  (MkHasTerm b', MkHasTerm w') ->
    hasToTermW (evalSubst @(Succ n) @n @(singleSubstU w) (singleW @n w') b')

parTargetW :: Par t t' -> TermW t -> TermW t'
parTargetW PVar          (WVar fx)          = WVar fx
parTargetW (PLam pb)     (WLam wb)          = WLam (parTargetW pb wb)
parTargetW (PApp pl pm)  (WApp wl wm)       = WApp (parTargetW pl wl) (parTargetW pm wm)
parTargetW (PBeta pb pw) (WApp (WLam wb) ww) =
  substSingleW (parTargetW pb wb) (parTargetW pw ww)

betaTargetW :: BetaStep t t' -> TermW t -> TermW t'
betaTargetW (XiApp1 sl) (WApp wl wm)       = WApp (betaTargetW sl wl) wm
betaTargetW (XiApp2 sm) (WApp wl wm)       = WApp wl (betaTargetW sm wm)
betaTargetW (XiLam sb)  (WLam wb)          = WLam (betaTargetW sb wb)
betaTargetW Beta        (WApp (WLam wb) ww) = substSingleW wb ww

-- | Parallel reduction is reflexive across the non-uniform scope index `n`.
parReflW :: TermW m -> Par m m
parReflW (WVar _)     = PVar
parReflW (WLam wb)    = PLam (parReflW wb)
parReflW (WApp wl wm) = PApp (parReflW wl) (parReflW wm)

parRefl :: forall (n :: Nat). foreach (m :: UTerm n) -> Par m m
parRefl m = parReflW (mkTermW m)

-- | Every single β-step is a parallel reduction step (`—→-to-⇒`).
betaToParW :: TermW l -> BetaStep l r -> Par l r
betaToParW (WVar _)            s           = case s of {}
betaToParW (WApp wl wm)        (XiApp1 sl) = PApp (betaToParW wl sl) (parReflW wm)
betaToParW (WApp wl wm)        (XiApp2 sm) = PApp (parReflW wl) (betaToParW wm sm)
betaToParW (WLam wb)           (XiLam sb)  = PLam (betaToParW wb sb)
betaToParW (WApp (WLam wb) ww) Beta        = PBeta (parReflW wb) (parReflW ww)

betaToPar :: forall (n :: Nat) (r :: UTerm n).
             foreach (l :: UTerm n) -> BetaStep l r -> Par l r
betaToPar l s = betaToParW (mkTermW l) s

-- | Lift single-step `BetaStep -> Par` to multi-step reduction (`—↠-to-⇒*`).
betasToParsW :: TermW m1 -> BetaSteps m1 m2 -> ParSteps m1 m2
betasToParsW _  BRefl        = PSRefl
betasToParsW wm (BCons s bs) = PSCons (betaToParW wm s) (betasToParsW (betaTargetW s wm) bs)

betasToPars :: forall (n :: Nat) (m2 :: UTerm n).
               foreach (m1 :: UTerm n) -> BetaSteps m1 m2 -> ParSteps m1 m2
betasToPars m1 bs = betasToParsW (mkTermW m1) bs
```

## Parallel substitution (`parRename`, `parSubst`) and the Diamond Property (`parDiamond`)

Because `Par` uses functional `substSingleU`, the entire Tait–Martin-Löf
parallel substitution lemma reduces directly to `renCommute` and `substCommute`
from [Substitution](/substitution/):

- **`parRename`**: simultaneous renaming preserves parallel reduction (using
  `renCommute` in the `PBeta` case).
- **`parSubst` / `parSubstSingle`**: simultaneous and single-variable
  substitution preserve parallel reduction (using `substCommute` in the `PBeta`
  case).
- **`parDiamondW` / `parDiamond`**: parallel reduction satisfies the one-step
  **Diamond Property**. In the `PApp (PLam b1) w1` vs. `PBeta b2 w2` overlap,
  `parSubstSingle` closes the right edge while `PBeta` closes the left edge; in
  the `PBeta` vs. `PBeta` overlap, both targets reduce identically to
  `substSingleU b* w*`.

```haskell
-- | Two terms `m1` and `m2` are joinable under `rel` if they share a common reduct `k`.
type Joinable :: forall (n :: Nat). (UTerm n -> UTerm n -> Type) -> UTerm n -> UTerm n -> Type
data Joinable rel m1 m2 where
  Join :: rel m1 k -> rel m2 k -> Joinable rel m1 m2

-- | Joinability is symmetric for any reduction relation `rel`.
joinSym :: Joinable rel m1 m2 -> Joinable rel m2 m1
joinSym (Join p1 p2) = Join p2 p1

-- | Simultaneous renaming preserves parallel reduction (`rename-⇒`).
parRename :: forall m n (r :: Rename m n) (t t' :: UTerm m).
             RenW @m @n r -> TermW t -> Par t t' -> Par (renameU r t) (renameU r t')
parRename _  _                PVar         = PVar
parRename rw (WLam wb)        (PLam pb)    =
  PLam (parRename @(Succ m) @(Succ n) @(extU r) (extRenW @m @n @r rw) wb pb)
parRename rw (WApp wl wm)     (PApp pl pm) =
  PApp (parRename @m @n @r rw wl pl) (parRename @m @n @r rw wm pm)
parRename rw (WApp (WLam wb) ww) (PBeta pb pw) =
  case (termWToHas (parTargetW pb wb), termWToHas (parTargetW pw ww)) of
    (MkHasTerm b', MkHasTerm w') ->
      case renCommute @m @n @r rw w' b' of
        Refl -> PBeta (parRename @(Succ m) @(Succ n) @(extU r) (extRenW @m @n @r rw) wb pb)
                      (parRename @m @n @r rw ww pw)

-- | Pointwise parallel reduction between two simultaneous substitutions.
type ParSub :: forall m n. Subst m n -> Subst m n -> Type
type ParSub @m @n s1 s2 = foreach (x :: Fin m) -> Par (s1 x) (s2 x)

parSubstExts :: forall m n (s1 s2 :: Subst m n).
                SubW @m @n s1 -> ParSub @m @n s1 s2
             -> ParSub @(Succ m) @(Succ n) (extsU s1) (extsU s2)
parSubstExts _   _  FZ     = PVar
parSubstExts sw1 ps (FS x) =
  parRename @n @(Succ n) @shiftFin (shiftW @n) (hasToTermW (sw1 x)) (ps x)

-- | Simultaneous parallel substitution lemma (`subst-⇒`).
parSubst :: forall m n (s1 s2 :: Subst m n) (t t' :: UTerm m).
            SubW @m @n s1 -> SubW @m @n s2
         -> ParSub @m @n s1 s2
         -> TermW t -> Par t t'
         -> Par (substU s1 t) (substU s2 t')
parSubst _   _   ps (WVar fx)    PVar         = case finWToHas fx of MkHasFin x -> ps x
parSubst sw1 sw2 ps (WLam wb)    (PLam pb)    =
  PLam (parSubst @(Succ m) @(Succ n) @(extsU s1) @(extsU s2)
          (extsW @m @n @s1 sw1) (extsW @m @n @s2 sw2)
          (parSubstExts @m @n @s1 @s2 sw1 ps) wb pb)
parSubst sw1 sw2 ps (WApp wl wm) (PApp pl pm) =
  PApp (parSubst @m @n @s1 @s2 sw1 sw2 ps wl pl)
       (parSubst @m @n @s1 @s2 sw1 sw2 ps wm pm)
parSubst sw1 sw2 ps (WApp (WLam wb) ww) (PBeta pb pw) =
  case (termWToHas (parTargetW pb wb), termWToHas (parTargetW pw ww)) of
    (MkHasTerm b', MkHasTerm w') ->
      case substCommute @m @n @s2 sw2 w' b' of
        Refl ->
          PBeta (parSubst @(Succ m) @(Succ n) @(extsU s1) @(extsU s2)
                   (extsW @m @n @s1 sw1) (extsW @m @n @s2 sw2)
                   (parSubstExts @m @n @s1 @s2 sw1 ps) wb pb)
                (parSubst @m @n @s1 @s2 sw1 sw2 ps ww pw)

singleParSub :: forall n (w w' :: UTerm n).
                Par w w' -> ParSub @(Succ n) @n (singleSubstU w) (singleSubstU w')
singleParSub pw FZ     = pw
singleParSub _  (FS x) = parReflW (WVar (mkFinW x))

-- | Single-variable parallel substitution lemma: `Par b b'` and `Par w w'` imply
-- `Par (substSingleU b w) (substSingleU b' w')`.
parSubstSingle :: forall n (b b' :: UTerm (Succ n)) (w w' :: UTerm n).
                  TermW b -> TermW w -> TermW w'
               -> Par b b' -> Par w w'
               -> Par (substSingleU b w) (substSingleU b' w')
parSubstSingle wb ww ww' pb pw =
  case (termWToHas ww, termWToHas ww') of
    (MkHasTerm w1, MkHasTerm w2) ->
      parSubst @(Succ n) @n @(singleSubstU w) @(singleSubstU w')
        (singleW @n w1) (singleW @n w2) (singleParSub @n pw) wb pb

-- | One-step Diamond Property of parallel reduction (`par-diamond`)!
parDiamondW :: TermW m -> Par m n1 -> Par m n2 -> Joinable Par n1 n2
parDiamondW _                PVar             PVar             = Join PVar PVar
parDiamondW (WLam wb)        (PLam b1)        (PLam b2)        = case parDiamondW wb b1 b2 of
  Join q1 q2 -> Join (PLam q1) (PLam q2)
parDiamondW (WApp wl wm)     (PApp l1 m1)     (PApp l2 m2)     =
  case (parDiamondW wl l1 l2, parDiamondW wm m1 m2) of
    (Join ql1 ql2, Join qm1 qm2) -> Join (PApp ql1 qm1) (PApp ql2 qm2)
parDiamondW (WApp (WLam wb) ww) (PApp (PLam b1) w1) (PBeta b2 w2) =
  case (parDiamondW wb b1 b2, parDiamondW ww w1 w2) of
    (Join qb1 qb2, Join qw1 qw2) ->
      let wb2'   = parTargetW b2 wb
          ww2'   = parTargetW w2 ww
          wwStar = parTargetW qw2 ww2'
      in Join (PBeta qb1 qw1) (parSubstSingle wb2' ww2' wwStar qb2 qw2)
parDiamondW (WApp (WLam wb) ww) (PBeta b1 w1) (PApp (PLam b2) w2) =
  joinSym (parDiamondW (WApp (WLam wb) ww) (PApp (PLam b2) w2) (PBeta b1 w1))
parDiamondW (WApp (WLam wb) ww) (PBeta b1 w1) (PBeta b2 w2) =
  case (parDiamondW wb b1 b2, parDiamondW ww w1 w2) of
    (Join qb1 qb2, Join qw1 qw2) ->
      let wb1'   = parTargetW b1 wb
          wb2'   = parTargetW b2 wb
          ww1'   = parTargetW w1 ww
          ww2'   = parTargetW w2 ww
          wwStar = parTargetW qw1 ww1'
      in Join (parSubstSingle wb1' ww1' wwStar qb1 qw1)
              (parSubstSingle wb2' ww2' wwStar qb2 qw2)

parDiamond :: forall (n :: Nat) (n1 n2 :: UTerm n).
              foreach (m :: UTerm n) -> Par m n1 -> Par m n2 -> Joinable Par n1 n2
parDiamond m = parDiamondW (mkTermW m)
```

## Strip Lemma, Church–Rosser Confluence, and Uniqueness of Normal Forms

With `parDiamond` proved, the Church–Rosser theorem follows directly:

1. **`strip`**: pastes one-step `parDiamondW` squares along any horizontal
   `ParSteps` sequence.
2. **`parConfluence`**: stacks vertical strips to prove confluence for `ParSteps`.
3. **`churchRosser`**: converts both `BetaSteps` reductions into `ParSteps` via
   `betasToParsW`, joins them via `parConfluenceW`, and translates back via
   `parsToBetas`.
4. **`uniqueNormalForm`**: combines `churchRosser` with `normalNoBetaSteps` to
   prove that any two normal forms reached from the same term `l` are
   propositionally equal (`m1 :~: m2`).

```haskell
-- | Strip Lemma: one `Par` step commutes with any sequence of `ParSteps`.
stripW :: TermW m -> Par m n1 -> ParSteps m n2 -> Joinable ParSteps n1 n2
stripW _  p1 PSRefl         = Join PSRefl (PSCons p1 PSRefl)
stripW wm p1 (PSCons p2 ps) = case parDiamondW wm p1 p2 of
  Join q1 q2 -> case stripW (parTargetW p2 wm) q2 ps of
    Join r1 r2 -> Join (PSCons q1 r1) r2

strip :: forall (n :: Nat) (n1 n2 :: UTerm n).
         foreach (m :: UTerm n) -> Par m n1 -> ParSteps m n2 -> Joinable ParSteps n1 n2
strip m = stripW (mkTermW m)

-- | Confluence of parallel reduction (`par-confluence`).
parConfluenceW :: TermW l -> ParSteps l m1 -> ParSteps l m2 -> Joinable ParSteps m1 m2
parConfluenceW _  PSRefl         ps2 = Join ps2 PSRefl
parConfluenceW wl (PSCons p1 q1) ps2 = case stripW wl p1 ps2 of
  Join r1 r2 -> case parConfluenceW (parTargetW p1 wl) q1 r1 of
    Join s1 s2 -> Join s1 (psTrans r2 s2)

parConfluence :: forall (n :: Nat) (m1 m2 :: UTerm n).
                 foreach (l :: UTerm n) -> ParSteps l m1 -> ParSteps l m2 -> Joinable ParSteps m1 m2
parConfluence l = parConfluenceW (mkTermW l)

-- | Church-Rosser confluence for full β-reduction (`_—↠_`).
churchRosser :: forall (n :: Nat) (m1 m2 :: UTerm n).
                foreach (l :: UTerm n)
             -> BetaSteps l m1 -> BetaSteps l m2
             -> Joinable BetaSteps m1 m2
churchRosser l bs1 bs2 =
  let wl = mkTermW l
  in case parConfluenceW wl (betasToParsW wl bs1) (betasToParsW wl bs2) of
       Join ps1 ps2 -> Join (parsToBetas ps1) (parsToBetas ps2)

-- | Neutral terms cannot take a β-step.
neutralNoBetaStep :: Neutral m -> Not (BetaStep m n)
neutralNoBetaStep NVar         s          = case s of {}
neutralNoBetaStep (NApp nl _)  (XiApp1 s) = neutralNoBetaStep nl s
neutralNoBetaStep (NApp _  nm) (XiApp2 s) = normalNoBetaStep nm s
neutralNoBetaStep (NApp nl _)  Beta       = case nl of {}

-- | Normal forms cannot take a β-step.
normalNoBetaStep :: Normal m -> Not (BetaStep m n)
normalNoBetaStep (NNeu nm) s         = neutralNoBetaStep nm s
normalNoBetaStep (NLam nb) (XiLam s) = normalNoBetaStep nb s

-- | A normal form reduces in zero or more steps only to itself.
normalNoBetaSteps :: Normal m -> BetaSteps m n -> m :~: n
normalNoBetaSteps _  BRefl       = Refl
normalNoBetaSteps nm (BCons s _) = absurd (normalNoBetaStep nm s)

-- | Neutral terms reduce under parallel reduction only to themselves (`neutral-⇒`).
neutralPar :: Neutral m -> Par m n -> m :~: n
neutralPar NVar         PVar         = Refl
neutralPar (NApp nl nm) (PApp pl pm) = case (neutralPar nl pl, normalPar nm pm) of
  (Refl, Refl) -> Refl
neutralPar (NApp nl _)  (PBeta _ _)  = case nl of {}

-- | Normal forms reduce under parallel reduction only to themselves (`normal-⇒`).
normalPar :: Normal m -> Par m n -> m :~: n
normalPar (NNeu nm) p         = neutralPar nm p
normalPar (NLam nb) (PLam pb) = case normalPar nb pb of
  Refl -> Refl

-- | Normal forms reduce under multi-step parallel reduction only to themselves (`normal-⇒*`).
normalParSteps :: Normal m -> ParSteps m n -> m :~: n
normalParSteps _  PSRefl        = Refl
normalParSteps nm (PSCons p ps) = case normalPar nm p of
  Refl -> normalParSteps nm ps

-- | Corollary of Church-Rosser: every term has at most one normal form.
uniqueNormalForm :: forall (n :: Nat) (m1 m2 :: UTerm n).
                    foreach (l :: UTerm n)
                 -> BetaSteps l m1 -> BetaSteps l m2
                 -> Normal m1 -> Normal m2
                 -> m1 :~: m2
uniqueNormalForm l bs1 bs2 nm1 nm2 =
  case churchRosser l bs1 bs2 of
    Join r1 r2 -> case (normalNoBetaSteps nm1 r1, normalNoBetaSteps nm2 r2) of
      (Refl, Refl) -> Refl
```

## Exercises

### Exercise `par-diamond-eg` (practice)

Consider `L = (λ x. x x) ((λ y. y) z)` from the introduction. Construct two
`Par` derivations from `L`: one contracting only the outer redex and one
contracting only the inner redex, then apply `parDiamond` to obtain their
common reduct `z z`.

### Exercise `par-subst-id` (practice)

Using `parRefl` and `parSubst`, show that parallel reduction is closed under
arbitrary multi-variable substitution without re-proving renaming.

## Changes from PLFA

- Reuses the substitution infrastructure from [Substitution](/substitution/) to prove Tait and Martin-Löf's Diamond Property (`parDiamond`), the Strip Lemma (`strip`), Church-Rosser confluence (`churchRosser`), and uniqueness of normal forms (`uniqueNormalForm`).
