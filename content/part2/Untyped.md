---
title: "Untyped: Untyped lambda calculus with full normalisation"
prev: /Inference/
next: /More/
src: content/part2/Untyped.md
module: PLFH.Part2.Untyped
plfaChapter: https://plfa.inf.ed.ac.uk/Untyped/
---

As Dana Scott and Robert Harper famously observed, the **untyped lambda
calculus** is better understood as the **uni-typed lambda calculus**: there is
only a single universal type `★` such that `★ ≅ ★ → ★`. Every term can be
applied to every other term—including itself!

Dropping distinct types dramatically simplifies our intrinsically-scoped
representation from [DeBruijn](/DeBruijn/):
- A typing context `Ctx` collapses to a single natural number `n :: Nat`
  counting how many free variables are currently in scope.
- A de Bruijn lookup `Lookup g a` collapses to the finite set `Fin n`
  representing indices `{0, …, n - 1}`.
- The entire language shrinks to just **three constructors**: variables (`UVar`),
  lambda abstractions (`ULam`), and applications (`UApp`)!

Despite having only three constructors, the pure untyped lambda calculus is
Turing-complete (encoding Booleans, pairs, Church numerals, and arbitrary
recursion via fixed-point combinators such as `Y` and `Ω`). It also serves as
the foundation for [BigStep](/BigStep/), [Substitution](/Substitution/),
[Confluence](/Confluence/), and all five chapters of Part 3
([Denotational Semantics](/Denotational/)).

## Imports

```haskell
{-# LANGUAGE DependentTypes #-}
module PLFH.Part2.Untyped
  ( Fin (..)
  , UTerm (..)
  , FinW (..)
  , TermW (..)
  , mkFinW
  , mkTermW
  , shiftFin
  , extU
  , renameU
  , extsU
  , substU
  , singleSubstU
  , substSingleU
  , Neutral (..)
  , Normal (..)
  , BetaStep (..)
  , BetaSteps (..)
  , bsTrans
  , bsApp1
  , bsApp2
  , bsLam
  , IdTerm
  , SelfApp
  , OmegaTerm
  , CZero
  , COne
  , CTwo
  , idTerm
  , idIsNormal
  , cZeroIsNormal
  , cOneIsNormal
  , cTwoIsNormal
  , omegaTerm
  , idAppStep
  , omegaStep
  , kOmegaStep
  , StepRes (..)
  , stepNormal
  , EvalRes (..)
  , evalNormal
  , evalNormalTerm
  ) where

import Data.Kind (Type)
import Data.Nat.Dependent (Nat (..))
```

## Well-scoped de Bruijn indices (`Fin n`) and terms (`UTerm n`)

Because every variable has the same universal type, `Fin n` simply guarantees
that a variable index is strictly less than the current binder depth `n`:
- `Fin Zero` is uninhabited (a closed term has no free variables!).
- `FZ :: Fin (Succ n)` is the innermost variable `0`.
- `FS :: Fin n -> Fin (Succ n)` shifts an outer variable outward by one binder.

A term `UTerm n` is guaranteed **well-scoped** with at most `n` free variables:
entering a `ULam` increases the scope depth from `n` to `Succ n`.

```haskell
-- | Finite set {0, ..., n-1}: well-scoped de Bruijn variables in depth `n`.
data Fin (n :: Nat) where
  FZ :: Fin (Succ n)
  FS :: Fin n -> Fin (Succ n)

-- | Well-scoped untyped lambda terms with `n` free variables in scope.
data UTerm (n :: Nat) where
  UVar :: Fin n -> UTerm n
  ULam :: UTerm (Succ n) -> UTerm n
  UApp :: UTerm n -> UTerm n -> UTerm n

-- | Inductive structural witness for a de Bruijn index `x :: Fin n`.
type FinW :: forall (n :: Nat). Fin n -> Type
data FinW x where
  WFZ :: forall (m :: Nat). FinW (FZ :: Fin (Succ m))
  WFS :: forall (m :: Nat) (x :: Fin m). FinW x -> FinW (FS x)

-- | Inductive structural witness for a well-scoped term `t :: UTerm n`.
type TermW :: forall (n :: Nat). UTerm n -> Type
data TermW t where
  WVar :: FinW x -> TermW (UVar x)
  WLam :: TermW b -> TermW (ULam b)
  WApp :: TermW l -> TermW m -> TermW (UApp l m)

mkFinW :: forall (n :: Nat). foreach (x :: Fin n) -> FinW x
mkFinW FZ     = WFZ
mkFinW (FS x) = WFS (mkFinW x)

mkTermW :: forall (n :: Nat). foreach (t :: UTerm n) -> TermW t
mkTermW (UVar x)   = WVar (mkFinW x)
mkTermW (ULam b)   = WLam (mkTermW b)
mkTermW (UApp l m) = WApp (mkTermW l) (mkTermW m)

-- | Closed identity term: λx. x.
idTerm :: UTerm Zero
idTerm = ULam (UVar FZ)

-- | The classic diverging term Ω = (λx. x x) (λx. x x).
omegaTerm :: UTerm Zero
omegaTerm = UApp selfApp selfApp
  where
    selfApp :: UTerm Zero
    selfApp = ULam (UApp (UVar FZ) (UVar FZ))
```

Notice `omegaTerm`! In simply-typed lambda calculus, self-application `λ x ⇒ x · x`
is untypable (it would require a type `A` equal to `A → B`), so we had to add
an explicit `μ` construct for recursion. In the untyped lambda calculus,
`Ω = (λ x. x x) (λ x. x x)` is already a legal closed term—and as we verify
below (`omegaStep`), `Ω` reduces in one β-step straight back to `Ω`!

## Scope-preserving renaming and substitution

Simultaneous renaming (`extU`, `renameU`) and simultaneous capture-avoiding
substitution (`extsU`, `substU`, `substSingleU`) follow the exact same
Altenkirch–Reus / McBride pattern as [DeBruijn](/DeBruijn/), now indexed only
by scope depth `n :: Nat`:

```haskell
-- | Shift a variable up by one de Bruijn level.
shiftFin :: Fin m -> Fin (Succ m)
shiftFin x = FS x

-- | Lift a variable renaming under a lambda binder.
extU :: (Fin m -> Fin n) -> Fin (Succ m) -> Fin (Succ n)
extU _   FZ     = FZ
extU rho (FS x) = FS (rho x)

-- | Simultaneous renaming on well-scoped untyped terms.
renameU :: (Fin m -> Fin n) -> UTerm m -> UTerm n
renameU rho (UVar x)   = UVar (rho x)
renameU rho (ULam b)   = ULam (renameU (extU rho) b)
renameU rho (UApp l m) = UApp (renameU rho l) (renameU rho m)

-- | Lift a substitution under a lambda binder.
extsU :: (Fin m -> UTerm n) -> Fin (Succ m) -> UTerm (Succ n)
extsU _     FZ     = UVar FZ
extsU sigma (FS x) = renameU shiftFin (sigma x)

-- | Simultaneous capture-avoiding substitution on well-scoped untyped terms.
substU :: (Fin m -> UTerm n) -> UTerm m -> UTerm n
substU sigma (UVar x)   = sigma x
substU sigma (ULam b)   = ULam (substU (extsU sigma) b)
substU sigma (UApp l m) = UApp (substU sigma l) (substU sigma m)

-- | Single-variable substitution map `w • ids`.
singleSubstU :: UTerm n -> Fin (Succ n) -> UTerm n
singleSubstU w FZ     = w
singleSubstU _ (FS x) = UVar x

-- | Single-variable substitution `b [ w ]`.
substSingleU :: UTerm (Succ n) -> UTerm n -> UTerm n
substSingleU b w = substU (singleSubstU w) b
```

## Neutral forms, Normal forms, and Full β-Reduction

In [Lambda](/Lambda/), we used call-by-value reduction on *closed* terms, which
stopped at any lambda abstraction. In the untyped lambda calculus, however, we
often want **full β-reduction**—reducing redexes *anywhere* in a term,
including underneath `ULam` binders and inside arguments to free variables!

When we reduce under binders, we encounter **open terms**. What does a
completely reduced term (no β-redexes left anywhere) look like? It is defined
mutually by **neutral terms** and **normal forms**:

- A **neutral term** (`Neutral t`) is a variable applied to zero or more normal
  arguments (`x · N₁ · … · Nₖ`)—it cannot trigger a β-reduction at the top
  because its head is a variable, not a lambda.
- A **normal form** (`Normal t`) is either a neutral term (`NNeu`) or a lambda
  abstraction whose body is itself in normal form (`NLam`).

Just as in [DeBruijn](/DeBruijn/), GHC promotes the indexed GADT `UTerm n` and
evaluates our ordinary functional `substSingleU b w` directly inside the `Beta`
constructor of `BetaStep`!

```haskell
-- | Neutral terms: a variable applied to zero or more normal arguments.
type Neutral :: forall (n :: Nat). UTerm n -> Type
data Neutral t where
  NVar :: Neutral (UVar x)
  NApp :: Neutral l -> Normal m -> Neutral (UApp l m)

-- | Normal forms under full β-reduction (no β-redexes anywhere).
type Normal :: forall (n :: Nat). UTerm n -> Type
data Normal t where
  NNeu :: Neutral t -> Normal t
  NLam :: Normal b  -> Normal (ULam b)

-- | Full β-reduction (including under lambdas and in neutral arguments).
type BetaStep :: forall (n :: Nat). UTerm n -> UTerm n -> Type
data BetaStep t t' where
  XiApp1 :: BetaStep l l' -> BetaStep (UApp l m) (UApp l' m)
  XiApp2 :: BetaStep m m' -> BetaStep (UApp l m) (UApp l m')
  XiLam  :: BetaStep b b' -> BetaStep (ULam b) (ULam b')
  Beta   :: forall (n :: Nat) (b :: UTerm (Succ n)) (w :: UTerm n).
            BetaStep (UApp (ULam b) w) (substSingleU b w)

-- | Multi-step full β-reduction.
type BetaSteps :: forall (n :: Nat). UTerm n -> UTerm n -> Type
data BetaSteps t t' where
  BRefl :: BetaSteps t t
  BCons :: BetaStep s t -> BetaSteps t u -> BetaSteps s u

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

### Concrete examples: `id`, `id · id —→ id`, and `Ω —→ Ω`

Because `BetaStep` computes `substSingleU b w` directly at the type level,
concrete β-reductions such as `(λx. x) (λx. x) —→ λx. x`, `Ω —→ Ω`, and
`(λx y. y) Ω —→ λy. y` are each witnessed by a single constructor **`Beta`**:

```haskell
-- | Promoted closed terms: λx. x, λx. x x, and Ω = (λx. x x) (λx. x x).
type IdTerm    = (ULam (UVar FZ) :: UTerm Zero)
type SelfApp   = (ULam (UApp (UVar FZ) (UVar FZ)) :: UTerm Zero)
type OmegaTerm = (UApp SelfApp SelfApp :: UTerm Zero)

-- | Evidence that λx. x is in full normal form!
idIsNormal :: Normal IdTerm
idIsNormal = NLam (NNeu NVar)

-- | Concrete β-step: (λx. x) (λx. x) —→ (λx. x).
idAppStep :: BetaStep (UApp IdTerm IdTerm) IdTerm
idAppStep = Beta

-- | Concrete β-step: Ω —→ Ω!
omegaStep :: BetaStep OmegaTerm OmegaTerm
omegaStep = Beta

-- | Church numerals 0, 1, 2 in the untyped λ-calculus (λ s. λ z. s^n z).
type CZero = (ULam (ULam (UVar FZ)) :: UTerm Zero)
type COne  = (ULam (ULam (UApp (UVar (FS FZ)) (UVar FZ))) :: UTerm Zero)
type CTwo  = (ULam (ULam (UApp (UVar (FS FZ)) (UApp (UVar (FS FZ)) (UVar FZ)))) :: UTerm Zero)

-- | Church numerals are in full normal form (`Church-numerals`).
cZeroIsNormal :: Normal CZero
cZeroIsNormal = NLam (NLam (NNeu NVar))

cOneIsNormal :: Normal COne
cOneIsNormal = NLam (NLam (NNeu (NApp NVar (NNeu NVar))))

cTwoIsNormal :: Normal CTwo
cTwoIsNormal = NLam (NLam (NNeu (NApp NVar (NNeu (NApp NVar (NNeu NVar))))))

-- | Normal-order termination on a diverging argument (`K-omega`):
-- `(λ x. λ y. y) Ω —→ λ y. y` in a single outermost β-step!
kOmegaStep :: BetaStep (UApp (ULam (ULam (UVar FZ))) OmegaTerm) IdTerm
kOmegaStep = Beta
```

### Negative control: bogus β-step endpoint is rejected

Because `Beta` evaluates `substSingleU b w` directly, attempting to claim that
`(λx. x) (λx. x)` reduces to `Ω` is rejected by GHC with `GHC-83865`:

```{.haskell .fail name="NegBadBetaStep" expect="GHC-83865"}
{-# LANGUAGE DependentTypes #-}
module NegBadBetaStep (badBeta) where

import PLFH.Part2.Untyped (BetaStep (..), IdTerm, OmegaTerm, UTerm (..))

badBeta :: BetaStep (UApp IdTerm IdTerm) OmegaTerm
badBeta = Beta
```

## Normal-order vs. applicative-order reduction

Unlike call-by-value in [Lambda](/Lambda/), full β-reduction (`BetaStep`) is
**non-deterministic**: a term like `(λ x. λ y. y) Ω` can either discard `Ω`
immediately (outermost β-step, reaching the normal form `λ y. y`) or spin
forever reducing `Ω` inside the argument!

By the Standardization Theorem, **normal-order** (leftmost-outermost) reduction
is guaranteed to reach a normal form whenever one exists.

Because GHC binds indexed GADTs (`UTerm n`) as retained `foreach` fields inside
`StepRes` and `EvalRes` and reduces `substSingleU b m` directly, PLFA's
**constructive normal-order evaluator** (`stepNormal` and `evalNormal`) takes
only 30 lines, returning a certified multi-step `BetaSteps` trace plus a
`Normal` proof whenever evaluation finishes within the gas budget:

```haskell
-- | Outcome of one leftmost-outermost (normal-order) reduction step.
type StepRes :: forall (n :: Nat). UTerm n -> Type
data StepRes t where
  Reduct :: foreach (t' :: UTerm n) -> BetaStep t t' -> StepRes t
  IsNorm :: Normal t -> StepRes t

-- | Normal-order step for an application `UApp l m`.
stepApp :: forall (n :: Nat).
           foreach (l m :: UTerm n) -> StepRes (UApp l m)
stepApp (ULam b)     m = Reduct (substSingleU b m) Beta
stepApp (UVar x)     m = case stepNormal m of
  Reduct m' sm -> Reduct (UApp (UVar x) m') (XiApp2 sm)
  IsNorm nm    -> IsNorm (NNeu (NApp NVar nm))
stepApp (UApp l1 l2) m = case stepApp l1 l2 of
  Reduct l' sl       -> Reduct (UApp l' m) (XiApp1 sl)
  IsNorm (NNeu neuL) -> case stepNormal m of
    Reduct m' sm -> Reduct (UApp (UApp l1 l2) m') (XiApp2 sm)
    IsNorm nm    -> IsNorm (NNeu (NApp neuL nm))

-- | Constructive normal-order single-step reducer (`stepNormal`).
stepNormal :: forall (n :: Nat). foreach (t :: UTerm n) -> StepRes t
stepNormal (UVar _)   = IsNorm (NNeu NVar)
stepNormal (ULam b)   = case stepNormal b of
  Reduct b' sb -> Reduct (ULam b') (XiLam sb)
  IsNorm nb    -> IsNorm (NLam nb)
stepNormal (UApp l m) = stepApp l m

-- | Outcome of gas-bounded normal-order evaluation (`Finished` in PLFA).
type EvalRes :: forall (n :: Nat). UTerm n -> Type
data EvalRes t where
  EvalDone     :: foreach (nf :: UTerm n) -> BetaSteps t nf -> Normal nf -> EvalRes t
  EvalOutOfGas :: foreach (t' :: UTerm n) -> BetaSteps t t' -> EvalRes t

-- | Gas-bounded normal-order evaluator returning a certified `BetaSteps` trace
-- and `Normal` proof!
evalNormal :: forall (n :: Nat). Nat -> foreach (t :: UTerm n) -> EvalRes t
evalNormal gas t = case gas of
  Zero   -> EvalOutOfGas t BRefl
  Succ g -> case stepNormal t of
    IsNorm nt    -> EvalDone t BRefl nt
    Reduct t' st -> case evalNormal g t' of
      EvalDone nf bs nnf -> EvalDone nf (BCons st bs) nnf
      EvalOutOfGas u bs  -> EvalOutOfGas u (BCons st bs)

-- | Plain wrapper for running `evalNormal` on arbitrary runtime `UTerm n` values.
evalNormalTerm :: forall (n :: Nat). Nat -> UTerm n -> Maybe (UTerm n)
evalNormalTerm gas t = case evalNormal gas t of
  EvalDone nf _ _  -> Just nf
  EvalOutOfGas _ _ -> Nothing
```

## Exercises

#### Exercise `Church-numerals` (practice)

Define Church numerals `cZero`, `cOne`, `cTwo :: UTerm Zero` (where `n` is
`λ s. λ z. s (s … (s z) …)`) using `ULam`, `UApp`, `UVar`, `FZ`, and `FS FZ`,
and check that `cZero = ULam (ULam (UVar FZ))` and `cOne = ULam (ULam (UApp (UVar (FS FZ)) (UVar FZ)))` satisfy `Normal`!

#### Exercise `K-omega` (practice)

Use `Beta` to construct a one-step reduction proof showing that
`(λ x. λ y. y) Ω` reduces in a single step to `IdTerm`, illustrating why
normal-order reduction terminates on terms where call-by-value diverges!

## Changes from PLFA

- Adapted from [Untyped](https://plfa.inf.ed.ac.uk/Untyped/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/Untyped.lagda.md)),
  licensed under CC BY 4.0.
- Ports `Fin`, `UTerm`, `extU`, `renameU`, `extsU`, `substU`,
  `substSingleU`, `Neutral`, `Normal`, functional `BetaStep` (`Beta` over
  `substSingleU b w`, verified by negative control `NegBadBetaStep`),
  `BetaSteps`, `idIsNormal`, `idAppStep`, `omegaTerm`, `omegaStep`,
  `cZeroIsNormal`/`cOneIsNormal`/`cTwoIsNormal`, `kOmegaStep`, and the
  constructive normal-order evaluator (`stepNormal`, `evalNormal`,
  `evalNormalTerm`), reducing `(λx y. y) Ω —↠ id` with a certified `BetaSteps`
  and `Normal` derivation.
