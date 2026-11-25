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
  , shiftFin
  , extU
  , renameU
  , extsU
  , substU
  , singleSubstU
  , substSingleU
  , BumpFin (..)
  , ShiftU (..)
  , RemoveFin (..)
  , SubstAtU (..)
  , Neutral (..)
  , Normal (..)
  , BetaStep (..)
  , BetaSteps (..)
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
  , BumpRes (..)
  , bumpProof
  , ShiftRes (..)
  , shiftProof
  , CmpFin (..)
  , cmpFin
  , SubstRes (..)
  , substProof
  , StepRes (..)
  , stepNormal
  , EvalRes (..)
  , evalNormal
  , evalNormalTerm
  ) where

import Data.Kind (Type)
import HaskLib.Nat (Nat (..))
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

## Relational capture-avoiding substitution (`SubstAtU`)

<div class="wip-notice">
<strong>[WIP NOTICE — Relational <code>SubstAtU</code> vs. functional <code>substSingleU</code>]</strong>
PLFA writes the β-rule directly using the function
<code>substSingleU b w</code>. To keep <code>BetaStep</code>—and all
downstream theorems in <a href="/Confluence/">Confluence</a>,
<a href="/Soundness/">Soundness</a>, <a href="/Adequacy/">Adequacy</a>, and
<a href="/ContextualEquivalence/">ContextualEquivalence</a>—<strong>100%
mathematically sound</strong> with zero unconstrained type variables and
explicit structural induction on substitution derivations, we state
single-variable de Bruijn substitution inductively via <code>SubstAtU</code>
below (verified by negative control <code>NegBadBetaStep</code>).
</div>

Each of the four inductive relations below is completely deterministic:
- `BumpFin c x y`: shifts index `x` up by `1` whenever `x >= c`;
- `ShiftU c m m'`: weakens a term `m` by shifting every free variable `>= c` up
  by `1` (used to avoid capture when descending under a `ULam`);
- `RemoveFin c x y`: closes the gap left at `c` for every distinct variable
  `x /= c`;
- `SubstAtU c w m m'`: substitutes `w` for variable `c` in `m`, yielding `m'`.

```haskell
-- | Shift a variable `x :: Fin n` up by one slot at cutoff `c :: Fin (Succ n)`.
type BumpFin :: forall (n :: Nat). Fin (Succ n) -> Fin n -> Fin (Succ n) -> Type
data BumpFin c x y where
  BumpZ  :: BumpFin FZ x (FS x)
  BumpSZ :: forall {n} (c :: Fin (Succ n)). BumpFin (FS c) FZ FZ
  BumpSS :: BumpFin c x y -> BumpFin (FS c) (FS x) (FS y)

-- | Capture-avoiding weakening: shift all free variables >= `c` up by one.
type ShiftU :: forall (n :: Nat). Fin (Succ n) -> UTerm n -> UTerm (Succ n) -> Type
data ShiftU c m m' where
  ShiftVar :: BumpFin c x y -> ShiftU c (UVar x) (UVar y)
  ShiftLam :: ShiftU (FS c) b b' -> ShiftU c (ULam b) (ULam b')
  ShiftApp :: ShiftU c l l' -> ShiftU c m m' -> ShiftU c (UApp l m) (UApp l' m')

-- | Remove slot `c` from any distinct variable `x /= c` in `Fin (Succ n)`.
type RemoveFin :: forall (n :: Nat). Fin (Succ n) -> Fin (Succ n) -> Fin n -> Type
data RemoveFin c x y where
  RemGt :: forall {n} (y :: Fin n). RemoveFin FZ (FS y) y
  RemLt :: forall {n} (c :: Fin (Succ n)). RemoveFin (FS c) FZ FZ
  RemSS :: RemoveFin c x y -> RemoveFin (FS c) (FS x) (FS y)

-- | Deterministic relational single-variable substitution `m [ c := w ] ↦ m'`.
type SubstAtU :: forall (n :: Nat). Fin (Succ n) -> UTerm n -> UTerm (Succ n) -> UTerm n -> Type
data SubstAtU c w m m' where
  SUEq  :: SubstAtU c w (UVar c) w
  SUNeq :: RemoveFin c x y -> SubstAtU c w (UVar x) (UVar y)
  SULam :: ShiftU FZ w w' -> SubstAtU (FS c) w' b b' -> SubstAtU c w (ULam b) (ULam b')
  SUApp :: SubstAtU c w l l' -> SubstAtU c w m m' -> SubstAtU c w (UApp l m) (UApp l' m')
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

Just as in [DeBruijn](/DeBruijn/), GHC accepts **promoting the indexed GADT
`UTerm n`** to index `Neutral`, `Normal`, `BetaStep`, and `BetaSteps`!

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
  Beta   :: forall (n :: Nat) (w :: UTerm n) (b :: UTerm (Succ n)) (r :: UTerm n).
            SubstAtU FZ w b r -> BetaStep (UApp (ULam b) w) r

-- | Multi-step full β-reduction.
type BetaSteps :: forall (n :: Nat). UTerm n -> UTerm n -> Type
data BetaSteps t t' where
  BRefl :: BetaSteps t t
  BCons :: BetaStep s t -> BetaSteps t u -> BetaSteps s u
```

### Concrete examples: `id`, `id · id —→ id`, and `Ω —→ Ω`

Because `BetaStep` works on promoted `UTerm Zero` values, we can verify concrete
normal forms and β-reductions directly in the type system:

```haskell
-- | Promoted closed terms: λx. x, λx. x x, and Ω = (λx. x x) (λx. x x).
type IdTerm    = (ULam (UVar FZ) :: UTerm Zero)
type SelfApp   = (ULam (UApp (UVar FZ) (UVar FZ)) :: UTerm Zero)
type OmegaTerm = (UApp SelfApp SelfApp :: UTerm Zero)

-- | Evidence that λx. x is in full normal form!
idIsNormal :: Normal IdTerm
idIsNormal = NLam (NNeu NVar)

-- | Concrete sound β-step: (λx. x) (λx. x) —→ (λx. x).
idAppStep :: BetaStep (UApp IdTerm IdTerm) IdTerm
idAppStep = Beta SUEq

-- | Concrete sound β-step: Ω —→ Ω!
omegaStep :: BetaStep OmegaTerm OmegaTerm
omegaStep = Beta (SUApp SUEq SUEq)

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
kOmegaStep =
  Beta (SULam
    (ShiftApp
      (ShiftLam (ShiftApp (ShiftVar BumpSZ) (ShiftVar BumpSZ)))
      (ShiftLam (ShiftApp (ShiftVar BumpSZ) (ShiftVar BumpSZ))))
    (SUNeq RemLt))
```

### Negative control: bogus β-step endpoint is rejected

Because `Beta` enforces deterministic `SubstAtU FZ w b r` (with zero
unconstrained function type variables!), attempting to reduce `(λx. x) (λx. x)`
to `Ω` is rejected by GHC with `GHC-83865`:

```{.haskell .fail name="NegBadBetaStep" expect="GHC-83865"}
{-# LANGUAGE DependentTypes #-}
module NegBadBetaStep (badBeta) where

import PLFH.Part2.Untyped (BetaStep (..), IdTerm, OmegaTerm, SubstAtU (..), UTerm (..))

badBeta :: BetaStep (UApp IdTerm IdTerm) OmegaTerm
badBeta = Beta SUEq
```

## Normal-order vs. applicative-order reduction

Unlike call-by-value in [Lambda](/Lambda/), full β-reduction (`BetaStep`) is
**non-deterministic**: a term like `(λ x. λ y. y) Ω` can either discard `Ω`
immediately (outermost β-step, reaching the normal form `λ y. y`) or spin
forever reducing `Ω` inside the argument!

By the Standardization Theorem, **normal-order** (leftmost-outermost) reduction
is guaranteed to reach a normal form whenever one exists.

Because GHC supports binding indexed GADTs (`Fin n`, `UTerm n`) as retained
`foreach` fields inside data constructors, we can write PLFA's **constructive
normal-order evaluator** (`stepNormal` and `evalNormal`) directly in Haskell!
Each helper (`bumpProof`, `shiftProof`, `cmpFin`, `substProof`) computes the
shifted or substituted term *together with* its checked `ShiftU` / `SubstAtU`
derivation, so `evalNormal` returns a certified multi-step `BetaSteps` trace
plus a `Normal` proof whenever it finishes within the gas budget:

```haskell
-- | Constructive witness for `BumpFin c x y`.
type BumpRes :: forall (n :: Nat). Fin (Succ n) -> Fin n -> Type
data BumpRes c x where
  MkBump :: foreach (y :: Fin (Succ n)) -> BumpFin c x y -> BumpRes c x

-- | Compute the bumped variable `y` together with its `BumpFin` proof.
bumpProof :: forall (n :: Nat).
             foreach (c :: Fin (Succ n)) -> foreach (x :: Fin n) -> BumpRes c x
bumpProof FZ      x       = MkBump (FS x) BumpZ
bumpProof (FS c') FZ      = MkBump FZ (BumpSZ @c')
bumpProof (FS c') (FS x') = case bumpProof c' x' of
  MkBump y b -> MkBump (FS y) (BumpSS b)

-- | Constructive witness for `ShiftU c m m'`.
type ShiftRes :: forall (n :: Nat). Fin (Succ n) -> UTerm n -> Type
data ShiftRes c m where
  MkShift :: foreach (m' :: UTerm (Succ n)) -> ShiftU c m m' -> ShiftRes c m

-- | Compute capture-avoiding weakening together with its `ShiftU` proof.
shiftProof :: forall (n :: Nat).
              foreach (c :: Fin (Succ n)) -> foreach (m :: UTerm n) -> ShiftRes c m
shiftProof c (UVar x)   = case bumpProof c x of
  MkBump y b -> MkShift (UVar y) (ShiftVar b)
shiftProof c (ULam b)   = case shiftProof (FS c) b of
  MkShift b' sb -> MkShift (ULam b') (ShiftLam sb)
shiftProof c (UApp l r) = case shiftProof c l of
  MkShift l' sl -> case shiftProof c r of
    MkShift r' sr -> MkShift (UApp l' r') (ShiftApp sl sr)

-- | Compare two indices in `Fin (Succ n)`: either equal or separated by `RemoveFin`.
type CmpFin :: forall (n :: Nat). Fin (Succ n) -> Fin (Succ n) -> Type
data CmpFin c x where
  CmpEq  :: CmpFin c c
  CmpNeq :: foreach (y :: Fin n) -> RemoveFin c x y -> CmpFin c x

-- | Helper for comparing `FS c'` once inspecting `c'` has refined the outer index to `Succ m`.
cmpFinFS :: forall (m :: Nat).
            foreach (c' :: Fin (Succ m)) -> foreach (x :: Fin (Succ (Succ m)))
         -> CmpFin (FS c') x
cmpFinFS c' FZ      = CmpNeq FZ (RemLt @c')
cmpFinFS c' (FS x') = case cmpFin c' x' of
  CmpEq      -> CmpEq
  CmpNeq y r -> CmpNeq (FS y) (RemSS r)

-- | Decidable comparison with `RemoveFin` evidence.
cmpFin :: forall (n :: Nat).
          foreach (c :: Fin (Succ n)) -> foreach (x :: Fin (Succ n)) -> CmpFin c x
cmpFin FZ            FZ     = CmpEq
cmpFin FZ            (FS y) = CmpNeq y (RemGt @y)
cmpFin (FS FZ)       x      = cmpFinFS FZ x
cmpFin (FS (FS c'')) x      = cmpFinFS (FS c'') x

-- | Constructive witness for `SubstAtU c w m r`.
type SubstRes :: forall (n :: Nat). Fin (Succ n) -> UTerm n -> UTerm (Succ n) -> Type
data SubstRes c w m where
  MkSubst :: foreach (r :: UTerm n) -> SubstAtU c w m r -> SubstRes c w m

-- | Compute single-variable substitution `m [ c := w ]` with its `SubstAtU` proof.
substProof :: forall (n :: Nat).
              foreach (c :: Fin (Succ n))
           -> foreach (w :: UTerm n)
           -> foreach (m :: UTerm (Succ n))
           -> SubstRes c w m
substProof c w (UVar x)   = case cmpFin c x of
  CmpEq      -> MkSubst w SUEq
  CmpNeq y r -> MkSubst (UVar y) (SUNeq r)
substProof c w (ULam b)   = case shiftProof FZ w of
  MkShift w' sw -> case substProof (FS c) w' b of
    MkSubst b' sb -> MkSubst (ULam b') (SULam sw sb)
substProof c w (UApp l r) = case substProof c w l of
  MkSubst l' sl -> case substProof c w r of
    MkSubst r' sr -> MkSubst (UApp l' r') (SUApp sl sr)

-- | Outcome of one leftmost-outermost (normal-order) reduction step.
type StepRes :: forall (n :: Nat). UTerm n -> Type
data StepRes t where
  Reduct :: foreach (t' :: UTerm n) -> BetaStep t t' -> StepRes t
  IsNorm :: Normal t -> StepRes t

-- | Normal-order step for an application `UApp l m`.
stepApp :: forall (n :: Nat).
           foreach (l m :: UTerm n) -> StepRes (UApp l m)
stepApp (ULam b)     m = case substProof FZ m b of
  MkSubst r sr -> Reduct r (Beta sr)
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

Using `Beta`, `SULam`, and `SUNeq`, construct a one-step reduction proof showing
that `(λ x. λ y. y) Ω` reduces in a single step to `IdTerm`, illustrating why
normal-order reduction terminates on terms where call-by-value diverges!

## Changes from PLFA

- Adapted from [Untyped](https://plfa.inf.ed.ac.uk/Untyped/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/Untyped.lagda.md)),
  licensed under CC BY 4.0.
- Checked direct ports of `Fin`, `UTerm`, `extU`, `renameU`, `extsU`,
  `substU`, `substSingleU`, `Neutral`, `Normal`, `BetaStep`, `BetaSteps`,
  `idIsNormal`, `idAppStep`, `omegaTerm`, `omegaStep`, `cZeroIsNormal`/
  `cOneIsNormal`/`cTwoIsNormal`, `kOmegaStep`, and the complete constructive
  normal-order evaluator (`bumpProof`, `shiftProof`, `cmpFin`, `substProof`,
  `stepNormal`, `evalNormal`, `evalNormalTerm`), reducing `(λx y. y) Ω —↠ id`
  with a certified `BetaSteps` + `Normal` derivation!
- Uses deterministic relational `SubstAtU` in `Beta` (verified by negative
  control `NegBadBetaStep`) for structural induction in downstream chapters.
