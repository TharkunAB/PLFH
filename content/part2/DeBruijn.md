---
title: "DeBruijn: Intrinsically-typed de Bruijn representation"
prev: /Properties/
next: /Inference/
src: content/part2/DeBruijn.md
module: PLFH.Part2.DeBruijn
plfaChapter: https://plfa.inf.ed.ac.uk/DeBruijn/
---

In [Lambda](/Lambda/) and [Properties](/Properties/), we gave an **extrinsic**
(Curry-style) formalization of the simply-typed lambda calculus: terms were
defined without types first, and a separate typing judgment `HasType g m a`
selected the well-typed terms afterward.

In this chapter we switch to an **intrinsic** (Church-style) formalization,
combined with **de Bruijn indices** (invented by Dutch mathematician Nicolaas
Govert de Bruijn in 1972 for the Automath proof checker):

1. Every term `Term g a` *carries its context `g` and type `a` in its Haskell
   type*—it is literally impossible to construct an ill-typed term!
2. Variable names disappear completely. Instead, a variable is a de Bruijn
   index `Lookup g a` counting how many binders to skip outward to find its
   binding site (`Z` for the innermost binder, `S Z` for the next binder out,
   and so on). Two α-equivalent terms like `λ x ⇒ x` and `λ y ⇒ y` have the
   *exact same* representation: `Lam (Var Z)`!
3. Simultaneous substitution (`subst`) is guaranteed **type-preserving by
   construction**, following the classic pattern of Thorsten Altenkirch and
   Bernhard Reus (1999) and Conor McBride: we first define simultaneous
   *renaming* (`rename`) and then use it to lift substitutions under binders
   without variable capture.

From a Dependent Haskell standpoint, this chapter is also a major milestone:
defining `Value` and `IsVal` requires **promoting an indexed GADT (`Term g a`)
to a kind**!

## Imports

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
{-# OPTIONS_GHC -fwrite-source-equations #-}
module PLFH.Part2.DeBruijn
  ( Ty (..)
  , Ctx (..)
  , Lookup (..)
  , Term (..)
  , ext
  , rename
  , exts
  , subst
  , substSingle
  , termTwo
  , Value (..)
  , valZero
  , IsVal (..)
  , checkValue
  ) where

import Data.Kind (Type)
```

## Types, nameless contexts, and de Bruijn lookups

Without variable names, a typing context `Ctx` is just a snoc-list of types:
`CEmpty` is the empty context `∅`, and `CExt g a` extends `g` with a new
innermost variable of type `a`.

A de Bruijn index `Lookup g a` (written `Γ ∋ A` in PLFA) points to an entry of
type `a` in context `g`:
- `Z` selects the most recently bound variable (`0`);
- `S x` skips the innermost variable and looks up `x` in the remaining outer
  context.

Notice how `Lookup` no longer needs `Not (x :~: y)` proofs! Shadowing is
completely automatic: `Z` always refers to the innermost binder, and `S Z`
refers to the one just outside it.

```haskell
-- | Simple types: natural numbers and functions.
data Ty = TNat | TArr Ty Ty
  deriving (Show)

-- | Nameless typing contexts.
data Ctx = CEmpty | CExt Ctx Ty

-- | Intrinsically typed de Bruijn indices (Γ ∋ A).
data Lookup (g :: Ctx) (a :: Ty) where
  Z :: Lookup (CExt g a) a
  S :: Lookup g a -> Lookup (CExt g b) a
```

## Intrinsically typed terms (`Γ ⊢ A`)

Compare the constructors of `Term g a` below with the typing rules of `HasType`
in [Lambda](/Lambda/): they are *one and the same*! Syntax and typing have
merged into a single indexed GADT:

```haskell
-- | Intrinsically typed STLC terms with naturals, case, and μ-recursion.
data Term (g :: Ctx) (a :: Ty) where
  Var  :: Lookup g a -> Term g a
  Lam  :: Term (CExt g a) b -> Term g (TArr a b)
  App  :: Term g (TArr a b) -> Term g a -> Term g b
  Zero :: Term g TNat
  Suc  :: Term g TNat -> Term g TNat
  Case :: Term g TNat -> Term g a -> Term (CExt g TNat) a -> Term g a
  Mu   :: Term (CExt g a) a -> Term g a

-- | Closed intrinsically-typed numeral 2.
termTwo :: Term g TNat
termTwo = Suc (Suc Zero)
```

Because `termTwo` is polymorphic in `g`, it is valid in *any* context `g`
(including `CEmpty`)!

## Simultaneous renaming and substitution (type-preserving by construction!)

Why define **simultaneous** renaming and substitution rather than substituting
one variable at a time? Because when you go under a lambda binder (`Lam`), a
single substitution for variable `0` becomes a substitution for variable `1`,
and any free variables inside the replacement term must be shifted up by one so
they do not get captured by the newly entered binder!

Following Altenkirch–Reus and McBride, we solve this cleanly in two stages:

1. **Simultaneous renaming (`rename`)**: given any map `rho :: forall a. Lookup g a -> Lookup d a`
   from variables in `g` to variables in `d`, `ext rho` extends `rho` under a
   new binder (`Z` maps to `Z`; `S x` maps to `S (rho x)`). Structural
   recursion on `Term g b` then produces a `Term d b`.
2. **Simultaneous substitution (`subst`)**: given any map
   `sigma :: forall a. Lookup g a -> Term d a` from variables in `g` to *terms*
   in `d`, `exts sigma` extends `sigma` under a new binder by mapping `Z` to
   `Var Z` and weakening every `sigma x` via `rename S` (shifting all of its
   free variables up by one so the new binder never captures them!).
3. **Single-variable substitution (`substSingle`)**: replacing the innermost
   variable `Z` with `w` while leaving all outer variables `S x` alone is just
   one special case of `subst`!

Every single function below ports to Dependent Haskell with the **exact same**
types and definitions as PLFA—and notice that we get the entire Substitution
Typing Lemma of [Properties](/Properties/) for free in its type signature!

```haskell
-- | Extend a variable renaming under a binder.
ext :: (forall a. Lookup g a -> Lookup d a)
    -> (forall a. Lookup (CExt g b) a -> Lookup (CExt d b) a)
ext _   Z     = Z
ext rho (S x) = S (rho x)

-- | Simultaneous renaming on intrinsically typed terms.
rename :: (forall a. Lookup g a -> Lookup d a) -> Term g b -> Term d b
rename rho (Var x)      = Var (rho x)
rename rho (Lam n)      = Lam (rename (ext rho) n)
rename rho (App l m)    = App (rename rho l) (rename rho m)
rename _   Zero         = Zero
rename rho (Suc m)      = Suc (rename rho m)
rename rho (Case l m n) = Case (rename rho l) (rename rho m) (rename (ext rho) n)
rename rho (Mu n)       = Mu (rename (ext rho) n)

-- | Extend a simultaneous substitution under a binder.
exts :: (forall a. Lookup g a -> Term d a)
     -> (forall a. Lookup (CExt g b) a -> Term (CExt d b) a)
exts _     Z     = Var Z
exts sigma (S x) = rename S (sigma x)

-- | Simultaneous substitution on intrinsically typed terms.
subst :: (forall a. Lookup g a -> Term d a) -> Term g b -> Term d b
subst sigma (Var x)      = sigma x
subst sigma (Lam n)      = Lam (subst (exts sigma) n)
subst sigma (App l m)    = App (subst sigma l) (subst sigma m)
subst _     Zero         = Zero
subst sigma (Suc m)      = Suc (subst sigma m)
subst sigma (Case l m n) = Case (subst sigma l) (subst sigma m) (subst (exts sigma) n)
subst sigma (Mu n)       = Mu (subst (exts sigma) n)

-- | Substitute a single closed/open term `w` for variable `Z` in `n` (N [ W ]).
substSingle :: Term (CExt g a) b -> Term g a -> Term g b
substSingle n w = subst (\case { Z -> w; S x -> Var x }) n
```

## Promoting `Term g a`: Values and decidable value classification

With `StandaloneKindSignatures` and `DataKinds`, GHC accepts **promoting the
indexed GADT `Term g a`** to a kind, letting us index `Value` and `IsVal`
directly over intrinsically-typed terms!

Even better, `checkValue` classifies any retained closed term
`foreach (m :: Term CEmpty a)` directly by ordinary pattern-matching equations—
and GHC recognizes that `Var x` is impossible in the empty context `CEmpty`
(`case x of {}`):

```haskell
-- | Values indexed by promoted intrinsically-typed terms!
type Value :: forall (g :: Ctx) (a :: Ty). Term g a -> Type
data Value m where
  VLam  :: Value (Lam n)
  VZero :: Value Zero
  VSuc  :: Value v -> Value (Suc v)

-- | Concrete witness that `Zero` is already a value.
valZero :: Value (Zero :: Term CEmpty TNat)
valZero = VZero

-- | Classification of a closed intrinsically-typed term as a value or non-value.
type IsVal :: forall (a :: Ty). Term CEmpty a -> Type
data IsVal m where
  YesVal :: Value m -> IsVal m
  NotVal :: IsVal m

-- | Equation-style value classification over retained intrinsically-typed `Term CEmpty a`!
checkValue :: forall (a :: Ty). foreach (m :: Term CEmpty a) -> IsVal m
checkValue (Var x)      = case x of {}
checkValue (Lam _)      = YesVal VLam
checkValue (App _ _)    = NotVal
checkValue Zero         = YesVal VZero
checkValue (Suc n)      = case checkValue n of
  YesVal v -> YesVal (VSuc v)
  NotVal   -> NotVal
checkValue (Case _ _ _) = NotVal
checkValue (Mu _)       = NotVal
```

## Intrinsically-typed Reduction (`Step`) and Progress (`appProgress`)

In the intrinsically-typed representation, `Step` has kind
`forall (g :: Ctx) (a :: Ty). Term g a -> Term g a -> Type`—so **Preservation
holds automatically** by the very type of `Step`! Every reduction step connects
two terms of the *exact same* type `a` in the *exact same* context `g`.

Compiling this syntax module with `{-# OPTIONS_GHC -fwrite-source-equations #-}`
publishes the checked equations for `rename`, `subst`, and `substSingle` into
its compiled interface (`DeBruijn.hi`). Our companion checked module
[`PLFH.Part2.DeBruijnProgress`](https://github.com/Tritlo/PLFH/blob/main/clients/PLFH/Part2/DeBruijnProgress.hs)
reads that native interface and defines all eight intrinsically-typed reduction
rules (`XiApp1`, `XiApp2`, `XiSuc`, `XiCase`, `BetaLam`, `BetaZero`, `BetaSuc`,
`BetaMu`) using real functional `D.substSingle`, concrete capture-avoiding beta
witnesses (`betaIdStep`, `betaCaptureAvoid`, `betaShiftUnderLam`), and the
checked application progress dispatcher `appProgress`:

```{.haskell .ignore}
-- Excerpt from checked client module PLFH.Part2.DeBruijnProgress:
type Step :: forall (g :: D.Ctx) (a :: D.Ty). D.Term g a -> D.Term g a -> Type
data Step m n where
  XiApp1   :: Step l l' -> Step (D.App l m) (D.App l' m)
  XiApp2   :: D.Value l -> Step m m' -> Step (D.App l m) (D.App l m')
  XiSuc    :: Step m m' -> Step (D.Suc m) (D.Suc m')
  XiCase   :: Step l l' -> Step (D.Case l m n) (D.Case l' m n)
  BetaLam  :: forall g a b (n :: D.Term (D.CExt g a) b) (w :: D.Term g a).
              D.Value w -> Step (D.App (D.Lam n) w) (D.substSingle n w)
  BetaZero :: forall g a (m :: D.Term g a) (n :: D.Term (D.CExt g D.TNat) a).
              Step (D.Case D.Zero m n) m
  BetaSuc  :: forall g a (m :: D.Term g a) (n :: D.Term (D.CExt g D.TNat) a)
                         (v :: D.Term g D.TNat).
              D.Value v -> Step (D.Case (D.Suc v) m n) (D.substSingle n v)
  BetaMu   :: forall g a (n :: D.Term (D.CExt g a) a).
              Step (D.Mu n) (D.substSingle n (D.Mu n))
```

### Negative control: forged variable capture is rejected

When substituting the open value `λ. Var (S Z)` under an inner binder,
`substSingle` must shift its free variable to `S (S Z)` (`betaShiftUnderLam`).
Claiming the unshifted (capturing) result `Lam (Lam (Var (S Z)))` is rejected
by GHC with `GHC-83865`:

```{.haskell .fail name="NegDeBruijnBadCapture" expect="GHC-83865"}
{-# LANGUAGE DataKinds, GADTs, TypeApplications #-}
module NegDeBruijnBadCapture (badCapture) where

import qualified PLFH.Part2.DeBruijn as D
import PLFH.Part2.DeBruijnProgress (Step (..))

badCapture
  :: Step @(D.CExt D.CEmpty D.TNat)
          @(D.TArr D.TNat (D.TArr D.TNat D.TNat))
          (D.App (D.Lam (D.Lam (D.Var (D.S D.Z)))) (D.Lam (D.Var (D.S D.Z))))
          (D.Lam (D.Lam (D.Var (D.S D.Z))))
badCapture = BetaLam D.VLam
```

<div class="wip-notice">
<strong>[WIP NOTICE — Full intrinsic <code>progress</code> over <code>Case</code> and <code>Mu</code>]</strong>
All eight reduction rules using functional <code>substSingle</code> and the
application progress branch (<code>appProgress</code>) check cleanly across the
compiled interface in <code>PLFH.Part2.DeBruijnProgress</code>. Completing full
recursive <code>progress</code> still awaits retained refinements for the outer
<code>Case</code> and <code>Mu</code> branches (and untyped substitution in
<code>Untyped</code> remains tracked separately in
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_SubstSingleUOpenEq.hs"><code>reproducers/R13_SubstSingleUOpenEq.hs</code></a>).
</div>

## Exercises

#### Exercise `two+two` (practice)

Define closed intrinsically-typed `plus :: Term CEmpty (TArr TNat (TArr TNat TNat))`
using `Mu`, `Lam`, `Case`, `Suc`, and de Bruijn indices `Z` / `S Z` / `S (S Z)`,
and verify that GHC accepts it without any separate typing proof!

#### Exercise `mul` (recommended)

Define closed intrinsically-typed `mul :: Term CEmpty (TArr TNat (TArr TNat TNat))`
in terms of `plus` above.

#### Exercise `subst-id` (stretch)

Explore what happens when you call `substSingle (Lam (Var (S Z))) Zero`: notice
that `exts` shifts `Zero` (no free variables) under the inner `Lam`, producing
`Lam Zero` without variable capture. What about `substSingle (Lam (Var (S Z))) (Var Z)`
in context `CExt CEmpty TNat`?

## Changes from PLFA

- Adapted from [DeBruijn](https://plfa.inf.ed.ac.uk/DeBruijn/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/DeBruijn.lagda.md)),
  licensed under CC BY 4.0.
- `Ty`, `Ctx`, `Lookup`, `Term`, `ext`, `rename`, `exts`, `subst`,
  `substSingle`, GADT-promoted `Value`, and direct equation-style
  `IsVal`/`checkValue` over retained `foreach (m :: Term CEmpty a)` all
  compile cleanly with `-dcore-lint -dstg-lint` and pass our `.hi` interface
  soundness audit.
- With `-fwrite-source-equations`, our checked client module
  `PLFH.Part2.DeBruijnProgress` defines all eight intrinsically-typed `Step`
  rules using real functional `substSingle`, concrete capture-avoiding beta
  witnesses (guarded by negative control `NegDeBruijnBadCapture`), and the
  application progress dispatcher `appProgress`; full `Case`/`Mu` `progress`
  remains marked `[WIP NOTICE]`.
