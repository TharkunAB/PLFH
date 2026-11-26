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
{-# LANGUAGE DependentTypes #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
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
  , plusTerm
  , mulTerm
  , Value (..)
  , valZero
  , IsVal (..)
  , checkValue
  , Step (..)
  , Steps (..)
  , Progress (..)
  , progress
  , appProgress
  , Gas (..)
  , Finished (..)
  , eval
  , betaIdStep
  , betaCaptureAvoid
  , betaShiftUnderLam
  ) where

import Data.Kind (Type)
import qualified Data.Nat.Dependent as N
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

-- | Intrinsically-typed recursive addition (`two+two`): Nat -> Nat -> Nat.
-- μ "+". λ m. λ n. case m [ zero => n | suc m' => suc ("+" m' n) ]
plusTerm :: Term g (TArr TNat (TArr TNat TNat))
plusTerm =
  Mu (Lam (Lam
    (Case (Var (S Z))
      (Var Z)
      (Suc (App (App (Var (S (S (S Z)))) (Var Z)) (Var (S Z)))))))

-- | Intrinsically-typed recursive multiplication (`mul`): Nat -> Nat -> Nat.
-- μ "*". λ m. λ n. case m [ zero => zero | suc m' => plus n ("*" m' n) ]
mulTerm :: Term g (TArr TNat (TArr TNat TNat))
mulTerm =
  Mu (Lam (Lam
    (Case (Var (S Z))
      Zero
      (App (App plusTerm (Var (S Z)))
           (App (App (Var (S (S (S Z)))) (Var Z)) (Var (S Z)))))))
```

Because `termTwo`, `plusTerm`, and `mulTerm` are polymorphic in `g`, they are
valid in *any* context `g` (including `CEmpty`)—notice how `mulTerm` embeds
`plusTerm` directly inside its `Case` branch with zero manual weakening or
separate typing proofs!

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

## Intrinsically-typed Reduction (`Step`) and Complete Progress (`progress`)

In the intrinsically-typed representation, `Step` has kind
`forall (g :: Ctx) (a :: Ty). Term g a -> Term g a -> Type`—so **Preservation
holds automatically** by the very type of `Step`! Every reduction step connects
two terms of the *exact same* type `a` in the *exact same* context `g`.

With `-XDependentTypes`, all eight intrinsically-typed reduction rules
(`XiApp1`, `XiApp2`, `XiSuc`, `XiCase`, `BetaLam`, `BetaZero`, `BetaSuc`,
`BetaMu`) use our ordinary functional `substSingle` directly in this module,
**`progress`** proves across all seven term constructors that
every closed well-typed term is either a value or takes a type-preserving step
(carrying the next term `n` as a retained `foreach` field in `PStep`), and
PLFA's 6-line **`eval`** runs any closed term up to a fuel bound `Gas`,
returning a machine-checked reduction trace `Steps m n` alongside the final
value!

```haskell
-- | Intrinsically type-preserving call-by-value reduction (`M —→ N`).
-- Preservation holds automatically by the kind of `Step`!
type Step :: forall (g :: Ctx) (a :: Ty). Term g a -> Term g a -> Type
data Step m n where
  XiApp1   :: Step l l' -> Step (App l m) (App l' m)
  XiApp2   :: Value l -> Step m m' -> Step (App l m) (App l m')
  XiSuc    :: Step m m' -> Step (Suc m) (Suc m')
  XiCase   :: Step l l' -> Step (Case l m n) (Case l' m n)
  BetaLam  :: forall g a b (n :: Term (CExt g a) b) (w :: Term g a).
              Value w -> Step (App (Lam n) w) (substSingle n w)
  BetaZero :: forall g a (m :: Term g a) (n :: Term (CExt g TNat) a).
              Step (Case Zero m n) m
  BetaSuc  :: forall g a (m :: Term g a) (n :: Term (CExt g TNat) a)
                         (v :: Term g TNat).
              Value v -> Step (Case (Suc v) m n) (substSingle n v)
  BetaMu   :: forall g a (n :: Term (CExt g a) a).
              Step (Mu n) (substSingle n (Mu n))

-- | Reflexive-transitive closure of intrinsically-typed reduction (`M —↠ N`).
type Steps :: forall (g :: Ctx) (a :: Ty). Term g a -> Term g a -> Type
data Steps m n where
  StepsRefl :: Steps m m
  StepsCons :: Step l m -> Steps m n -> Steps l n

-- | Intrinsically-typed progress witness for closed terms, carrying the
-- next term `n` as a retained `foreach` field for executable `eval`.
type Progress :: forall (a :: Ty). Term CEmpty a -> Type
data Progress m where
  PStep :: foreach (n :: Term CEmpty a) -> Step m n -> Progress m
  PDone :: Value m -> Progress m

-- | Progress theorem for intrinsically-typed STLC:
-- every closed well-typed term is either a value or takes a type-preserving step.
progress :: forall (a :: Ty). foreach (m :: Term CEmpty a) -> Progress m
progress (Var x)      = case x of {}
progress (Lam _)      = PDone VLam
progress (App l m)    = case progress l of
  PStep l' s -> PStep (App l' m) (XiApp1 s)
  PDone v    -> case progress m of
    PStep m' s -> PStep (App l m') (XiApp2 v s)
    PDone w    -> appBeta l m v w
progress Zero         = PDone VZero
progress (Suc n)      = case progress n of
  PStep n' s -> sucStep @n n' s
  PDone v    -> PDone (VSuc v)
progress (Case l m n) = case progress l of
  PStep l' s -> PStep (Case l' m n) (XiCase s)
  PDone v    -> caseBeta l m n v
progress (Mu n)       = PStep (substSingle n (Mu n)) BetaMu

sucStep :: forall (n :: Term CEmpty TNat).
           foreach (n' :: Term CEmpty TNat)
        -> Step n n' -> Progress (Suc n)
sucStep n' s = PStep (Suc n') (XiSuc s)

-- | Application case factored out as a standalone helper given subterm progress.
appProgress
  :: forall (a :: Ty).
     (forall (b :: Ty). foreach (m :: Term CEmpty b) -> Progress m)
  -> foreach (t :: Term CEmpty a) -> Maybe (Progress t)
appProgress recProg (App l m) = case recProg l of
  PStep l' s -> Just (PStep (App l' m) (XiApp1 s))
  PDone v    -> case recProg m of
    PStep m' s -> Just (PStep (App l m') (XiApp2 v s))
    PDone w    -> Just (appBeta l m v w)
appProgress _ _ = Nothing

betaStep :: forall a b.
            foreach (body :: Term (CExt CEmpty a) b) -> foreach (m :: Term CEmpty a)
         -> Value m -> Progress (App (Lam body) m)
betaStep body m w = PStep (substSingle body m) (BetaLam w)

appBeta :: forall a b.
           foreach (l :: Term CEmpty (TArr a b)) -> foreach (m :: Term CEmpty a)
        -> Value l -> Value m -> Progress (App l m)
appBeta l = case l of
  Lam body   -> \m _ w -> betaStep body m w
  Var x      -> \_ _ _ -> case x of {}
  App _ _    -> \_ v _ -> case v of {}
  Case _ _ _ -> \_ v _ -> case v of {}
  Mu _       -> \_ v _ -> case v of {}

caseBetaSuc :: forall a.
               foreach (p :: Term CEmpty TNat)
            -> foreach (n :: Term (CExt CEmpty TNat) a)
            -> forall (m :: Term CEmpty a). Value p -> Progress (Case (Suc p) m n)
caseBetaSuc p n w = PStep (substSingle n p) (BetaSuc w)

caseBeta :: forall a.
            foreach (l :: Term CEmpty TNat)
         -> foreach (m :: Term CEmpty a)
         -> foreach (n :: Term (CExt CEmpty TNat) a)
         -> Value l -> Progress (Case l m n)
caseBeta l = case l of
  Zero       -> \m _ _ -> PStep m BetaZero
  Suc p      -> \_ n v -> case v of { VSuc w -> caseBetaSuc p n w }
  Var x      -> \_ _ _ -> case x of {}
  App _ _    -> \_ _ v -> case v of {}
  Case _ _ _ -> \_ _ v -> case v of {}
  Mu _       -> \_ _ v -> case v of {}

-- | Fuel bound for gas-bounded intrinsically-typed evaluation (`Gas`).
newtype Gas = MkGas N.Nat

-- | Evaluation outcome for a closed term `m`, pairing the final term `n`
-- with its machine-checked reduction trace `Steps m n`.
type Finished :: forall (a :: Ty). Term CEmpty a -> Type
data Finished m where
  Done     :: foreach (n :: Term CEmpty a) -> Steps m n -> Value n -> Finished m
  OutOfGas :: foreach (n :: Term CEmpty a) -> Steps m n -> Finished m

-- | PLFA's 6-line intrinsically-typed evaluator (`eval`):
-- steps any closed term up to the fuel bound while certifying type preservation!
eval :: forall (a :: Ty). Gas -> foreach (m :: Term CEmpty a) -> Finished m
eval gas m = case gas of
  MkGas N.Zero     -> OutOfGas m StepsRefl
  MkGas (N.Succ g) -> case progress m of
    PDone v   -> Done m StepsRefl v
    PStep n s -> case eval (MkGas g) n of
      Done     vTerm ss v -> Done     vTerm (StepsCons s ss) v
      OutOfGas kTerm ss   -> OutOfGas kTerm (StepsCons s ss)

-- | Concrete β-reduction: (λ. 0) 0 —→ 0.
betaIdStep :: Step (App (Lam (Var Z)) Zero) Zero
betaIdStep = BetaLam VZero

-- | Concrete substitution under a binder: (λ. λ. 1) 0 —→ λ. 0.
betaCaptureAvoid :: Step (App (Lam (Lam (Var (S Z)))) Zero) (Lam Zero)
betaCaptureAvoid = BetaLam VZero

-- | Capture-avoiding substitution of an open value under a binder:
-- in context (∅, Nat), substituting `w = λ. Var (S Z)` (which references the
-- free outer Nat) into `λ. Var (S Z)` shifts `w`'s free variable to `S (S Z)`!
betaShiftUnderLam
  :: Step @(CExt CEmpty TNat)
          @(TArr TNat (TArr TNat TNat))
          (App (Lam (Lam (Var (S Z)))) (Lam (Var (S Z))))
          (Lam (Lam (Var (S (S Z)))))
betaShiftUnderLam = BetaLam VLam
```

### Negative control: forged variable capture is rejected

When substituting the open value `λ. Var (S Z)` under an inner binder,
`substSingle` must shift its free variable to `S (S Z)` (`betaShiftUnderLam`).
Claiming the unshifted (capturing) result `Lam (Lam (Var (S Z)))` is rejected
by GHC with `GHC-83865`:

```{.haskell .fail name="NegDeBruijnBadCapture" expect="GHC-83865"}
{-# LANGUAGE DependentTypes #-}
module NegDeBruijnBadCapture (badCapture) where

import qualified PLFH.Part2.DeBruijn as D

badCapture
  :: D.Step @(D.CExt D.CEmpty D.TNat)
            @(D.TArr D.TNat (D.TArr D.TNat D.TNat))
            (D.App (D.Lam (D.Lam (D.Var (D.S D.Z)))) (D.Lam (D.Var (D.S D.Z))))
            (D.Lam (D.Lam (D.Var (D.S D.Z))))
badCapture = D.BetaLam D.VLam
```

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
- All eight intrinsically-typed `Step` rules (using functional
  `substSingle`), concrete capture-avoiding beta
  witnesses, complete
  `progress` across all 7 term constructors (carrying retained
  `foreach n` inside `PStep`), and PLFA's 6-line intrinsically-typed evaluator
  `eval` (`Gas`, `Finished`) compile inline in `PLFH.Part2.DeBruijn`.
