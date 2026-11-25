---
title: "More: Additional constructs of simply-typed lambda calculus"
prev: /Untyped/
next: /Bisimulation/
src: content/part2/More.md
module: PLFH.Part2.More
plfaChapter: https://plfa.inf.ed.ac.uk/More/
---

Real functional programming languages offer far more than just functions and
natural numbers! Following PLFA's **More** chapter, we scale our
intrinsically-typed de Bruijn simply-typed lambda calculus from
[DeBruijn](/DeBruijn/) into a rich core functional language supporting:

- **Local `let` bindings** (`Let`, binding a computed value to variable `Z`),
- **Unit (`TUnit`, `TT`)** and **Products (`TProd`, `Pair`, `Fst`, `Snd`)** —
  the computational counterparts of `⊤` and `×` from [Connectives](/Connectives/),
- **Empty type / Void (`TVoid`, `Absurd`)** and **Sums (`TSum`, `Inl`, `Inr`,
  `CaseSum`)** — the computational counterparts of `⊥` and `⊎`,
- **Lists (`TList`, `Nil`, `Cons`, `CaseLst`)** — an inductive algebraic
  datatype whose `Cons` case branch binds **two** variables simultaneously
  (head and tail)!

By the **Curry–Howard correspondence** (propositions as types, proofs as
programs), every single typing rule below matches the corresponding
introduction (`-I`) and elimination (`-E`) rule of intuitionistic propositional
logic—for example, `Absurd` is *ex falso quodlibet*, `Pair`/`Fst`/`Snd` are
conjunction introduction and projections, and `Inl`/`Inr`/`CaseSum` are
disjunction introduction and case analysis!

## Imports

```haskell
{-# LANGUAGE DependentTypes #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
module PLFH.Part2.More
  ( Ty (..)
  , Ctx (..)
  , Lookup (..)
  , Term (..)
  , weakenLookup
  , ext
  , rename
  , exts
  , subst
  , singleSubst
  , doubleSubst
  , substSingle
  , substDouble
  , Value (..)
  , swapPair
  , mapMaybeNat
  , TBool
  , tTrue
  , tFalse
  , ifThenElse
  , swapSum
  , appendList
  , Step (..)
  , Steps (..)
  , Progress (..)
  , progress
  , listCaseBoth
  ) where

import Data.Kind (Type)
```

## Extended types, contexts, and intrinsically-typed terms

Each new type constructor brings its own introduction and elimination forms:

| Type (`Ty`) | Introduction forms | Elimination forms | Binders introduced |
| --- | --- | --- | --- |
| `TNat` | `Zero`, `Suc` | `CaseNat` | `1` (predecessor in `Suc` branch) |
| `TArr a b` | `Lam` | `App` | `1` (parameter in `Lam`) |
| `TUnit` | `TT` | *(none)* | `0` |
| `TProd a b` | `Pair` | `Fst`, `Snd` | `0` |
| `TSum a b` | `Inl`, `Inr` | `CaseSum` | `1` in each branch (`a` and `b`) |
| `TVoid` | *(none)* | `Absurd` | `0` |
| `TList a` | `Nil`, `Cons` | `CaseLst` | `2` (head `a` and tail `TList a`) |
| *(any `b`)* | — | `Let` / `Mu` | `1` |

Notice how `Let m n` can also be viewed as syntactic sugar for `App (Lam n) m`
under call-by-value—a correspondence we prove formally as a lock-step
bisimulation in [Bisimulation](/Bisimulation/)! (Similarly, PLFA introduces
pattern-matching `case p of (x, y) => n` as an exercise alongside `Fst`/`Snd`.)

```haskell
-- | Extended simple types: naturals, unit, void, arrows, products, sums, lists.
data Ty
  = TNat
  | TUnit
  | TVoid
  | TArr Ty Ty
  | TProd Ty Ty
  | TSum Ty Ty
  | TList Ty
  deriving (Show)

data Ctx = CEmpty | CExt Ctx Ty

data Lookup (g :: Ctx) (a :: Ty) where
  Z :: Lookup (CExt g a) a
  S :: Lookup g a -> Lookup (CExt g b) a

-- | Intrinsically typed terms for the extended simply-typed lambda calculus.
data Term (g :: Ctx) (a :: Ty) where
  Var     :: Lookup g a -> Term g a
  Lam     :: Term (CExt g a) b -> Term g (TArr a b)
  App     :: Term g (TArr a b) -> Term g a -> Term g b
  Zero    :: Term g TNat
  Suc     :: Term g TNat -> Term g TNat
  CaseNat :: Term g TNat -> Term g a -> Term (CExt g TNat) a -> Term g a
  Mu      :: Term (CExt g a) a -> Term g a
  Let     :: Term g a -> Term (CExt g a) b -> Term g b
  TT      :: Term g TUnit
  Pair    :: Term g a -> Term g b -> Term g (TProd a b)
  Fst     :: Term g (TProd a b) -> Term g a
  Snd     :: Term g (TProd a b) -> Term g b
  Inl     :: Term g a -> Term g (TSum a b)
  Inr     :: Term g b -> Term g (TSum a b)
  CaseSum :: Term g (TSum a b) -> Term (CExt g a) c -> Term (CExt g b) c -> Term g c
  Absurd  :: Term g TVoid -> Term g a
  Nil     :: Term g (TList a)
  Cons    :: Term g a -> Term g (TList a) -> Term g (TList a)
  CaseLst :: Term g (TList a) -> Term g b -> Term (CExt (CExt g a) (TList a)) b -> Term g b
```

## Renaming and capture-avoiding single & double substitution

Simultaneous renaming (`rename`) and simultaneous substitution (`subst`) scale
effortlessly to all 19 term constructors! Look closely at **`CaseLst`**: because
its `Cons` branch binds *two* variables (`x : a` and `xs : TList a`, with `xs`
at `Z` and `x` at `S Z`), we simply lift `ext` and `exts` twice (`ext (ext r)`
and `exts (exts s)`).

Likewise, contracting a `CaseLst` on `Cons v vs` requires substituting *two*
terms simultaneously—so in addition to `substSingle` (for `Lam`, `Let`, `Mu`,
`CaseNat`, and `CaseSum`), we define **`substDouble`** mapping `Z -> w`,
`S Z -> v`, and `S (S x) -> Var x`!

```haskell
ext :: (forall a. Lookup g a -> Lookup d a)
    -> (forall a. Lookup (CExt g b) a -> Lookup (CExt d b) a)
ext _ Z     = Z
ext r (S x) = S (r x)

rename :: (forall a. Lookup g a -> Lookup d a) -> Term g b -> Term d b
rename r (Var x)          = Var (r x)
rename r (Lam n)          = Lam (rename (ext r) n)
rename r (App l m)        = App (rename r l) (rename r m)
rename _ Zero             = Zero
rename r (Suc m)          = Suc (rename r m)
rename r (CaseNat l m n)  = CaseNat (rename r l) (rename r m) (rename (ext r) n)
rename r (Mu n)           = Mu (rename (ext r) n)
rename r (Let m n)        = Let (rename r m) (rename (ext r) n)
rename _ TT               = TT
rename r (Pair m n)       = Pair (rename r m) (rename r n)
rename r (Fst p)          = Fst (rename r p)
rename r (Snd p)          = Snd (rename r p)
rename r (Inl m)          = Inl (rename r m)
rename r (Inr m)          = Inr (rename r m)
rename r (CaseSum s l m)  = CaseSum (rename r s) (rename (ext r) l) (rename (ext r) m)
rename r (Absurd m)       = Absurd (rename r m)
rename _ Nil              = Nil
rename r (Cons x xs)      = Cons (rename r x) (rename r xs)
rename r (CaseLst xs n c) = CaseLst (rename r xs) (rename r n) (rename (ext (ext r)) c)

weakenLookup :: forall d b a. Lookup d a -> Lookup (CExt d b) a
weakenLookup x = S x

exts :: forall g d b.
        (forall a. Lookup g a -> Term d a)
     -> (forall a. Lookup (CExt g b) a -> Term (CExt d b) a)
exts _ Z     = Var Z
exts s (S x) = rename weakenLookup (s x)

subst :: (forall a. Lookup g a -> Term d a) -> Term g b -> Term d b
subst s (Var x)          = s x
subst s (Lam n)          = Lam (subst (exts s) n)
subst s (App l m)        = App (subst s l) (subst s m)
subst _ Zero             = Zero
subst s (Suc m)          = Suc (subst s m)
subst s (CaseNat l m n)  = CaseNat (subst s l) (subst s m) (subst (exts s) n)
subst s (Mu n)           = Mu (subst (exts s) n)
subst s (Let m n)        = Let (subst s m) (subst (exts s) n)
subst _ TT               = TT
subst s (Pair m n)       = Pair (subst s m) (subst s n)
subst s (Fst p)          = Fst (subst s p)
subst s (Snd p)          = Snd (subst s p)
subst s (Inl m)          = Inl (subst s m)
subst s (Inr m)          = Inr (subst s m)
subst s (CaseSum e l m)  = CaseSum (subst s e) (subst (exts s) l) (subst (exts s) m)
subst s (Absurd m)       = Absurd (subst s m)
subst _ Nil              = Nil
subst s (Cons x xs)      = Cons (subst s x) (subst s xs)
subst s (CaseLst xs n c) = CaseLst (subst s xs) (subst s n) (subst (exts (exts s)) c)

singleSubst :: forall g a. Term g a -> (forall b. Lookup (CExt g a) b -> Term g b)
singleSubst w Z     = w
singleSubst _ (S x) = Var x

doubleSubst :: forall g a b. Term g a -> Term g b
            -> (forall c. Lookup (CExt (CExt g a) b) c -> Term g c)
doubleSubst _ w Z         = w
doubleSubst v _ (S Z)     = v
doubleSubst _ _ (S (S x)) = Var x

substSingle :: Term (CExt g a) b -> Term g a -> Term g b
substSingle n w = subst (singleSubst w) n

substDouble :: Term (CExt (CExt g a) b) c -> Term g a -> Term g b -> Term g c
substDouble n v w = subst (doubleSubst v w) n
```

## Values and example programs

In call-by-value, every data constructor produces a value once its arguments
are values (`VTT`, `VPair`, `VInl`, `VInr`, `VNil`, `VCons`), while `TVoid` has
**no value constructors at all** (mirroring the fact that no closed well-typed
program of type `TVoid` can ever terminate at a value!):

```haskell
-- | Values indexed over promoted extended `Term g a`.
type Value :: forall (g :: Ctx) (a :: Ty). Term g a -> Type
data Value m where
  VLam  :: Value (Lam n)
  VZero :: Value Zero
  VSuc  :: Value v -> Value (Suc v)
  VTT   :: Value TT
  VPair :: Value v -> Value w -> Value (Pair v w)
  VInl  :: Value v -> Value (Inl v)
  VInr  :: Value v -> Value (Inr v)
  VNil  :: Value Nil
  VCons :: Value v -> Value vs -> Value (Cons v vs)

-- | Example: swap the components of a pair: λp. (snd p, fst p).
swapPair :: Term g (TArr (TProd a b) (TProd b a))
swapPair = Lam (Pair (Snd (Var Z)) (Fst (Var Z)))

-- | Example: unwrap a `Sum Unit Nat` (Maybe Nat) defaulting to Zero.
mapMaybeNat :: Term g (TArr (TSum TUnit TNat) TNat)
mapMaybeNat = Lam (CaseSum (Var Z) Zero (Var Z))

-- | Booleans encoded as `Unit + Unit` (`Bool ≃ ⊤ ⊎ ⊤`).
type TBool = TSum TUnit TUnit

tTrue :: Term g TBool
tTrue = Inl TT

tFalse :: Term g TBool
tFalse = Inr TT

-- | Conditional expression over `TBool`.
ifThenElse :: Term g (TArr TBool (TArr a (TArr a a)))
ifThenElse = Lam (Lam (Lam (CaseSum (Var (S (S Z))) (Var (S (S Z))) (Var (S Z)))))

-- | Commutativity of sums inside our object language: λs. case s of Inl x -> Inr x | Inr y -> Inl y.
swapSum :: Term g (TArr (TSum a b) (TSum b a))
swapSum = Lam (CaseSum (Var Z) (Inr (Var Z)) (Inl (Var Z)))

-- | Intrinsically-typed recursive list append (`++`) using `Mu` and `CaseLst`.
appendList :: Term g (TArr (TList a) (TArr (TList a) (TList a)))
appendList =
  Mu (Lam (Lam
    (CaseLst (Var (S Z))
      (Var Z)
      (Cons (Var (S Z)) (App (App (Var (S (S (S (S Z))))) (Var Z)) (Var (S (S Z))))))))
```

## Extended call-by-value reduction (`Step`) and Complete Progress (`progress`)

With `-XDependentTypes`, GHC evaluates both single-variable `substSingle` and
two-variable `substDouble` (lifting through double binders `ext (ext r)` and
`exts (exts s)` for `CaseLst`!) directly in the same module—so we define all
**27 intrinsically-typed call-by-value reduction rules** (`Step`), complete
unconditional **`progress`** across all **19 constructors** of `Term` (checked
with `-Werror=incomplete-patterns`, where `absurdProgress` discharges
`PDone v -> case v of {}` statically because `TVoid` has no value constructors!),
and the concrete double-substitution witness `listCaseBoth` inline right here:

```haskell
-- | Intrinsically type-preserving call-by-value reduction for extended STLC (27 rules!).
type Step :: forall (g :: Ctx) (a :: Ty). Term g a -> Term g a -> Type
data Step before after where
  XiApp1    :: Step f f' -> Step (App f x) (App f' x)
  XiApp2    :: Value f -> Step x x' -> Step (App f x) (App f x')
  BetaLam   :: forall g a b (body :: Term (CExt g a) b) (v :: Term g a).
               Value v -> Step (App (Lam body) v) (substSingle body v)

  XiSuc     :: Step n n' -> Step (Suc n) (Suc n')
  XiCaseNat :: Step n n' -> Step (CaseNat n z s) (CaseNat n' z s)
  BetaZero  :: Step (CaseNat Zero z s) z
  BetaSuc   :: forall g a (z :: Term g a) (s :: Term (CExt g TNat) a)
                      (v :: Term g TNat).
               Value v -> Step (CaseNat (Suc v) z s) (substSingle s v)
  BetaMu    :: forall g a (body :: Term (CExt g a) a).
               Step (Mu body) (substSingle body (Mu body))

  XiLet     :: Step m m' -> Step (Let m body) (Let m' body)
  BetaLet   :: forall g a b (m :: Term g a) (body :: Term (CExt g a) b).
               Value m -> Step (Let m body) (substSingle body m)

  XiPair1   :: Step l l' -> Step (Pair l r) (Pair l' r)
  XiPair2   :: Value l -> Step r r' -> Step (Pair l r) (Pair l r')
  XiFst     :: Step p p' -> Step (Fst p) (Fst p')
  XiSnd     :: Step p p' -> Step (Snd p) (Snd p')
  BetaFst   :: Value l -> Value r -> Step (Fst (Pair l r)) l
  BetaSnd   :: Value l -> Value r -> Step (Snd (Pair l r)) r

  XiInl     :: Step x x' -> Step (Inl x) (Inl x')
  XiInr     :: Step y y' -> Step (Inr y) (Inr y')
  XiCaseSum :: Step s s' -> Step (CaseSum s l r) (CaseSum s' l r)
  BetaInl   :: forall g a b c (l :: Term (CExt g a) c)
                      (r :: Term (CExt g b) c) (x :: Term g a).
               Value x -> Step (CaseSum (Inl x) l r) (substSingle l x)
  BetaInr   :: forall g a b c (l :: Term (CExt g a) c)
                      (r :: Term (CExt g b) c) (y :: Term g b).
               Value y -> Step (CaseSum (Inr y) l r) (substSingle r y)
  XiAbsurd  :: Step m m' -> Step (Absurd m) (Absurd m')

  XiCons1   :: Step x x' -> Step (Cons x xs) (Cons x' xs)
  XiCons2   :: Value x -> Step xs xs' -> Step (Cons x xs) (Cons x xs')
  XiCaseLst :: Step s s' -> Step (CaseLst s n c) (CaseLst s' n c)
  BetaNil   :: Step (CaseLst Nil n c) n
  BetaCons  :: forall g a b (n :: Term g b)
                      (c :: Term (CExt (CExt g a) (TList a)) b)
                      (x :: Term g a) (xs :: Term g (TList a)).
               Value x -> Value xs
            -> Step (CaseLst (Cons x xs) n c) (substDouble c x xs)

-- | Reflexive-transitive closure of extended STLC reduction (`M —↠ N`).
type Steps :: forall (g :: Ctx) (a :: Ty). Term g a -> Term g a -> Type
data Steps m n where
  StepsRefl :: Steps m m
  StepsCons :: Step l m -> Steps m n -> Steps l n

-- | A closed term in the extended language either steps or is a value.
type Progress :: forall (a :: Ty). Term CEmpty a -> Type
data Progress m where
  PStep :: Step m n -> Progress m
  PDone :: Value m -> Progress m

-- | Complete, unconditional Progress theorem across all 19 constructors of `Term`!
progress :: forall (a :: Ty). foreach (m :: Term CEmpty a) -> Progress m
progress (Var x)         = case x of {}
progress (Lam _)         = PDone VLam
progress (App f x)       = appProgress (progress f) (progress x)
progress Zero            = PDone VZero
progress (Suc n)         = sucProgress (progress n)
progress (CaseNat n _ _) = natCaseProgress (progress n)
progress (Mu body)       = PStep (BetaMu @CEmpty @a @body)
progress (Let m _)       = letProgress (progress m)
progress TT              = PDone VTT
progress (Pair l r)      = pairProgress (progress l) (progress r)
progress (Fst p)         = fstProgress (progress p)
progress (Snd p)         = sndProgress (progress p)
progress (Inl x)         = inlProgress (progress x)
progress (Inr y)         = inrProgress (progress y)
progress (CaseSum s _ _) = sumCaseProgress (progress s)
progress (Absurd m)      = absurdProgress (progress m)
progress Nil             = PDone VNil
progress (Cons x xs)     = consProgress (progress x) (progress xs)
progress (CaseLst s _ _) = listCaseProgress (progress s)

appProgress :: forall a b (f :: Term CEmpty (TArr a b)) (x :: Term CEmpty a).
               Progress f -> Progress x -> Progress (App f x)
appProgress (PStep s) _         = PStep (XiApp1 s)
appProgress (PDone v) (PStep s) = PStep (XiApp2 v s)
appProgress (PDone VLam) (PDone v) = PStep (BetaLam v)

sucProgress :: Progress n -> Progress (Suc n)
sucProgress (PStep s) = PStep (XiSuc s)
sucProgress (PDone v) = PDone (VSuc v)

natCaseProgress :: forall a (n :: Term CEmpty TNat) (z :: Term CEmpty a)
                          (s :: Term (CExt CEmpty TNat) a).
                   Progress n -> Progress (CaseNat n z s)
natCaseProgress (PStep step)      = PStep (XiCaseNat step)
natCaseProgress (PDone VZero)     = PStep BetaZero
natCaseProgress (PDone (VSuc val)) = PStep (BetaSuc val)

letProgress :: forall a b (m :: Term CEmpty a) (body :: Term (CExt CEmpty a) b).
               Progress m -> Progress (Let m body)
letProgress (PStep s) = PStep (XiLet s)
letProgress (PDone v) = PStep (BetaLet v)

pairProgress :: Progress l -> Progress r -> Progress (Pair l r)
pairProgress (PStep s) _         = PStep (XiPair1 s)
pairProgress (PDone v) (PStep s) = PStep (XiPair2 v s)
pairProgress (PDone v) (PDone w) = PDone (VPair v w)

fstProgress :: Progress p -> Progress (Fst p)
fstProgress (PStep s)           = PStep (XiFst s)
fstProgress (PDone (VPair v w)) = PStep (BetaFst v w)

sndProgress :: Progress p -> Progress (Snd p)
sndProgress (PStep s)           = PStep (XiSnd s)
sndProgress (PDone (VPair v w)) = PStep (BetaSnd v w)

inlProgress :: Progress x -> Progress (Inl x)
inlProgress (PStep s) = PStep (XiInl s)
inlProgress (PDone v) = PDone (VInl v)

inrProgress :: Progress y -> Progress (Inr y)
inrProgress (PStep s) = PStep (XiInr s)
inrProgress (PDone v) = PDone (VInr v)

sumCaseProgress :: forall a b c (s :: Term CEmpty (TSum a b))
                          (l :: Term (CExt CEmpty a) c)
                          (r :: Term (CExt CEmpty b) c).
                   Progress s -> Progress (CaseSum s l r)
sumCaseProgress (PStep step)    = PStep (XiCaseSum step)
sumCaseProgress (PDone (VInl v)) = PStep (BetaInl v)
sumCaseProgress (PDone (VInr v)) = PStep (BetaInr v)

absurdProgress :: Progress m -> Progress (Absurd m)
absurdProgress (PStep s) = PStep (XiAbsurd s)
absurdProgress (PDone v) = case v of {}

consProgress :: Progress x -> Progress xs -> Progress (Cons x xs)
consProgress (PStep s) _          = PStep (XiCons1 s)
consProgress (PDone v) (PStep s)  = PStep (XiCons2 v s)
consProgress (PDone v) (PDone vs) = PDone (VCons v vs)

listCaseProgress :: forall a b (s :: Term CEmpty (TList a)) (n :: Term CEmpty b)
                           (c :: Term (CExt (CExt CEmpty a) (TList a)) b).
                    Progress s -> Progress (CaseLst s n c)
listCaseProgress (PStep step)            = PStep (XiCaseLst step)
listCaseProgress (PDone VNil)            = PStep BetaNil
listCaseProgress (PDone (VCons v vs))    = PStep (BetaCons v vs)

-- | Concrete `BetaCons` witness exercising `substDouble`:
-- `S Z` receives the head (`Suc Zero`) and `Z` receives the tail (`Cons Zero Nil`)!
listCaseBoth
  :: Step @CEmpty @(TProd TNat (TList TNat))
          (CaseLst (Cons (Suc Zero) (Cons Zero Nil))
                   (Pair Zero Nil)
                   (Pair (Var (S Z)) (Var Z)))
          (Pair (Suc Zero) (Cons Zero Nil))
listCaseBoth = BetaCons (VSuc VZero) (VCons VZero VNil)
```

### Negative control: forged `BetaCons` double-substitution target is rejected

In `listCaseBoth`, `CaseLst (Cons (Suc Zero) (Cons Zero Nil)) ... (Pair (Var (S Z)) (Var Z))`
substitutes `Suc Zero` for `S Z` and `Cons Zero Nil` for `Z`. Claiming the head
became `Zero` instead of `Suc Zero` is rejected by GHC with `GHC-83865`:

```{.haskell .fail name="NegMoreConsTarget" expect="GHC-83865"}
{-# LANGUAGE DependentTypes #-}
module NegMoreConsTarget (wrongHead) where

import qualified PLFH.Part2.More as M

wrongHead :: M.Step @M.CEmpty @(M.TProd M.TNat (M.TList M.TNat))
                    (M.CaseLst (M.Cons (M.Suc M.Zero) (M.Cons M.Zero M.Nil))
                               (M.Pair M.Zero M.Nil)
                               (M.Pair (M.Var (M.S M.Z)) (M.Var M.Z)))
                    (M.Pair M.Zero (M.Cons M.Zero M.Nil))
wrongHead = M.BetaCons (M.VSuc M.VZero) (M.VCons M.VZero M.VNil)
```

## Exercises

#### Exercise `bool-as-sum` (practice)

Represent Booleans as `type TBool = TSum TUnit TUnit` (`true = Inl TT`,
`false = Inr TT`) and write an intrinsically-typed `ifThenElse` combinator
`Term g (TArr TBool (TArr a (TArr a a)))` using `CaseSum`.

#### Exercise `append-list` (recommended)

Write an intrinsically-typed list append function
`Term CEmpty (TArr (TList a) (TArr (TList a) (TList a)))` using `Mu`, `Lam`,
`CaseLst`, and `Cons`, carefully tracking the two variables bound by `CaseLst`
(`Z` for the tail, `S Z` for the head)!

#### Exercise `sum-comm` (practice)

Construct `swapSum :: Term g (TArr (TSum a b) (TSum b a))` using `Lam`,
`CaseSum`, `Inr`, and `Inl`.

## Changes from PLFA

- Adapted from [More](https://plfa.inf.ed.ac.uk/More/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/More.lagda.md)),
  licensed under CC BY 4.0.
- All extended constructs (`Let`, `TUnit`, `TProd`, `TSum`, `TVoid`, `TList`),
  renaming, substitution (`substSingle`, `substDouble`), GADT-promoted `Value`,
  example programs, all 27 intrinsically-typed `Step` rules (using real
  `substSingle` and `substDouble` directly in the same module), complete
  unconditional 19-branch `progress` (`-Werror=incomplete-patterns`), and
  concrete `listCaseBoth` (guarded by negative control `NegMoreConsTarget`)
  compile inline in `PLFH.Part2.More` with `-dcore-lint -dstg-lint` and zero
  promoted-constructor ticks.
