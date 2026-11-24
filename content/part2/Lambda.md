---
title: "Lambda: Introduction to Lambda Calculus"
prev: /Lists/
next: /Properties/
src: content/part2/Lambda.md
module: PLFH.Part2.Lambda
plfaChapter: https://plfa.inf.ed.ac.uk/Lambda/
---

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, ExplicitForAll, GADTs, TypeOperators #-}
module PLFH.Part2.Lambda
  ( Id
  , eqId
  , Term (..)
  , Ty (..)
  , Ctx (..)
  , Value (..)
  , substTerm
  , Step (..)
  , Steps (..)
  , Lookup (..)
  , HasType (..)
  , termTwo
  , twoTyped
  ) where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..))
import PLFH.Part1.Decidable (Not)
```

Welcome to Part 2: **Programming Language Foundations**. Following PLFA,
we formalize the simply-typed lambda calculus with natural numbers, case
analysis, and general recursion (`μ` / `fix`).

In this chapter we define:

1. Abstract syntax of terms (`Term`), types (`Ty`), and typing contexts (`Ctx`),
2. Values (`Value`),
3. Capture-avoiding substitution for closed terms (`substTerm`),
4. Call-by-value reduction (`Step` and `Steps`), and
5. Extrinsic typing derivations (`Lookup` and `HasType`).

## Syntax of terms, types, and contexts

PLFA uses `Id = String` for variable names. Here we use structural Peano
identifiers `type Id = Nat` (representing variable names `x0`, `x1`, `x2`, …)
so identifier equality `eqId` is an ordinary structural Haskell function on
a closed algebraic datatype:

```haskell
-- | Variable identifiers represented structurally as Peano naturals.
type Id = Nat

-- | Structural equality on variable identifiers.
eqId :: Id -> Id -> Bool
eqId Zero     Zero     = True
eqId Zero     (Succ _) = False
eqId (Succ _) Zero     = False
eqId (Succ m) (Succ n) = eqId m n

-- | Untyped lambda calculus terms with naturals, case, and μ-recursion.
data Term
  = Var Id
  | Lam Id Term
  | App Term Term
  | TZero
  | TSuc Term
  | TCase Term Term Id Term
  | TMu Id Term
  deriving (Show)

-- | Simple types: natural numbers and functions.
data Ty
  = TNat
  | TArr Ty Ty
  deriving (Show)

-- | Typing contexts associating variable identifiers with types.
data Ctx
  = CEmpty
  | CExt Ctx Id Ty
  deriving (Show)
```

## Values

A term is a *value* if it is a lambda abstraction, zero, or the successor
of a value:

```haskell
-- | Evidence that a term is a call-by-value value.
data Value (t :: Term) where
  VLam  :: Value ('Lam x n)
  VZero :: Value 'TZero
  VSuc  :: Value v -> Value ('TSuc v)
```

## Substitution (`_[_:=_]`)

Following PLFA, `substTerm m y v` substitutes the closed term `v` for free
occurrences of variable `y` in term `m`:

```haskell
-- | Substitute a closed term `v` for free occurrences of `y` in `m`.
substTerm :: Term -> Id -> Term -> Term
substTerm (Var x) y v = case eqId x y of
  True  -> v
  False -> Var x
substTerm (Lam x n) y v = case eqId x y of
  True  -> Lam x n
  False -> Lam x (substTerm n y v)
substTerm (App l m) y v = App (substTerm l y v) (substTerm m y v)
substTerm TZero _ _ = TZero
substTerm (TSuc m) y v = TSuc (substTerm m y v)
substTerm (TCase l m x n) y v = case eqId x y of
  True  -> TCase (substTerm l y v) (substTerm m y v) x n
  False -> TCase (substTerm l y v) (substTerm m y v) x (substTerm n y v)
substTerm (TMu x n) y v = case eqId x y of
  True  -> TMu x n
  False -> TMu x (substTerm n y v)
```

## One-step and multi-step reduction (`_—→_`, `_—↠_`)

Call-by-value one-step reduction is an indexed GADT `Step m n` (written
`M —→ N` in PLFA), using our ordinary `substTerm` function directly in
`BetaLam`, `BetaSuc`, and `BetaMu`:

```haskell
-- | Call-by-value one-step reduction relation (M —→ N).
data Step (m :: Term) (n :: Term) where
  XiApp1   :: Step l l' -> Step ('App l m) ('App l' m)
  XiApp2   :: Value v -> Step m m' -> Step ('App v m) ('App v m')
  BetaLam  :: forall v x n. Value v -> Step ('App ('Lam x n) v) (substTerm n x v)
  XiSuc    :: Step m m' -> Step ('TSuc m) ('TSuc m')
  XiCase   :: Step l l' -> Step ('TCase l m x n) ('TCase l' m x n)
  BetaZero :: Step ('TCase 'TZero m x n) m
  BetaSuc  :: forall v m x n. Value v -> Step ('TCase ('TSuc v) m x n) (substTerm n x v)
  BetaMu   :: forall x m. Step ('TMu x m) (substTerm m x ('TMu x m))

-- | Reflexive-transitive closure of one-step reduction (M —↠ N).
data Steps (m :: Term) (n :: Term) where
  StepsRefl :: Steps m m
  StepsCons :: Step l m -> Steps m n -> Steps l n
```

The three beta constructors bind their term indices explicitly, and each result
uses the ordinary `substTerm` function defined above. The negative control
below verifies that GHC rejects an arbitrary reduction target.

## Context lookup and typing (`_∋_⦂_`, `_⊢_⦂_`)

Context lookup ensures shadowing is respected by requiring `Not (x :~: y)`
whenever skipping past a binding for `y`:

```haskell
-- | Evidence that variable `x` has type `a` in context `g` (Γ ∋ x ⦂ A).
data Lookup (g :: Ctx) (x :: Id) (a :: Ty) where
  LZ :: Lookup ('CExt g x a) x a
  LS :: Not (x :~: y) -> Lookup g x a -> Lookup ('CExt g y b) x a

-- | Extrinsic typing derivation (Γ ⊢ M ⦂ A).
data HasType (g :: Ctx) (m :: Term) (a :: Ty) where
  TVar   :: Lookup g x a -> HasType g ('Var x) a
  TLam   :: HasType ('CExt g x a) n b -> HasType g ('Lam x n) ('TArr a b)
  TApp   :: HasType g l ('TArr a b) -> HasType g m a -> HasType g ('App l m) b
  TZeroT :: HasType g 'TZero 'TNat
  TSucT  :: HasType g m 'TNat -> HasType g ('TSuc m) 'TNat
  TCaseT :: HasType g l 'TNat -> HasType g m a -> HasType ('CExt g x 'TNat) n a
         -> HasType g ('TCase l m x n) a
  TMuT   :: HasType ('CExt g x a) m a -> HasType g ('TMu x m) a
```

### Example: the numeral `2` and its typing derivation

```haskell
-- | The term representing natural number 2.
termTwo :: Term
termTwo = TSuc (TSuc TZero)

-- | Typing derivation showing ∅ ⊢ suc (suc zero) : Nat.
twoTyped :: HasType 'CEmpty ('TSuc ('TSuc 'TZero)) 'TNat
twoTyped = TSucT (TSucT TZeroT)
```

### Negative control: ill-typed application is rejected

Trying to apply `TZero` (which has type `'TNat`) as a function is rejected
by GHC with `GHC-83865`:

```{.haskell .fail name="NegIllTypedApp" expect="GHC-83865"}
{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs #-}
module NegIllTypedApp (badApp) where

import PLFH.Part2.Lambda (Ctx (..), HasType (..), Term (..), Ty (..))

badApp :: HasType 'CEmpty ('App 'TZero 'TZero) 'TNat
badApp = TApp TZeroT TZeroT
```

### Negative control: a beta step must compute its target

The term `TMu Zero TZero` unfolds to `TZero`. The following step has a
different target and GHC rejects it.

```{.haskell .fail name="NegBetaMuTarget" expect="GHC-83865"}
{-# LANGUAGE DataKinds, GADTs #-}
module NegBetaMuTarget (wrong) where

import HaskLib.Nat (Nat (Zero))
import PLFH.Part2.Lambda (Step (..), Term (..))

wrong :: Step ('TMu 'Zero 'TZero)
              ('TCase 'TZero 'TZero 'Zero ('TMu 'Zero 'TZero))
wrong = BetaMu
```

## Changes from PLFA

- Adapted from [Lambda](https://plfa.inf.ed.ac.uk/Lambda/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/Lambda.lagda.md)).
- Replaced `Id = String` with structural `type Id = Nat` so identifier
  equality does not depend on string-literal closed evaluation.
- `Term`, `Ty`, `Ctx`, `Value`, `substTerm`, `Lookup`, and `HasType` all port
  directly with the exact same inference rules and pass `-dcore-lint -dstg-lint`.
- The beta rules use the ordinary `substTerm` in this module. The interface
  audit and `NegBetaMuTarget` check that callers cannot choose another target.
