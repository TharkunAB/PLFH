---
title: "Lambda: Introduction to Lambda Calculus"
prev: /Lists/
next: /Properties/
src: content/part2/Lambda.md
module: PLFH.Part2.Lambda
plfaChapter: https://plfa.inf.ed.ac.uk/Lambda/
---

Welcome to Part 2: **Programming Language Foundations**. In Part 1 we built up
logic, equality, relations, and induction in Dependent Haskell. Now we put
those tools to work formalizing programming languages themselves—starting with
Alonzo Church's **simply-typed lambda calculus** (STLC), extended with natural
numbers, case analysis, and general recursion (`μ`).

This chapter follows PLFA's *extrinsic* formulation of STLC: we first define
untyped syntax (`Term`) and its operational semantics (values, substitution,
and call-by-value reduction), and then separately define a typing judgment
(`HasType`) that picks out the well-typed programs. In [Properties](/Properties/)
we prove that every closed, well-typed program satisfies Progress and
Preservation; in [DeBruijn](/DeBruijn/) we revisit the same language using
*intrinsically* typed terms.

## Imports

We import propositional equality `(:~:)`, Peano naturals `Nat` from
`Data.Nat.Dependent` (used here as structural variable identifiers), and `Not` from
[Decidable](/Decidable/) to express variable inequality during context lookup.

```haskell
{-# LANGUAGE DependentTypes, LambdaCase #-}
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
  , TwoChurch
  , twoChurchTyped
  , AddTerm
  , addTyped
  , stepExample
  ) where

import Data.Type.Equality ((:~:) (Refl))
import Data.Nat.Dependent (Nat (..))
import PLFH.Part1.Decidable (Not)
```

## The lambda calculus and Church's notation

In informal mathematical notation (and PLFA), our language has seven term forms,
two type forms, and typing contexts binding variables to types:

```text
Types     A, B   ::=  Nat  |  A -> B
Contexts  Γ      ::=  ∅    |  Γ, x : A
Terms     L,M,N  ::=  x
                  |   λ x ⇒ N
                  |   L · M
                  |   zero
                  |   suc M
                  |   case L [ zero ⇒ M | suc x ⇒ N ]
                  |   μ x ⇒ M
```

Here:
- `x` is a **variable**;
- `λ x ⇒ N` is a **lambda abstraction** (anonymous function with parameter `x`
  and body `N`);
- `L · M` is **function application**;
- `zero` and `suc M` build **natural numbers**;
- `case L [ zero ⇒ M | suc x ⇒ N ]` performs **case analysis** on a natural
  number `L`, evaluating `M` if `L` is `zero` and substituting the predecessor
  for `x` in `N` if `L` is `suc V`;
- `μ x ⇒ M` is a **general fixpoint** (recursive definition), unfolding `x` to
  `μ x ⇒ M` itself inside `M`.

For example, addition of two natural numbers is defined using `μ` and `case`:

```text
plus = μ "+" ⇒ λ m ⇒ λ n ⇒ case m [ zero ⇒ n | suc m' ⇒ suc ("+" · m' · n) ]
```

Because `μ` allows arbitrary recursion, our simply-typed lambda calculus is
Turing-complete—well-typed terms can loop forever (such as `μ x ⇒ x`), yet as
we will prove in [Properties](/Properties/), they can never *get stuck* on a
type error!

## Bound and free variables, and the Barendregt convention

A variable `x` is **bound** in `λ x ⇒ N`, in the `suc x ⇒ N` branch of `case`,
and in `μ x ⇒ M`; any occurrence of a variable outside the scope of a matching
binder is **free**. A term with no free variables is called **closed**.

On paper, we routinely identify terms up to renaming of bound variables
(*α-equivalence*, so `λ x ⇒ x` and `λ y ⇒ y` denote the same function) and
assume bound variables are chosen distinct from free variables (the *Barendregt
convention*). When formalizing in a proof assistant, however, names are concrete
data! In this chapter we restrict substitution `substTerm m y v` to replacing
`y` with a **closed** term `v`, which neatly avoids variable capture without
needing α-renaming. (In [DeBruijn](/DeBruijn/) we eliminate variable names
altogether using de Bruijn indices so that α-equivalent terms are syntactically
identical.)

## Syntax of terms, types, and contexts

PLFA uses `Id = String` for variable names. In PLFH we represent variable
identifiers structurally as Peano naturals `type Id = Nat` (think of `0`, `1`,
`2`, … as variables `x₀`, `x₁`, `x₂`, …) so that identifier equality `eqId` is
an ordinary structural Haskell function on a closed algebraic datatype whose
equations GHC can evaluate at the type level:

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

Notice that `Ctx` grows to the *right* (`CExt g x a` represents `Γ, x : A`),
matching the standard pen-and-paper convention where the most recently bound
variable appears on the right and shadows earlier bindings of the same name.

## Values

In **call-by-value** evaluation, we evaluate function arguments to values before
performing β-reduction, and we do *not* reduce underneath a lambda binder. A
term is therefore a **value** (`Value t`) if and only if it is:

- a lambda abstraction `Lam x n` (`VLam`),
- zero `TZero` (`VZero`), or
- the successor `TSuc v` of a value `v` (`VSuc`).

```haskell
-- | Evidence that a term is a call-by-value value.
data Value (t :: Term) where
  VLam  :: Value (Lam x n)
  VZero :: Value TZero
  VSuc  :: Value v -> Value (TSuc v)
```

With `DataKinds`, the promoted constructors `Lam`, `TZero`, and `TSuc` can be
written directly in the index positions of `Value` without needing a leading
tick because no type constructors share those names.

## Substitution (`_[_:=_]`)

Following PLFA, `substTerm m y v` (written `M [ y := V ]` on paper) substitutes
a **closed** term `v` for every *free* occurrence of variable `y` in `m`.

Each binding construct (`Lam`, `TCase`'s successor branch, and `TMu`) checks
whether its own bound variable `x` equals `y` via `eqId x y`:

- If `eqId x y` is `True`, the inner binder **shadows** `y`, so substitution
  stops and leaves the body untouched.
- If `eqId x y` is `False`, substitution recurses into the body (no capture is
  possible because `v` is closed).

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

Call-by-value **small-step operational semantics** specifies how a term takes a
single deterministic reduction step `Step m n` (written `M —→ N` in PLFA). The
rules fall into two groups:

- **Compatibility (congruence) rules (`ξ`)**: specify *where* the next redex
  lies. In `App l m`, we reduce `l` first (`XiApp1`); only once `l` is a value
  `v` do we reduce `m` (`XiApp2`). Similarly `XiSuc` reduces inside `TSuc`, and
  `XiCase` reduces the scrutinee of `TCase`.
- **Computation (redex) rules (`β`)**: perform actual work once the relevant
  subterms are values:
  - `BetaLam`: applying a lambda `Lam x n` to a value `v` substitutes `v` for
    `x` in `n`;
  - `BetaZero`: `case` on `TZero` selects the zero branch `m`;
  - `BetaSuc`: `case` on `TSuc v` (with `Value v`) substitutes `v` for `x` in
    the successor branch `n`;
  - `BetaMu`: unfolding `TMu x m` substitutes the whole fixpoint `TMu x m` for
    `x` in `m`.

Notice how `BetaLam`, `BetaSuc`, and `BetaMu` call our ordinary Haskell
function `substTerm` directly in their result types!

```haskell
-- | Call-by-value one-step reduction relation (M —→ N).
data Step (m :: Term) (n :: Term) where
  XiApp1   :: Step l l' -> Step (App l m) (App l' m)
  XiApp2   :: Value v -> Step m m' -> Step (App v m) (App v m')
  BetaLam  :: forall v x n. Value v -> Step (App (Lam x n) v) (substTerm n x v)
  XiSuc    :: Step m m' -> Step (TSuc m) (TSuc m')
  XiCase   :: Step l l' -> Step (TCase l m x n) (TCase l' m x n)
  BetaZero :: Step (TCase TZero m x n) m
  BetaSuc  :: forall v m x n. Value v -> Step (TCase (TSuc v) m x n) (substTerm n x v)
  BetaMu   :: forall x m. Step (TMu x m) (substTerm m x (TMu x m))

-- | Reflexive-transitive closure of one-step reduction (M —↠ N).
data Steps (m :: Term) (n :: Term) where
  StepsRefl :: Steps m m
  StepsCons :: Step l m -> Steps m n -> Steps l n
```

The three `β` constructors bind their term indices with explicit `forall` so
that `substTerm` refers strictly to the top-level substitution function rather
than an unconstrained type variable. The negative control `NegBetaMuTarget`
below verifies that GHC enforces the exact computed target of `BetaMu`.

## Context lookup and typing (`_∋_⦂_`, `_⊢_⦂_`)

A typing judgment `HasType g m a` (written `Γ ⊢ M ⦂ A` in PLFA) asserts that
under typing context `g`, term `m` has type `a`.

First we define **context lookup** `Lookup g x a` (`Γ ∋ x ⦂ A`), witnessing
that the *rightmost* binding of variable `x` in context `g` has type `a`:

- `LZ` finds `x : a` immediately at the end of `CExt g x a`;
- `LS` skips past an outer binding `y : b` **only** when given a proof
  `Not (x :~: y)` that `x` and `y` are distinct, enforcing lexical shadowing!

The typing rules follow natural deduction's **introduction (`-I`)** and
**elimination (`-E`)** pattern for each type constructor:

- Functions (`TArr a b`): introduced by `TLam` (`→-I`), eliminated by `TApp`
  (`→-E`).
- Naturals (`TNat`): introduced by `TZeroT` and `TSucT` (`ℕ-I`), eliminated by
  `TCaseT` (`ℕ-E`).
- Variables and recursion: `TVar` reads a type from `Lookup`, and `TMuT` types
  `TMu x m` at `a` whenever `m` has type `a` under the assumption `x : a`.

```haskell
-- | Evidence that variable `x` has type `a` in context `g` (Γ ∋ x ⦂ A).
data Lookup (g :: Ctx) (x :: Id) (a :: Ty) where
  LZ :: Lookup (CExt g x a) x a
  LS :: Not (x :~: y) -> Lookup g x a -> Lookup (CExt g y b) x a

-- | Extrinsic typing derivation (Γ ⊢ M ⦂ A).
data HasType (g :: Ctx) (m :: Term) (a :: Ty) where
  TVar   :: Lookup g x a -> HasType g (Var x) a
  TLam   :: HasType (CExt g x a) n b -> HasType g (Lam x n) (TArr a b)
  TApp   :: HasType g l (TArr a b) -> HasType g m a -> HasType g (App l m) b
  TZeroT :: HasType g TZero TNat
  TSucT  :: HasType g m TNat -> HasType g (TSuc m) TNat
  TCaseT :: HasType g l TNat -> HasType g m a -> HasType (CExt g x TNat) n a
         -> HasType g (TCase l m x n) a
  TMuT   :: HasType (CExt g x a) m a -> HasType g (TMu x m) a
```

### Examples: `2`, Church numeral `2c`, recursive addition (`+`), and a concrete β-reduction

Alongside the numeral `2`, we also check PLFA's flagship STLC examples:
the **Church numeral `2c`** (`λ s ⇒ λ z ⇒ s · (s · z)`), **recursive addition**
via `TMu` (`μ "+" ⇒ λ m ⇒ λ n ⇒ case m [ zero ⇒ n | suc m' ⇒ suc ("+" · m' · n) ]`),
and a concrete multi-step reduction exercising `BetaLam` and `substTerm`:

```haskell
-- | The term representing natural number 2.
termTwo :: Term
termTwo = TSuc (TSuc TZero)

-- | Typing derivation showing ∅ ⊢ suc (suc zero) : Nat.
twoTyped :: HasType CEmpty (TSuc (TSuc TZero)) TNat
twoTyped = TSucT (TSucT TZeroT)

-- | Church numeral 2c = λ 0 ⇒ λ 1 ⇒ 0 · (0 · 1) (`→-example`).
type TwoChurch = Lam 0 (Lam 1 (App (Var 0) (App (Var 0) (Var 1))))

-- | Typing derivation for Church numeral 2c at (Nat -> Nat) -> (Nat -> Nat).
twoChurchTyped :: HasType CEmpty TwoChurch (TArr (TArr TNat TNat) (TArr TNat TNat))
twoChurchTyped =
  TLam (TLam (TApp (TVar (LS (\case {}) LZ))
                   (TApp (TVar (LS (\case {}) LZ)) (TVar LZ))))

-- | Recursive addition in STLC via `TMu`:
--   μ 0 ⇒ λ 1 ⇒ λ 2 ⇒ case 1 [ zero ⇒ 2 | suc 3 ⇒ suc ((0 · 3) · 2) ].
type AddTerm =
  TMu 0 (Lam 1 (Lam 2
    (TCase (Var 1) (Var 2) 3
      (TSuc (App (App (Var 0) (Var 3)) (Var 2))))))

-- | Typing derivation showing ∅ ⊢ AddTerm : Nat -> Nat -> Nat.
addTyped :: HasType CEmpty AddTerm (TArr TNat (TArr TNat TNat))
addTyped =
  TMuT (TLam (TLam
    (TCaseT
      (TVar (LS (\case {}) LZ))
      (TVar LZ)
      (TSucT (TApp (TApp (TVar (LS (\case {}) (LS (\case {}) (LS (\case {}) LZ))))
                         (TVar LZ))
                   (TVar (LS (\case {}) LZ)))))))

-- | Concrete β-reduction (`Step-example`): (λ 0 ⇒ suc 0) · (suc zero) —↠ suc (suc zero).
stepExample :: Steps (App (Lam 0 (TSuc (Var 0))) (TSuc TZero)) (TSuc (TSuc TZero))
stepExample = StepsCons (BetaLam (VSuc VZero)) StepsRefl
```

### Negative control: ill-typed application is rejected

Trying to apply `TZero` (which has type `TNat`) as a function fails to unify
`TNat` with `TArr a b`, so GHC rejects it with `GHC-83865`:

```{.haskell .fail name="NegIllTypedApp" expect="GHC-83865"}
{-# LANGUAGE DependentTypes #-}
module NegIllTypedApp (badApp) where

import PLFH.Part2.Lambda (Ctx (..), HasType (..), Term (..), Ty (..))

badApp :: HasType CEmpty (App TZero TZero) TNat
badApp = TApp TZeroT TZeroT
```

### Negative control: a beta step must compute its target

The term `TMu Zero TZero` unfolds via `substTerm TZero Zero (TMu Zero TZero)`
to `TZero`. Attempting to give `BetaMu` a different target term is rejected by
GHC with `GHC-83865`:

```{.haskell .fail name="NegBetaMuTarget" expect="GHC-83865"}
{-# LANGUAGE DependentTypes #-}
module NegBetaMuTarget (wrong) where

import Data.Nat.Dependent (Nat (Zero))
import PLFH.Part2.Lambda (Step (..), Term (..))

wrong :: Step (TMu Zero TZero)
              (TCase TZero TZero Zero (TMu Zero TZero))
wrong = BetaMu
```

## Exercises

#### Exercise `mul` (recommended)

Write out a closed STLC `Term` defining multiplication of two natural numbers
using `TMu`, `Lam`, `TCase`, and addition, and construct its `HasType CEmpty`
derivation of type `TArr TNat (TArr TNat TNat)`.

#### Exercise `→-example` (practice)

Construct a closed `HasType` derivation for the Church numeral `2c = λ s ⇒ λ z ⇒ s · (s · z)` at type `TArr (TArr TNat TNat) (TArr TNat TNat)` using
`TLam`, `TApp`, `TVar`, `LZ`, and `LS`.

#### Exercise `Step-example` (practice)

Construct a concrete `Steps` derivation reducing `App (Lam Zero (TSuc (Var Zero))) (TSuc TZero)` to `TSuc (TSuc TZero)` using `StepsCons`, `BetaLam`, `VSuc`, `VZero`, and `StepsRefl`.

## Changes from PLFA

- Adapted from [Lambda](https://plfa.inf.ed.ac.uk/Lambda/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/Lambda.lagda.md)),
  licensed under CC BY 4.0.
- Replaced `Id = String` with structural `type Id = Nat` so identifier
  equality `eqId` is an ordinary closed-datatype structural function with
  checked type-level equations.
- `Term`, `Ty`, `Ctx`, `Value`, `substTerm`, `Step`, `Steps`, `Lookup`, and
  `HasType` all port directly with the exact same inference rules and pass
  `-dcore-lint -dstg-lint`.
- The three beta rules (`BetaLam`, `BetaSuc`, `BetaMu`) invoke the ordinary
  `substTerm` function directly; `NegIllTypedApp` and `NegBetaMuTarget` verify
  that ill-typed terms and forged beta targets are rejected.
