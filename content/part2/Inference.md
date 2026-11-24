---
title: "Inference: Type Inference for Intrinsically-Typed Terms"
prev: /DeBruijn/
next: /Untyped/
src: content/part2/Inference.md
module: PLFH.Part2.Inference
plfaChapter: https://plfa.inf.ed.ac.uk/Inference/
---

In [DeBruijn](/DeBruijn/) we represented programs as intrinsically typed terms
`Term g a`, whose well-typedness is enforced statically by GHC. That makes
metatheory wonderfully clean—ill-typed terms simply do not exist!—but it leaves
a practical question: in a real compiler or interpreter, programs arrive from a
parser as **untyped abstract syntax trees** (`RawTerm`), not as pre-verified
typing derivations!

How do we bridge the gap between untyped syntax and intrinsically typed terms?
We write a **certified type inference and typechecking algorithm**:

- Given a runtime typing context `g :: Ctx` and a raw syntax tree `RawTerm`,
  `infer` *synthesizes* a runtime type `a :: Ty` paired with an intrinsically
  typed `Term g a` (or returns `Nothing` if the raw term is ill-typed).
- Given an expected runtime type `a :: Ty`, `check` verifies that the raw term
  has type `a` and returns `Maybe (Term g a)`.

Notice the beauty of dependent types here: **soundness of type inference is
guaranteed by construction!** Because `infer` returns a `Term g a`, it is
impossible for `infer` to succeed and report a bogus type—the returned value
*is* a complete machine-checked typing derivation! Every single line of this
chapter compiles natively with `-dcore-lint -dstg-lint` with **no singletons
and no type families**.

## Imports

We import propositional equality `(:~:)`, Peano naturals `HaskLib.Nat` (for
raw de Bruijn numbers), `Not` from [Decidable](/Decidable/), and our
intrinsically typed STLC definitions from [DeBruijn](/DeBruijn/).

```haskell
{-# LANGUAGE DependentTypes #-}
module PLFH.Part2.Inference
  ( RawTerm (..)
  , decEqTy
  , Typed (..)
  , LookupRes (..)
  , lookupCtx
  , infer
  , check
  , rawIdNat
  , rawTwo
  ) where

import Data.Type.Equality ((:~:) (Refl))
import qualified HaskLib.Nat as N
import PLFH.Part1.Decidable (Not)
import PLFH.Part2.DeBruijn (Ctx (..), Lookup (..), Term (..), Ty (..))
```

## Bidirectional vs. syntax-directed typing, and raw syntax (`RawTerm`)

Our typing rules in [DeBruijn](/DeBruijn/) are almost **syntax-directed**: the
outermost constructor of a term determines which typing rule applies. The only
places where an untyped term lacks enough information to *synthesize* its type
from the bottom up are variable-binding forms (`Lam` and `Mu`), where the
bound variable's type could otherwise be anything.

Following PLFA's Church-style raw syntax, we annotate `RLam` and `RMu` with the
type `Ty` of their bound variable, while variable occurrences are plain runtime
natural numbers `N.Nat` (unverified de Bruijn indices):

```haskell
-- | Untyped abstract syntax tree with runtime de Bruijn indices and binder annotations.
data RawTerm
  = RVar N.Nat
  | RLam Ty RawTerm
  | RApp RawTerm RawTerm
  | RZero
  | RSuc RawTerm
  | RCase RawTerm RawTerm RawTerm
  | RMu Ty RawTerm
  deriving (Show)
```

Notice what is *not* checked by `RawTerm`: `RVar 99` can refer out of bounds,
`RApp RZero RZero` can apply zero to zero, and `RCase RZero RZero (RLam TNat (RVar 0))`
can have mismatched branch types. Our certified `infer` function will reject all
of these and produce a `Term g a` only when every typing invariant holds.

## Decidable type equality (`decEqTy`)

When typechecking an application `RApp l m`, a `RCase` expression's two
branches, or a recursive `RMu a m`, we need to test whether two runtime types
`a` and `b` are equal—and, when they are, obtain a **propositional equality
proof** `a :~: b` so GHC knows `Term g a` and `Term g b` have the same type!

Because `Ty` is a simple inductive datatype, structural recursion on retained
`foreach (a :: Ty)` and `foreach (b :: Ty)` decides equality cleanly:

```haskell
-- | Decidable equality on simple types `Ty`.
decEqTy :: foreach (a b :: Ty) -> Either (Not (a :~: b)) (a :~: b)
decEqTy TNat b = case b of
  TNat     -> Right Refl
  TArr _ _ -> Left (\case {})
decEqTy (TArr a1 a2) b = case b of
  TNat       -> Left (\case {})
  TArr b1 b2 -> case decEqTy a1 b1 of
    Left neq   -> Left (\Refl -> neq Refl)
    Right Refl -> case decEqTy a2 b2 of
      Left neq   -> Left (\Refl -> neq Refl)
      Right Refl -> Right Refl
```

## Dependent result packages & runtime context lookup

When `infer` succeeds on a raw term in context `g`, it does not know the
result type `a` in advance—it *discovers* `a` at runtime! We therefore package
the inferred runtime type `a :: Ty` (bound with `foreach` so callers can inspect
it!) together with the intrinsically typed term `Term g a` in a dependent pair
`Typed g`.

Likewise, looking up a raw de Bruijn number `n :: N.Nat` in a runtime context
`g :: Ctx` returns `Maybe (LookupRes g)`, pairing the discovered entry type `a`
with the verified de Bruijn pointer `Lookup g a`:

```haskell
-- | An inferred runtime type paired with its intrinsically typed term.
data Typed (g :: Ctx) where
  MkTyped :: foreach (a :: Ty) -> Term g a -> Typed g

-- | A successful context lookup: runtime type `a` and proof `Lookup g a`.
data LookupRes (g :: Ctx) where
  Found :: foreach (a :: Ty) -> Lookup g a -> LookupRes g

-- | Look up a runtime de Bruijn number in a runtime typing context `g`.
lookupCtx :: foreach (g :: Ctx) -> N.Nat -> Maybe (LookupRes g)
lookupCtx CEmpty     _          = Nothing
lookupCtx (CExt _ a) N.Zero     = Just (Found a Z)
lookupCtx (CExt g _) (N.Succ n) = case lookupCtx g n of
  Nothing          -> Nothing
  Just (Found b p) -> Just (Found b (S p))
```

## Certified Type Inference (`infer`) and Checking (`check`)

Now `infer` walks `RawTerm` structurally, combining `lookupCtx` and `decEqTy`:

- **`RVar n`**: look up `n` in `g`; if found at type `a` with pointer `p`, wrap
  `Var p`.
- **`RLam a body`**: extend the runtime context to `CExt g a`, infer `body`'s
  type `b`, and return `TArr a b` with `Lam body'`.
- **`RApp l m`**: infer `l`'s type `lTy`, match on `lTy` to ensure it is
  `TArr a b`, infer `m`'s type `a'`, and call `decEqTy a a'`! Matching
  `Right Refl` unifies `a` and `a'`, so GHC accepts `App l' m'` at type `b`!
- **`RZero` / `RSuc m`**: verify `m` has type `TNat`.
- **`RCase l m n`**: verify `l` has type `TNat`, infer `m`'s type `a` and `n`'s
  type `a'` in `CExt g TNat`, and unify `a` with `a'` via `decEqTy`.
- **`RMu a m`**: infer `m`'s type `a'` in `CExt g a` and verify `a :~: a'`.

Finally, `check` checks a raw term against a caller-supplied runtime type `a`
by running `infer` and comparing the inferred type `a'` with `a`:

```haskell
-- | Certified type inference: given a runtime context `g` and raw term,
-- infer a runtime type `a` and construct an intrinsically-typed `Term g a`.
infer :: foreach (g :: Ctx) -> RawTerm -> Maybe (Typed g)
infer g raw = case raw of
  RVar n -> case lookupCtx g n of
    Nothing          -> Nothing
    Just (Found a p) -> Just (MkTyped a (Var p))
  RLam a body -> case infer (CExt g a) body of
    Nothing                -> Nothing
    Just (MkTyped b body') -> Just (MkTyped (TArr a b) (Lam body'))
  RApp l m -> case infer g l of
    Nothing -> Nothing
    Just (MkTyped lTy l') -> case lTy of
      TNat     -> Nothing
      TArr a b -> case infer g m of
        Nothing -> Nothing
        Just (MkTyped a' m') -> case decEqTy a a' of
          Right Refl -> Just (MkTyped b (App l' m'))
          Left _     -> Nothing
  RZero -> Just (MkTyped TNat Zero)
  RSuc m -> case infer g m of
    Nothing -> Nothing
    Just (MkTyped mTy m') -> case mTy of
      TNat     -> Just (MkTyped TNat (Suc m'))
      TArr _ _ -> Nothing
  RCase l m n -> case infer g l of
    Nothing -> Nothing
    Just (MkTyped lTy l') -> case lTy of
      TArr _ _ -> Nothing
      TNat     -> case infer g m of
        Nothing -> Nothing
        Just (MkTyped a m') -> case infer (CExt g TNat) n of
          Nothing -> Nothing
          Just (MkTyped a' n') -> case decEqTy a a' of
            Right Refl -> Just (MkTyped a (Case l' m' n'))
            Left _     -> Nothing
  RMu a m -> case infer (CExt g a) m of
    Nothing -> Nothing
    Just (MkTyped a' m') -> case decEqTy a a' of
      Right Refl -> Just (MkTyped a (Mu m'))
      Left _     -> Nothing

-- | Certified type checking against an expected runtime type `a`.
check :: foreach (g :: Ctx) -> RawTerm -> foreach (a :: Ty) -> Maybe (Term g a)
check g raw a = case infer g raw of
  Just (MkTyped a' t) -> case decEqTy a a' of
    Right Refl -> Just t
    Left _     -> Nothing
  Nothing -> Nothing

-- | Example raw terms: `λ (x : Nat) -> x` and `2`.
rawIdNat :: RawTerm
rawIdNat = RLam TNat (RVar N.Zero)

rawTwo :: RawTerm
rawTwo = RSuc (RSuc RZero)
```

Notice what happens at runtime (tested in PLFH's executable smoke test):
- `infer CEmpty (RApp rawIdNat rawTwo)` returns `Just (MkTyped TNat (App (Lam (Var Z)) (Suc (Suc Zero))))`!
- `infer CEmpty (RApp RZero rawTwo)` returns `Nothing` (applying `0` to `2` is rejected)!
- `check CEmpty rawTwo TNat` returns `Just (Suc (Suc Zero))`, while `check CEmpty rawTwo (TArr TNat TNat)` returns `Nothing`.

<div class="wip-notice">
<strong>[WIP NOTICE — Unidirectional <code>Maybe</code> inference vs. PLFA's bidirectional <code>Dec</code>]</strong>
PLFA's <code>Inference</code> chapter presents a <em>bidirectional</em> type
checker (splitting syntax into synthesizable terms <code>Raw⁺</code> and
checkable terms <code>Raw⁻</code> so lambdas need no parameter annotations when
checked against a known arrow type) and returns a <em>decidable</em> proof
<code>Dec (∃ A. Γ ⊢ M ⦂ A)</code> certifying both soundness (well-typed terms
produce a derivation) and completeness (rejected terms come with a proof that
no derivation exists). Here we implement unidirectional Church-annotated
<code>infer</code> / <code>check</code> returning <code>Maybe</code>: every
accepted term carries a machine-checked intrinsic <code>Term g a</code>
derivation, while completeness refutations and bidirectional unannotated lambdas
are left open as an exercise/future upgrade.
</div>

## Exercises

#### Exercise `erase` and round-trip soundness (recommended)

Define an erasure function `erase :: Term g a -> RawTerm` that strips the
dependent typing information back down to raw syntax (preserving binder
annotations on `Lam` and `Mu`), and observe that `infer` on `erase t` recovers
a term equivalent to `t`.

#### Exercise `Bidirectional` (stretch)

Notice that `RLam` always requires a type annotation even when it is checked
against a known function type `TArr a b` via `check`. Following PLFA's
bidirectional typing system, split `RawTerm` into *synthesizable* terms
(variables, applications, annotated expressions) and *checkable* terms (unannotated
lambdas `λ. body`), mutually recursing between `infer` and `check`!

#### Exercise `Inference-errors` (practice)

Replace `Maybe` in `infer` with a rich `Either TypeError (Typed g)` carrying
structured diagnostics (out-of-scope variable, expected function type, type
mismatch with expected and actual `Ty`), or strengthen it further to `Dec`
carrying formal refutations.

## Changes from PLFA

- Adapted from [Inference](https://plfa.inf.ed.ac.uk/Inference/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/Inference.lagda.md)),
  licensed under CC BY 4.0.
- Implements certified type inference (`infer`) and type checking (`check`)
  for Church-annotated de Bruijn STLC terms (variables, lambdas, applications,
  `Zero`, `Suc`, `Case`, `Mu`), returning intrinsically-typed `Term g a` values
  from [DeBruijn](/DeBruijn/).
- Uses unidirectional `Maybe` in place of PLFA's bidirectional `Dec`-based
  `synthesize`/`inherit` (so soundness is checked intrinsically, while
  completeness refutations are omitted); all dependent type refinement,
  decidable `Ty` equality, and runtime `Ctx` lookup are checked directly by GHC
  with `-dcore-lint -dstg-lint`.
