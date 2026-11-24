---
title: "Inference: Type Inference for Intrinsically-Typed Terms"
prev: /DeBruijn/
next: /Untyped/
src: content/part2/Inference.md
module: PLFH.Part2.Inference
plfaChapter: https://plfa.inf.ed.ac.uk/22.08/Inference/
---

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, ScopedTypeVariables, TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module PLFH.Part2.Inference
  ( RawTerm (..)
  , decEqTy
  , Typed (..)
  , LookupRes (..)
  , ArrTerm (..)
  , matchArr
  , matchNat
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

In [DeBruijn](/DeBruijn/) we defined intrinsically typed terms `Term g a`,
whose well-typedness is enforced statically by GHC. But in a real compiler,
programs arrive as *untyped* raw syntax trees parsed from text!

Following PLFA's **Inference** chapter, we write a **certified type
inference and typechecking algorithm** that takes a raw, untyped term
`RawTerm` and a runtime context `g :: Ctx`, and—if typechecking succeeds—
returns a **dependent pair** (`Typed g`) pairing the inferred runtime type
`a :: Ty` with an intrinsically-typed derivation `Term g a`!

Every single piece of this chapter compiles natively with `-dcore-lint -dstg-lint`
with **no singletons and no type families**!

## Raw untyped syntax (`RawTerm`)

Lambda abstractions and `μ`-recursions carry type annotations for their bound
variables (bidirectional/Church-style syntax), while variable occurrences are
plain runtime de Bruijn numbers (`N.Nat`):

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

## Decidable type equality (`decEqTy`)

To check that a function's argument type matches its parameter type, we need
decidable propositional equality on `Ty`:

```haskell
-- | Decidable equality on simple types `Ty`.
decEqTy :: foreach (a :: Ty) -> foreach (b :: Ty) -> Either (Not (a :~: b)) (a :~: b)
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

A successful inference returns a runtime type `a :: Ty` paired with an
intrinsically typed `Term g a` (a `foreach`-carrying GADT constructor):

```haskell
-- | An inferred runtime type paired with its intrinsically typed term.
data Typed (g :: Ctx) where
  MkTyped :: foreach (a :: Ty) -> Term g a -> Typed g

-- | A successful context lookup: runtime type `a` and proof `Lookup g a`.
data LookupRes (g :: Ctx) where
  Found :: foreach (a :: Ty) -> Lookup g a -> LookupRes g

-- | A term proven to have a function type `TArr a b`, exposing both runtime types.
data ArrTerm (g :: Ctx) where
  MkArrTerm :: foreach (a :: Ty) -> foreach (b :: Ty) -> Term g ('TArr a b) -> ArrTerm g

-- | Refine a typed term to an arrow type by matching its retained type index.
matchArr :: forall (g :: Ctx). foreach (t :: Ty) -> Term g t -> Maybe (ArrTerm g)
matchArr TNat       _ = Nothing
matchArr (TArr a b) t = Just (MkArrTerm a b t)

-- | Refine a typed term to `TNat` by matching its retained type index.
matchNat :: forall (g :: Ctx). foreach (t :: Ty) -> Term g t -> Maybe (Term g 'TNat)
matchNat TNat       t = Just t
matchNat (TArr _ _) _ = Nothing

-- | Look up a runtime de Bruijn number in a runtime typing context `g`.
lookupCtx :: foreach (g :: Ctx) -> N.Nat -> Maybe (LookupRes g)
lookupCtx CEmpty     _          = Nothing
lookupCtx (CExt _ a) N.Zero     = Just (Found a Z)
lookupCtx (CExt g _) (N.Succ n) = case lookupCtx g n of
  Nothing          -> Nothing
  Just (Found b p) -> Just (Found b (S p))
```

## Certified Type Inference (`infer`) and Checking (`check`)

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
    Just (MkTyped lTy l') -> case matchArr @g lTy l' of
      Nothing -> Nothing
      Just (MkArrTerm a b lArr) -> case infer g m of
        Nothing -> Nothing
        Just (MkTyped a' m') -> case decEqTy a a' of
          Right Refl -> Just (MkTyped b (App @g @a @b lArr m'))
          Left _     -> Nothing
  RZero -> Just (MkTyped TNat Zero)
  RSuc m -> case infer g m of
    Nothing -> Nothing
    Just (MkTyped mTy m') -> case matchNat @g mTy m' of
      Nothing   -> Nothing
      Just mNat -> Just (MkTyped TNat (Suc mNat))
  RCase l m n -> case infer g l of
    Nothing -> Nothing
    Just (MkTyped lTy l') -> case matchNat @g lTy l' of
      Nothing   -> Nothing
      Just lNat -> case infer g m of
        Nothing -> Nothing
        Just (MkTyped a m') -> case infer (CExt g TNat) n of
          Nothing -> Nothing
          Just (MkTyped a' n') -> case decEqTy a a' of
            Right Refl -> Just (MkTyped a (Case lNat m' n'))
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

<div class="wip-notice">
<strong>[WIP NOTICE — Two R03 ergonomics findings surfaced by <code>infer</code>]</strong>
Although the entire certified type inference and checking engine above compiles
cleanly with <code>-dcore-lint -dstg-lint</code>, writing it uncovered two
clean R03 ergonomic boundaries on GHC <code>d15cbd41fe</code>:
<ol>
  <li><strong>Inline <code>case lTy of</code> on a GADT indexed by a retained <code>g</code>:</strong>
      Matching <code>case lTy of { TNat -&gt; ...; TArr a b -&gt; ... }</code>
      directly with <code>l' :: Term g lTy</code> in scope (when <code>g :: Ctx</code>
      is itself <code>foreach</code>-retained) fails with
      <code>GHC-83605</code> (<em>Retained constructor refinement does not
      support this type yet: <code>Term g lTy</code></em>), requiring the
      top-level helpers <code>matchArr</code> and <code>matchNat</code>. See
      <a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R03_CaseRefinementMultiIndexGadt.hs"><code>R03_CaseRefinementMultiIndexGadt.hs</code></a>.</li>
  <li><strong>Untouchable existential argument inside retained applications under <code>Refl</code>:</strong>
      Writing <code>MkTyped b (App lArr m')</code> inside a GADT equality match
      (<code>Right Refl</code>) under <code>foreach (g :: Ctx)</code> without explicit
      type applications <code>App @g @a @b</code> fails with <code>GHC-83865</code>
      (<code>g0</code>/<code>a0</code> untouchable inside <code>bound by a
      retained application</code>). See
      <a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R03_UntouchableUnderRetainedApp.hs"><code>R03_UntouchableUnderRetainedApp.hs</code></a>.</li>
</ol>
</div>

## Changes from PLFA `v22.08`

- Adapted from [Inference (v22.08)](https://plfa.inf.ed.ac.uk/22.08/Inference/)
  ([source](https://github.com/plfa/plfa.github.io/blob/e2d545f3df0db4d4206c5448735665abde02d81f/src/plfa/part2/Inference.lagda.md)).
- Implements full certified type inference (`infer`) and type checking (`check`)
  for Church-annotated de Bruijn STLC terms (variables, lambdas, applications,
  `Zero`, `Suc`, `Case`, `Mu`), returning intrinsically-typed `Term g a` values
  from [DeBruijn](/DeBruijn/).
- Uses `Maybe` in place of PLFA's `Result`/`Error` sum for conciseness; all
  dependent type refinement, decidable `Ty` equality, and runtime `Ctx` lookup
  are checked directly by GHC with `-dcore-lint -dstg-lint`.
