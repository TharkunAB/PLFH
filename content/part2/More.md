---
title: "More: Additional constructs of simply-typed lambda calculus"
prev: /Untyped/
next: /Bisimulation/
src: content/part2/More.md
module: PLFH.Part2.More
plfaChapter: https://plfa.inf.ed.ac.uk/More/
---

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
module PLFH.Part2.More
  ( Ty (..)
  , Ctx (..)
  , Lookup (..)
  , Term (..)
  , ext
  , rename
  , exts
  , subst
  , substSingle
  , substDouble
  , Value (..)
  , swapPair
  , mapMaybeNat
  ) where

import Data.Kind (Type)
```

Following PLFA's **More** chapter, we extend our intrinsically-typed de Bruijn
simply-typed lambda calculus with a full suite of everyday functional
programming constructs:

- **`let` bindings** (`Let`),
- **Unit (`TUnit`, `TT`)** and **Products (`TProd`, `Pair`, `Fst`, `Snd`)**,
- **Void (`TVoid`, `Absurd`)** and **Sums (`TSum`, `Inl`, `Inr`, `CaseSum`)**,
- **Lists (`TList`, `Nil`, `Cons`, `CaseLst`)**.

All extended types, contexts, intrinsically-typed terms, simultaneous renaming
and single/double substitution, promoted `Value`, and example programs compile
cleanly with `-dcore-lint -dstg-lint`!

## Extended types, contexts, and intrinsically-typed terms

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
  Z :: Lookup ('CExt g a) a
  S :: Lookup g a -> Lookup ('CExt g b) a

-- | Intrinsically typed terms for the extended simply-typed lambda calculus.
data Term (g :: Ctx) (a :: Ty) where
  Var     :: Lookup g a -> Term g a
  Lam     :: Term ('CExt g a) b -> Term g ('TArr a b)
  App     :: Term g ('TArr a b) -> Term g a -> Term g b
  Zero    :: Term g 'TNat
  Suc     :: Term g 'TNat -> Term g 'TNat
  CaseNat :: Term g 'TNat -> Term g a -> Term ('CExt g 'TNat) a -> Term g a
  Mu      :: Term ('CExt g a) a -> Term g a
  Let     :: Term g a -> Term ('CExt g a) b -> Term g b
  TT      :: Term g 'TUnit
  Pair    :: Term g a -> Term g b -> Term g ('TProd a b)
  Fst     :: Term g ('TProd a b) -> Term g a
  Snd     :: Term g ('TProd a b) -> Term g b
  Inl     :: Term g a -> Term g ('TSum a b)
  Inr     :: Term g b -> Term g ('TSum a b)
  CaseSum :: Term g ('TSum a b) -> Term ('CExt g a) c -> Term ('CExt g b) c -> Term g c
  Absurd  :: Term g 'TVoid -> Term g a
  Nil     :: Term g ('TList a)
  Cons    :: Term g a -> Term g ('TList a) -> Term g ('TList a)
  CaseLst :: Term g ('TList a) -> Term g b -> Term ('CExt ('CExt g a) ('TList a)) b -> Term g b
```

## Renaming and capture-avoiding substitution

Notice `CaseLst`, whose `Cons` branch binds *two* variables (head and tail)
and therefore lifts renamings and substitutions twice (`ext (ext r)`, `exts (exts s)`):

```haskell
ext :: (forall a. Lookup g a -> Lookup d a)
    -> (forall a. Lookup ('CExt g b) a -> Lookup ('CExt d b) a)
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

exts :: (forall a. Lookup g a -> Term d a)
     -> (forall a. Lookup ('CExt g b) a -> Term ('CExt d b) a)
exts _ Z     = Var Z
exts s (S x) = rename S (s x)

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

substSingle :: Term ('CExt g a) b -> Term g a -> Term g b
substSingle n w = subst (\case { Z -> w; S x -> Var x }) n

substDouble :: Term ('CExt ('CExt g a) b) c -> Term g a -> Term g b -> Term g c
substDouble n v w = subst (\case { Z -> w; S Z -> v; S (S x) -> Var x }) n
```

## Values and example terms

```haskell
-- | Values indexed over promoted extended `Term g a`.
type Value :: forall (g :: Ctx) (a :: Ty). Term g a -> Type
data Value m where
  VLam  :: Value ('Lam n)
  VZero :: Value 'Zero
  VSuc  :: Value v -> Value ('Suc v)
  VTT   :: Value 'TT
  VPair :: Value v -> Value w -> Value ('Pair v w)
  VInl  :: Value v -> Value ('Inl v)
  VInr  :: Value v -> Value ('Inr v)
  VNil  :: Value 'Nil
  VCons :: Value v -> Value vs -> Value ('Cons v vs)

-- | Example: swap the components of a pair: λp. (snd p, fst p).
swapPair :: Term g ('TArr ('TProd a b) ('TProd b a))
swapPair = Lam (Pair (Snd (Var Z)) (Fst (Var Z)))

-- | Example: unwrap a `Sum Unit Nat` (Maybe Nat) defaulting to Zero.
mapMaybeNat :: Term g ('TArr ('TSum 'TUnit 'TNat) 'TNat)
mapMaybeNat = Lam (CaseSum (Var Z) Zero (Var Z))
```

## Extended call-by-value reduction (`Step`)

<div class="wip-notice">
<strong>[WIP NOTICE — Functional <code>Step</code> blocked on GADT-indexed <code>substSingle</code> / <code>substDouble</code> (R13/R16)]</strong>
As in <a href="/DeBruijn/">DeBruijn</a>, writing unqualified <code>substSingle</code>
and <code>substDouble</code> in the <code>BetaLam</code>, <code>BetaLet</code>,
<code>BetaInl</code>, <code>BetaInr</code>, and <code>BetaCons</code> constructors
of <code>Step</code> silently quantified fresh unconstrained type variables, while
qualifying them from a split syntax module currently fails with
<code>GHC-70565</code>. Functional <code>Step</code> and
intrinsically-typed <code>progress</code> remain tracked as
<code>[WIP NOTICE]</code> (see
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_SubstSingleUOpenEq.hs"><code>R13_SubstSingleUOpenEq.hs</code></a>
and
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R03_ForEachGadtEquations.hs"><code>R03_ForEachGadtEquations.hs</code></a>).
</div>

## Changes from PLFA

- Adapted from [More](https://plfa.inf.ed.ac.uk/More/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/More.lagda.md)).
- All extended constructs (`Let`, `TUnit`, `TProd`, `TSum`, `TVoid`, `TList`),
  renaming, substitution (`substSingle`, `substDouble`), and GADT-promoted
  `Value` compile cleanly with `-dcore-lint -dstg-lint`.
- Functional `Step` (`Syntax.substSingle` / `Syntax.substDouble`) and
  intrinsically-typed `progress` are marked `[WIP NOTICE]` rather than leaving
  unconstrained fresh-tyvar beta constructors.
