-- Generated from content/part2/More.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
{-# OPTIONS_GHC -fwrite-source-equations #-}
{-# LINE 37 "content/part2/More.md" #-}
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
  , TBool
  , tTrue
  , tFalse
  , ifThenElse
  , swapSum
  , appendList
  ) where

import Data.Kind (Type)

{-# LINE 83 "content/part2/More.md" #-}
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

{-# LINE 137 "content/part2/More.md" #-}
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

exts :: (forall a. Lookup g a -> Term d a)
     -> (forall a. Lookup (CExt g b) a -> Term (CExt d b) a)
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

substSingle :: Term (CExt g a) b -> Term g a -> Term g b
substSingle n w = subst (\case { Z -> w; S x -> Var x }) n

substDouble :: Term (CExt (CExt g a) b) c -> Term g a -> Term g b -> Term g c
substDouble n v w = subst (\case { Z -> w; S Z -> v; S (S x) -> Var x }) n

{-# LINE 204 "content/part2/More.md" #-}
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
