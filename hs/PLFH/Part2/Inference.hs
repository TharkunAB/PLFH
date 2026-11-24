-- Generated from content/part2/Inference.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, ScopedTypeVariables, TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LINE 14 "content/part2/Inference.md" #-}
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
import qualified HaskLib.Size as S
import PLFH.Part1.Decidable (Not)
import PLFH.Part2.DeBruijn (Ctx (..), Lookup (..), Term (..), Ty (..))

{-# LINE 55 "content/part2/Inference.md" #-}
-- | Untyped abstract syntax tree with runtime de Bruijn indices and binder annotations.
data RawTerm
  = RVar S.Size
  | RLam Ty RawTerm
  | RApp RawTerm RawTerm
  | RZero
  | RSuc RawTerm
  | RCase RawTerm RawTerm RawTerm
  | RMu Ty RawTerm
  deriving (Show)

{-# LINE 73 "content/part2/Inference.md" #-}
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

{-# LINE 93 "content/part2/Inference.md" #-}
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
lookupCtx :: foreach (g :: Ctx) -> S.Size -> Maybe (LookupRes g)
lookupCtx CEmpty     _          = Nothing
lookupCtx (CExt _ a) S.Zero     = Just (Found a Z)
lookupCtx (CExt g _) (S.Succ n) = case lookupCtx g n of
  Nothing          -> Nothing
  Just (Found b p) -> Just (Found b (S p))

{-# LINE 127 "content/part2/Inference.md" #-}
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
rawIdNat = RLam TNat (RVar S.Zero)

rawTwo :: RawTerm
rawTwo = RSuc (RSuc RZero)
