-- Generated from content/part2/Inference.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, ScopedTypeVariables, TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LINE 43 "content/part2/Inference.md" #-}
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

{-# LINE 74 "content/part2/Inference.md" #-}
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

{-# LINE 102 "content/part2/Inference.md" #-}
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

{-# LINE 129 "content/part2/Inference.md" #-}
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

{-# LINE 166 "content/part2/Inference.md" #-}
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
