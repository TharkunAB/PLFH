-- Generated from content/part1/Lists.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, TypeOperators #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}
{-# LINE 14 "content/part1/Lists.md" #-}
module PLFH.Part1.Lists
  ( appendAssoc
  , appendNilR
  , lengthAppendLaw
  , lengthMapLaw
  , lengthReverseLaw
  , mapAppend
  , mapCompose
  , mapId
  , All (..)
  , Any (..)
  , In
  , allAppend
  , allMap
  , zeroInList
  , threeNotInList
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl), gcastWith)
import Data.Void (Void)
import HaskLib (lengthAppend, lengthMap, lengthReverse, size, withEquality)
import HaskLib.Size (Size (..), plus)
import PLFH.Part1.Decidable (Not)

{-# LINE 54 "content/part1/Lists.md" #-}
-- | Associativity of Prelude list append: (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
appendAssoc :: forall a. foreach (xs :: [a]) -> foreach (ys :: [a]) -> foreach (zs :: [a])
            -> ((xs ++ ys) ++ zs) :~: (xs ++ (ys ++ zs))
appendAssoc []       _  _  = Refl
appendAssoc (_ : xs) ys zs = withEquality (appendAssoc xs ys zs) Refl

-- | Right identity of Prelude list append: xs ++ [] = xs.
appendNilR :: forall a. foreach (xs :: [a]) -> (xs ++ '[]) :~: xs
appendNilR []       = Refl
appendNilR (_ : xs) = withEquality (appendNilR xs) Refl

{-# LINE 73 "content/part1/Lists.md" #-}
-- | Length of append (reused from HaskLib.lengthAppend).
lengthAppendLaw :: forall a. foreach (xs :: [a]) -> foreach (ys :: [a])
                -> size (xs ++ ys) :~: plus (size xs) (size ys)
lengthAppendLaw xs ys = lengthAppend xs ys

-- | Length of map (reused from HaskLib.lengthMap).
lengthMapLaw :: forall a b. foreach (f :: a -> b) -> foreach (xs :: [a])
             -> size (map f xs) :~: size xs
lengthMapLaw f xs = lengthMap f xs

-- | Length of reverse (reused from HaskLib.lengthReverse).
lengthReverseLaw :: forall a. foreach (xs :: [a])
                 -> size (reverse xs) :~: size xs
lengthReverseLaw xs = lengthReverse xs

{-# LINE 116 "content/part1/Lists.md" #-}
-- | Map distributes over append: map f (xs ++ ys) = map f xs ++ map f ys.
mapAppend :: forall a b. foreach (f :: a -> b) -> foreach (xs :: [a]) -> foreach (ys :: [a])
          -> map f (xs ++ ys) :~: (map f xs ++ map f ys)
mapAppend f xs ys = case xs of
  []        -> Refl
  (_ : xs') -> gcastWith (mapAppend f xs' ys) Refl

-- | Functor composition law: map (g . f) xs = map g (map f xs).
mapCompose :: forall a b c. foreach (g :: b -> c) -> foreach (f :: a -> b) -> foreach (xs :: [a])
           -> map (g . f) xs :~: map g (map f xs)
mapCompose g f xs = case xs of
  []        -> Refl
  (_ : xs') -> gcastWith (mapCompose g f xs') Refl

-- | Functor identity law: map id xs = xs.
mapId :: forall a. foreach (xs :: [a]) -> map id xs :~: xs
mapId []       = Refl
mapId (_ : xs) = gcastWith (mapId xs) Refl

{-# LINE 175 "content/part1/Lists.md" #-}
-- | Evidence that predicate `p` holds for every element of `xs`.
data All (p :: a -> Type) (xs :: [a]) where
  AllNil  :: All p '[]
  AllCons :: p x -> All p xs -> All p (x ': xs)

-- | Evidence that predicate `p` holds for at least one element of `xs`.
data Any (p :: a -> Type) (xs :: [a]) where
  Here  :: p x -> Any p (x ': xs)
  There :: Any p xs -> Any p (x ': xs)

-- | List membership: `x` appears in `xs`.
type In (x :: a) (xs :: [a]) = Any ((:~:) x) xs

-- | If `p` holds for all of `xs` and all of `ys`, it holds for `xs ++ ys`.
allAppend :: All p xs -> All p ys -> All p (xs ++ ys)
allAppend AllNil           pys = pys
allAppend (AllCons px pxs) pys = AllCons px (allAppend pxs pys)

-- | Transforming element proofs under `All`.
allMap :: (forall x. p x -> q x) -> All p xs -> All q xs
allMap _ AllNil           = AllNil
allMap f (AllCons px pxs) = AllCons (f px) (allMap f pxs)

-- | Concrete membership proof: 0 ∈ [0, 1, 0].
zeroInList :: In 'Zero '[ 'Zero, 'Succ 'Zero, 'Zero ]
zeroInList = Here Refl

-- | Concrete non-membership proof: 2 ∉ [0, 1].
threeNotInList :: Not (In ('Succ ('Succ 'Zero)) '[ 'Zero, 'Succ 'Zero ])
threeNotInList (Here eq)          = case eq of {}
threeNotInList (There (Here eq))  = case eq of {}
threeNotInList (There (There p))  = case p of {}
