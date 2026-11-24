-- Generated from content/part1/Lists.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE AllowAmbiguousTypes, DataKinds, EmptyCase, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, PolyKinds, ScopedTypeVariables, TypeApplications, TypeOperators #-}
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
  , shunt
  , shuntAppend
  , downFrom
  , zeros
  , lengthDownFrom
  , lengthZeros
  , All (..)
  , Any (..)
  , In
  , allAppend
  , allAppendInv
  , allMap
  , anyAppendL
  , anyAppendR
  , anyAppendInv
  , decAll
  , decAny
  , zeroInList
  , threeNotInList
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl), gcastWith)
import Data.Void (Void)
import HaskLib (lengthAppend, lengthMap, lengthReverse, rewrite, size)
import HaskLib.Nat (Nat (..), plus)
import PLFH.Part1.Decidable (Dec (..), Not)

{-# LINE 66 "content/part1/Lists.md" #-}
-- | Associativity of Prelude list append: (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
appendAssoc :: forall a. foreach (xs :: [a]) -> foreach (ys :: [a]) -> foreach (zs :: [a])
            -> ((xs ++ ys) ++ zs) :~: (xs ++ (ys ++ zs))
appendAssoc []       _  _  = Refl
appendAssoc (_ : xs) ys zs = rewrite (appendAssoc xs ys zs) Refl

-- | Right identity of Prelude list append: xs ++ [] = xs.
appendNilR :: forall a. foreach (xs :: [a]) -> (xs ++ '[]) :~: xs
appendNilR []       = Refl
appendNilR (_ : xs) = rewrite (appendNilR xs) Refl

{-# LINE 85 "content/part1/Lists.md" #-}
-- | Length of append (reused directly from HaskLib.lengthAppend).
lengthAppendLaw :: forall a. foreach (xs :: [a]) -> foreach (ys :: [a])
                -> size (xs ++ ys) :~: plus (size xs) (size ys)
lengthAppendLaw = lengthAppend

-- | Length of map (reused directly from HaskLib.lengthMap).
lengthMapLaw :: forall a b. foreach (f :: a -> b) -> foreach (xs :: [a])
             -> size (map f xs) :~: size xs
lengthMapLaw = lengthMap

-- | Length of reverse (reused directly from HaskLib.lengthReverse).
lengthReverseLaw :: forall a. foreach (xs :: [a])
                 -> size (reverse xs) :~: size xs
lengthReverseLaw = lengthReverse

{-# LINE 115 "content/part1/Lists.md" #-}
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

{-# LINE 153 "content/part1/Lists.md" #-}
-- | Accumulating list reversal helper `shunt`.
shunt :: [a] -> [a] -> [a]
shunt []     ys = ys
shunt (x:xs) ys = shunt xs (x : ys)

-- | Distributivity of `shunt` over append (`shunt-++`).
shuntAppend :: forall a. foreach (xs :: [a]) -> foreach (ys :: [a]) -> foreach (zs :: [a])
            -> shunt (xs ++ ys) zs :~: shunt ys (shunt xs zs)
shuntAppend []     _  _  = Refl
shuntAppend (x:xs) ys zs = shuntAppend xs ys (x : zs)

-- | Countdown list from `n - 1` down to `0` (`downFrom`).
downFrom :: Nat -> [Nat]
downFrom Zero     = []
downFrom (Succ n) = n : downFrom n

-- | A list of `n` copies of `Zero`.
zeros :: Nat -> [Nat]
zeros Zero     = []
zeros (Succ n) = Zero : zeros n

-- | Length of `downFrom n` equals `n`.
lengthDownFrom :: foreach (n :: Nat) -> size (downFrom n) :~: n
lengthDownFrom Zero     = Refl
lengthDownFrom (Succ n) = case lengthDownFrom n of { Refl -> Refl }

-- | Length of `zeros n` equals `n`.
lengthZeros :: foreach (n :: Nat) -> size (zeros n) :~: n
lengthZeros Zero     = Refl
lengthZeros (Succ n) = case lengthZeros n of { Refl -> Refl }

{-# LINE 213 "content/part1/Lists.md" #-}
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

-- | Inversion of `All` over append: `All p (xs ++ ys)` splits into `All p xs` and `All p ys`.
allAppendInv :: foreach (xs :: [a]) -> All p (xs ++ ys) -> (All p xs, All p ys)
allAppendInv []     ays            = (AllNil, ays)
allAppendInv (_:xs) (AllCons px r) =
  case allAppendInv xs r of
    (axs, ays) -> (AllCons px axs, ays)

-- | Left introduction for `Any` over append.
anyAppendL :: forall a (p :: a -> Type) (xs :: [a]) (ys :: [a]). Any p xs -> Any p (xs ++ ys)
anyAppendL (Here px) = Here px
anyAppendL (There r) = There (anyAppendL @a @p @_ @ys r)

-- | Right introduction for `Any` over append.
anyAppendR :: forall a (p :: a -> Type) (ys :: [a]).
              foreach (xs :: [a]) -> Any p ys -> Any p (xs ++ ys)
anyAppendR []     ays = ays
anyAppendR (x:xs) ays = There @p @(xs ++ ys) @x (anyAppendR @a @p @ys xs ays)

-- | Inversion of `Any` over append: `Any p (xs ++ ys)` comes from `xs` or `ys`.
anyAppendInv :: foreach (xs :: [a]) -> Any p (xs ++ ys) -> Either (Any p xs) (Any p ys)
anyAppendInv []     ays       = Right ays
anyAppendInv (_:_)  (Here px) = Left (Here px)
anyAppendInv (_:xs) (There r) =
  case anyAppendInv xs r of
    Left  axs -> Left (There axs)
    Right ays -> Right ays

-- | Decidability of universal list quantification `All p xs`.
decAll :: (foreach (x :: a) -> Dec (p x)) -> foreach (xs :: [a]) -> Dec (All p xs)
decAll d xs = case xs of
  []    -> Yes AllNil
  x:xs' -> case d x of
    No npx -> No (\case AllCons px _ -> npx px)
    Yes px -> case decAll d xs' of
      Yes axs -> Yes (AllCons px axs)
      No naxs -> No (\case AllCons _ axs -> naxs axs)

-- | Decidability of existential list quantification `Any p xs`.
decAny :: (foreach (x :: a) -> Dec (p x)) -> foreach (xs :: [a]) -> Dec (Any p xs)
decAny d xs = case xs of
  []    -> No (\case {})
  x:xs' -> case d x of
    Yes px  -> Yes (Here px)
    No  npx -> case decAny d xs' of
      Yes axs -> Yes (There axs)
      No naxs -> No (\case Here px -> npx px; There axs -> naxs axs)

-- | Concrete membership proof: 0 ∈ [0, 1, 0].
zeroInList :: In (0 :: Nat) '[ (0 :: Nat), (1 :: Nat), (0 :: Nat) ]
zeroInList = Here Refl

-- | Concrete non-membership proof: 2 ∉ [0, 1].
threeNotInList :: Not (In (2 :: Nat) '[ (0 :: Nat), (1 :: Nat) ])
threeNotInList (Here eq)          = case eq of {}
threeNotInList (There (Here eq))  = case eq of {}
threeNotInList (There (There p))  = case p of {}
