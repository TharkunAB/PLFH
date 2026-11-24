-- Generated from content/part1/Lists.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE AllowAmbiguousTypes, DataKinds, EmptyCase, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, Modifiers, NoListTuplePuns, PolyKinds, ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures, TypeApplications, TypeOperators #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}
{-# LINE 36 "content/part1/Lists.md" #-}
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
  , notAnyToAllNot
  , allNotToNotAny
  , notAnyIffAllNot
  , decAll
  , decAny
  , zeroInList
  , threeNotInList
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl), gcastWith)
import Data.Void (Void)
import GHC.Tuple (Tuple2)
import GHC.Types (List, Matchability)
import HaskLib (lengthAppend, lengthMap, lengthReverse, rewrite, size)
import HaskLib.Nat (Nat (..), plus)
import PLFH.Part1.Decidable (Dec (..), Not)
import PLFH.Part1.Isomorphism (Iff (..))

{-# LINE 103 "content/part1/Lists.md" #-}
-- | Associativity of Prelude list append: (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
appendAssoc :: forall a. foreach (xs :: List a) -> foreach (ys :: List a) -> foreach (zs :: List a)
            -> ((xs ++ ys) ++ zs) :~: (xs ++ (ys ++ zs))
appendAssoc []       _  _  = Refl
appendAssoc (_ : xs) ys zs = rewrite (appendAssoc xs ys zs) Refl

-- | Right identity of Prelude list append: xs ++ [] = xs.
appendNilR :: forall a. foreach (xs :: List a) -> (xs ++ []) :~: xs
appendNilR []       = Refl
appendNilR (_ : xs) = rewrite (appendNilR xs) Refl

{-# LINE 124 "content/part1/Lists.md" #-}
-- | Length of append (reused directly from HaskLib.lengthAppend).
lengthAppendLaw :: forall a. foreach (xs :: List a) -> foreach (ys :: List a)
                -> size (xs ++ ys) :~: plus (size xs) (size ys)
lengthAppendLaw = lengthAppend

-- | Length of map (reused directly from HaskLib.lengthMap).
lengthMapLaw :: forall a b. foreach (f :: a -> b) -> foreach (xs :: List a)
             -> size (map f xs) :~: size xs
lengthMapLaw = lengthMap

-- | Length of reverse (reused directly from HaskLib.lengthReverse).
lengthReverseLaw :: forall a. foreach (xs :: List a)
                 -> size (reverse xs) :~: size xs
lengthReverseLaw = lengthReverse

{-# LINE 156 "content/part1/Lists.md" #-}
-- | Map distributes over append: map f (xs ++ ys) = map f xs ++ map f ys.
mapAppend :: forall a b. foreach (f :: a -> b) -> foreach (xs :: List a) -> foreach (ys :: List a)
          -> map f (xs ++ ys) :~: (map f xs ++ map f ys)
mapAppend f xs ys = case xs of
  []        -> Refl
  (_ : xs') -> gcastWith (mapAppend f xs' ys) Refl

-- | Functor composition law: map (g . f) xs = map g (map f xs).
mapCompose :: forall a b c. foreach (g :: b -> c) -> foreach (f :: a -> b) -> foreach (xs :: List a)
           -> map (g . f) xs :~: map g (map f xs)
mapCompose g f xs = case xs of
  []        -> Refl
  (_ : xs') -> gcastWith (mapCompose g f xs') Refl

-- | Functor identity law: map id xs = xs.
mapId :: forall a. foreach (xs :: List a) -> map id xs :~: xs
mapId []       = Refl
mapId (_ : xs) = gcastWith (mapId xs) Refl

{-# LINE 202 "content/part1/Lists.md" #-}
-- | Accumulating linear-time list reversal helper `shunt`.
shunt :: List a -> List a -> List a
shunt []     ys = ys
shunt (x:xs) ys = shunt xs (x : ys)

-- | Distributivity of `shunt` over append (`shunt-++`).
shuntAppend :: forall a. foreach (xs :: List a) -> foreach (ys :: List a) -> foreach (zs :: List a)
            -> shunt (xs ++ ys) zs :~: shunt ys (shunt xs zs)
shuntAppend []     _  _  = Refl
shuntAppend (x:xs) ys zs = shuntAppend xs ys (x : zs)

-- | Countdown list from `n - 1` down to `0` (`downFrom`).
downFrom :: Nat -> List Nat
downFrom Zero     = []
downFrom (Succ n) = n : downFrom n

-- | A list of `n` copies of `Zero`.
zeros :: Nat -> List Nat
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

{-# LINE 273 "content/part1/Lists.md" #-}
-- | Matchability-polymorphic universal list predicate: `p` holds for every element of `xs`.
type All :: forall {a} {m :: Matchability}. (a %m -> Type) -> List a -> Type
data All p xs where
  AllNil  :: forall {a} {m :: Matchability} {p :: a %m -> Type}. All p []
  AllCons :: forall {a} {m :: Matchability} {p :: a %m -> Type} {x} {xs}.
             p x -> All p xs -> All p (x : xs)

-- | Matchability-polymorphic existential list predicate: `p` holds for some element of `xs`.
type Any :: forall {a} {m :: Matchability}. (a %m -> Type) -> List a -> Type
data Any p xs where
  Here  :: forall {a} {m :: Matchability} (p :: a %m -> Type) (x :: a) (xs :: List a).
           p x -> Any p (x : xs)
  There :: forall {a} {m :: Matchability} (p :: a %m -> Type) (xs :: List a) (x :: a).
           Any p xs -> Any p (x : xs)

-- | List membership (`_∈_`): `x` appears in `xs`.
type In (x :: a) (xs :: List a) = Any ((:~:) x) xs

{-# LINE 301 "content/part1/Lists.md" #-}
-- | If `p` holds for all of `xs` and all of `ys`, it holds for `xs ++ ys`.
allAppend :: forall {a} {m :: Matchability} {p :: a %m -> Type} {xs} {ys}.
             All p xs -> All p ys -> All p (xs ++ ys)
allAppend AllNil           pys = pys
allAppend (AllCons px pxs) pys = AllCons px (allAppend pxs pys)

-- | Transforming element proofs under `All`.
allMap :: forall {a} {m1 :: Matchability} {m2 :: Matchability}
                 {p :: a %m1 -> Type} {q :: a %m2 -> Type} {xs}.
          (forall x. p x -> q x) -> All p xs -> All q xs
allMap _ AllNil           = AllNil
allMap f (AllCons px pxs) = AllCons (f px) (allMap f pxs)

-- | Inversion of `All` over append: `All p (xs ++ ys)` splits into `All p xs` and `All p ys`.
allAppendInv :: forall {a} {m :: Matchability} {p :: a %m -> Type} {ys}.
                foreach (xs :: List a) -> All p (xs ++ ys) -> Tuple2 (All p xs) (All p ys)
allAppendInv []     ays            = (AllNil, ays)
allAppendInv (_:xs) (AllCons px r) =
  case allAppendInv xs r of
    (axs, ays) -> (AllCons px axs, ays)

-- | Left introduction for `Any` over append.
anyAppendL :: forall a {m :: Matchability} (p :: a %m -> Type) (xs :: List a) (ys :: List a).
              Any p xs -> Any p (xs ++ ys)
anyAppendL (Here px) = Here px
anyAppendL (There r) = There (anyAppendL @a @p @_ @ys r)

-- | Right introduction for `Any` over append.
anyAppendR :: forall a {m :: Matchability} (p :: a %m -> Type) (ys :: List a).
              foreach (xs :: List a) -> Any p ys -> Any p (xs ++ ys)
anyAppendR []     ays = ays
anyAppendR (x:xs) ays = There @p @(xs ++ ys) @x (anyAppendR @a @p @ys xs ays)

-- | Inversion of `Any` over append: `Any p (xs ++ ys)` comes from `xs` or `ys`.
anyAppendInv :: forall {a} {m :: Matchability} {p :: a %m -> Type} {ys}.
                foreach (xs :: List a) -> Any p (xs ++ ys) -> Either (Any p xs) (Any p ys)
anyAppendInv []     ays       = Right ays
anyAppendInv (_:_)  (Here px) = Left (Here px)
anyAppendInv (_:xs) (There r) =
  case anyAppendInv xs r of
    Left  axs -> Left (There axs)
    Right ays -> Right ays

{-# LINE 352 "content/part1/Lists.md" #-}
mkNotHere :: forall {a} {m :: Matchability} {p :: a %m -> Type} {x} {xs}.
             Not (Any p (x : xs)) -> Not (p x)
mkNotHere nany px = nany (Here px)

-- | De Morgan forward: `¬(Any p xs) -> All (¬ ∘ p) xs` using an inline type lambda!
notAnyToAllNot :: forall {a} {m :: Matchability} (p :: a %m -> Type).
                  foreach (xs :: List a) -> Not (Any p xs) -> All (\x -> Not (p x)) xs
notAnyToAllNot []     _    = AllNil
notAnyToAllNot (_:xs) nany =
  AllCons (mkNotHere nany) (notAnyToAllNot @p xs (\anyXs -> nany (There anyXs)))

-- | De Morgan backward: `All (¬ ∘ p) xs -> ¬(Any p xs)`.
allNotToNotAny :: forall {a} {m :: Matchability} (p :: a %m -> Type) (xs :: List a).
                  All (\x -> Not (p x)) xs -> Not (Any p xs)
allNotToNotAny (AllCons npx _) (Here px) = npx px
allNotToNotAny (AllCons _ nxs) (There r) = allNotToNotAny @p nxs r

-- | Full De Morgan bi-implication (`¬Any⇔All¬`): `Not (Any p xs) ⇔ All (\x -> Not (p x)) xs`.
notAnyIffAllNot :: forall {a} {m :: Matchability} (p :: a %m -> Type).
                   foreach (xs :: List a) -> Iff (Not (Any p xs)) (All (\x -> Not (p x)) xs)
notAnyIffAllNot [] = Iff (\_ -> AllNil) (\_ anyNil -> case anyNil of {})
notAnyIffAllNot (_:xs) = case notAnyIffAllNot @p xs of
  Iff toTail fromTail ->
    Iff (\nany -> AllCons (mkNotHere nany) (toTail (\r -> nany (There r))))
        (\case AllCons npx nxs -> \case { Here px -> npx px; There r -> fromTail nxs r })

{-# LINE 385 "content/part1/Lists.md" #-}
-- | Decidability of universal list quantification `All p xs` (`All?`).
decAll :: forall {a} {m :: Matchability} {p :: a %m -> Type}.
          (foreach (x :: a) -> Dec (p x)) -> foreach (xs :: List a) -> Dec (All p xs)
decAll d xs = case xs of
  []    -> Yes AllNil
  x:xs' -> case d x of
    No npx -> No (\case AllCons px _ -> npx px)
    Yes px -> case decAll d xs' of
      Yes axs -> Yes (AllCons px axs)
      No naxs -> No (\case AllCons _ axs -> naxs axs)

-- | Decidability of existential list quantification `Any p xs` (`Any?`).
decAny :: forall {a} {m :: Matchability} {p :: a %m -> Type}.
          (foreach (x :: a) -> Dec (p x)) -> foreach (xs :: List a) -> Dec (Any p xs)
decAny d xs = case xs of
  []    -> No (\case {})
  x:xs' -> case d x of
    Yes px  -> Yes (Here px)
    No  npx -> case decAny d xs' of
      Yes axs -> Yes (There axs)
      No naxs -> No (\case Here px -> npx px; There axs -> naxs axs)

-- | Concrete membership proof: 0 ∈ [0, 1, 0] (zero ticks with NoListTuplePuns!).
zeroInList :: In (0 :: Nat) [0 :: Nat, 1 :: Nat, 0 :: Nat]
zeroInList = Here Refl

-- | Concrete non-membership proof: 2 ∉ [0, 1].
threeNotInList :: Not (In (2 :: Nat) [0 :: Nat, 1 :: Nat])
threeNotInList (Here eq)          = case eq of {}
threeNotInList (There (Here eq))  = case eq of {}
threeNotInList (There (There p))  = case p of {}
