-- Generated from content/part1/Lists.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE AllowAmbiguousTypes, DependentTypes #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}
{-# LINE 34 "content/part1/Lists.md" #-}
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
  , rev
  , revAppend
  , revInvolutive
  , shuntRev
  , reverses
  , downFrom
  , zeros
  , lengthDownFrom
  , lengthZeros
  , foldrPlusSeed
  , foldrPlusAppend
  , foldrTimesSeed
  , foldrTimesAppend
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
  , allToIn
  , inToAll
  , AnyWitness (..)
  , anyToWitness
  , witnessToAny
  , anyIffWitness
  , memberValue
  , decAll
  , decAny
  , decIn
  , zeroInList
  , threeNotInList
  ) where

import Prelude hiding (foldr)
import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl), gcastWith, sym, trans)
import Data.Void (Void)
import GHC.Tuple (Tuple2)
import GHC.Types (List)
import HaskLib (Matchability, foldr, lengthReverse, rewrite, size)
import HaskLib.Nat (Nat (..), plus, plusZero)
import PLFH.Part1.Decidable (Dec (..), Not)
import PLFH.Part1.Induction (cong, plusAssoc, timesAssoc)
import PLFH.Part1.Isomorphism (Iff (..))
import PLFH.Part1.Naturals (times)

{-# LINE 121 "content/part1/Lists.md" #-}
-- | Associativity of Prelude list append: (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
appendAssoc :: forall a. foreach (xs ys zs :: List a)
            -> ((xs ++ ys) ++ zs) :~: (xs ++ (ys ++ zs))
appendAssoc []       _  _  = Refl
appendAssoc (_ : xs) ys zs = rewrite (appendAssoc xs ys zs) Refl

-- | Right identity of Prelude list append: xs ++ [] = xs.
appendNilR :: forall a. foreach (xs :: List a) -> (xs ++ []) :~: xs
appendNilR []       = Refl
appendNilR (_ : xs) = rewrite (appendNilR xs) Refl

{-# LINE 144 "content/part1/Lists.md" #-}
-- | Length of append: size (xs ++ ys) = size xs + size ys.
lengthAppendLaw :: forall a. foreach (xs ys :: List a)
                -> size (xs ++ ys) :~: plus (size xs) (size ys)
lengthAppendLaw []       _  = Refl
lengthAppendLaw (_ : xs) ys = cong Succ (lengthAppendLaw xs ys)

-- | Length of map: size (map f xs) = size xs.
lengthMapLaw :: forall a b. foreach (f :: a -> b) -> foreach (xs :: List a)
             -> size (map f xs) :~: size xs
lengthMapLaw _ []       = Refl
lengthMapLaw f (_ : xs) = cong Succ (lengthMapLaw f xs)

-- | Length of Prelude reverse (proved via accumulator in HaskLib.List.lengthReverse).
lengthReverseLaw :: forall a. foreach (xs :: List a)
                 -> size (reverse xs) :~: size xs
lengthReverseLaw = lengthReverse

{-# LINE 178 "content/part1/Lists.md" #-}
-- | Map distributes over append: map f (xs ++ ys) = map f xs ++ map f ys.
mapAppend :: forall a b. foreach (f :: a -> b) -> foreach (xs :: List a) -> foreach (ys :: List a)
          -> map f (xs ++ ys) :~: (map f xs ++ map f ys)
mapAppend _ []       _  = Refl
mapAppend f (_ : xs) ys = gcastWith (mapAppend f xs ys) Refl

-- | Functor composition law: map (g . f) xs = map g (map f xs).
mapCompose :: forall a b c. foreach (g :: b -> c) -> foreach (f :: a -> b) -> foreach (xs :: List a)
           -> map (g . f) xs :~: map g (map f xs)
mapCompose _ _ []       = Refl
mapCompose g f (_ : xs) = gcastWith (mapCompose g f xs) Refl

-- | Functor identity law: map id xs = xs.
mapId :: forall a. foreach (xs :: List a) -> map id xs :~: xs
mapId []       = Refl
mapId (_ : xs) = gcastWith (mapId xs) Refl

{-# LINE 211 "content/part1/Lists.md" #-}
-- | Accumulating linear-time list reversal helper `shunt`.
shunt :: List a -> List a -> List a
shunt []     ys = ys
shunt (x:xs) ys = shunt xs (x : ys)

-- | Distributivity of `shunt` over append (`shunt-++`).
shuntAppend :: forall a. foreach (xs ys zs :: List a)
            -> shunt (xs ++ ys) zs :~: shunt ys (shunt xs zs)
shuntAppend []     _  _  = Refl
shuntAppend (x:xs) ys zs = shuntAppend xs ys (x : zs)

-- | Naive quadratic list reversal (`reverse` in PLFA).
rev :: List a -> List a
rev []     = []
rev (x:xs) = rev xs ++ [x]

-- | Reversal distributes contravariantly over append (`reverse-++-distrib`).
revAppend :: forall a. foreach (xs ys :: List a)
          -> rev (xs ++ ys) :~: (rev ys ++ rev xs)
revAppend []     ys = sym (appendNilR @a (rev ys))
revAppend (x:xs) ys =
  case revAppend xs ys of
    Refl -> case appendAssoc (rev ys) (rev xs) [x] of
      Refl -> Refl

-- | Reversing a list twice returns the original list (`reverse-involutive`).
revInvolutive :: forall a. foreach (xs :: List a) -> rev (rev xs) :~: xs
revInvolutive []     = Refl
revInvolutive (x:xs) =
  case revAppend (rev xs) [x] of
    Refl -> case revInvolutive xs of
      Refl -> Refl

-- | Relating `shunt` to naive `rev` (`shunt-reverse`): `shunt xs ys = rev xs ++ ys`.
shuntRev :: forall a. foreach (xs ys :: List a)
         -> shunt xs ys :~: (rev xs ++ ys)
shuntRev []     _  = Refl
shuntRev (x:xs) ys =
  case shuntRev xs (x : ys) of
    Refl -> case appendAssoc (rev xs) [x] ys of
      Refl -> Refl

-- | Fast linear-time reversal `shunt xs []` agrees with naive `rev xs` (`reverses`)!
reverses :: forall a. foreach (xs :: List a) -> shunt xs [] :~: rev xs
reverses xs =
  case shuntRev xs [] of
    Refl -> appendNilR (rev xs)

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

{-# LINE 292 "content/part1/Lists.md" #-}
-- | Move the seed to the right of the zero-seeded fold.
foldrPlusSeed :: foreach (xs :: List Nat) -> foreach (z :: Nat)
              -> foldr plus z xs :~: plus (foldr plus Zero xs) z
foldrPlusSeed []       _ = Refl
foldrPlusSeed (x : xs) z =
  trans (cong (plus x) (foldrPlusSeed xs z))
        (sym (plusAssoc x (foldr plus Zero xs) z))

-- | Sum concatenated lists by adding their individual sums (`foldr-monoid-++` for `+`).
foldrPlusAppend :: foreach (xs ys :: List Nat)
                -> foldr plus Zero (xs ++ ys)
               :~: plus (foldr plus Zero xs) (foldr plus Zero ys)
foldrPlusAppend []       _  = Refl
foldrPlusAppend (x : xs) ys =
  trans (cong (plus x) (foldrPlusAppend xs ys))
        (sym (plusAssoc x (foldr plus Zero xs) (foldr plus Zero ys)))

-- | Move the seed to the right of a multiplicative right fold.
foldrTimesSeed :: foreach (xs :: List Nat) -> foreach (z :: Nat)
               -> foldr times z xs :~: times (foldr times 1 xs) z
foldrTimesSeed []       z = sym (plusZero z)
foldrTimesSeed (x : xs) z =
  trans (cong (times x) (foldrTimesSeed xs z))
        (sym (timesAssoc x (foldr times 1 xs) z))

-- | Multiply concatenated lists by multiplying their individual products (`foldr-monoid-++` for `*`).
foldrTimesAppend :: foreach (xs ys :: List Nat)
                 -> foldr times 1 (xs ++ ys)
                :~: times (foldr times 1 xs) (foldr times 1 ys)
foldrTimesAppend []       ys = sym (plusZero (foldr times 1 ys))
foldrTimesAppend (x : xs) ys =
  trans (cong (times x) (foldrTimesAppend xs ys))
        (sym (timesAssoc x (foldr times 1 xs) (foldr times 1 ys)))

{-# LINE 355 "content/part1/Lists.md" #-}
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

{-# LINE 383 "content/part1/Lists.md" #-}
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

{-# LINE 434 "content/part1/Lists.md" #-}
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

{-# LINE 470 "content/part1/Lists.md" #-}
-- | Evidence that a member of the list satisfies the predicate.
type AnyWitness :: forall {a} {m :: Matchability}. (a %m -> Type) -> List a -> Type
data AnyWitness p xs where
  MkAnyWitness :: forall {a} {m :: Matchability} {p :: a %m -> Type} {x} {xs}.
                  In x xs -> p x -> AnyWitness p xs

anyToWitness :: forall {a} {m :: Matchability} {p :: a %m -> Type} {xs}.
                Any p xs -> AnyWitness p xs
anyToWitness (Here px) = MkAnyWitness (Here Refl) px
anyToWitness (There r) = case anyToWitness r of
  MkAnyWitness member px -> MkAnyWitness (There member) px

witnessToAny :: forall {a} {m :: Matchability} {p :: a %m -> Type} {xs}.
                AnyWitness p xs -> Any p xs
witnessToAny (MkAnyWitness (Here Refl) px) = Here px
witnessToAny (MkAnyWitness (There member) px) =
  There (witnessToAny (MkAnyWitness member px))

-- | `Any` holds exactly when a list member satisfies the predicate (`Any-∃`).
anyIffWitness :: forall {a} {m :: Matchability} (p :: a %m -> Type) (xs :: List a).
                 Iff (Any p xs) (AnyWitness p xs)
anyIffWitness = Iff anyToWitness witnessToAny

-- | Read the element at the position selected by a membership proof.
memberValue :: forall a (x :: a). foreach (xs :: List a) -> In x xs -> a
memberValue []       r           = case r of {}
memberValue (x : _)  (Here Refl) = x
memberValue (_ : xs) (There r)   = memberValue xs r

{-# LINE 520 "content/part1/Lists.md" #-}
-- | Pointwise characterization of `All`: if `p` holds for all elements of `xs`
-- and `x ∈ xs`, then `p x` (`All-to-∈`).
allToIn :: forall {a} {m :: Matchability} {p :: a %m -> Type} {x} {xs}.
           All p xs -> In x xs -> p x
allToIn (AllCons px _)   (Here Refl) = px
allToIn (AllCons _  pxs) (There r)   = allToIn pxs r

-- | Converse (`∈-to-All`): if `p x` holds for every member `x ∈ xs`, then `All p xs`.
inToAll :: forall {a} {m :: Matchability} {p :: a %m -> Type}.
           foreach (xs :: List a) -> (forall (x :: a). In x xs -> p x) -> All p xs
inToAll []       _ = AllNil
inToAll (x : xs) f = AllCons (f @x (Here Refl)) (inToAll xs (\r -> f (There r)))

-- | Decidability of universal list quantification `All p xs` (`All?`).
decAll :: forall {a} {m :: Matchability} {p :: a %m -> Type}.
          (foreach (x :: a) -> Dec (p x)) -> foreach (xs :: List a) -> Dec (All p xs)
decAll _ []       = Yes AllNil
decAll d (x : xs) = case d x of
  No npx -> No (\case AllCons px _ -> npx px)
  Yes px -> case decAll d xs of
    Yes axs -> Yes (AllCons px axs)
    No naxs -> No (\case AllCons _ axs -> naxs axs)

-- | Decidability of existential list quantification `Any p xs` (`Any?`).
decAny :: forall {a} {m :: Matchability} {p :: a %m -> Type}.
          (foreach (x :: a) -> Dec (p x)) -> foreach (xs :: List a) -> Dec (Any p xs)
decAny _ []       = No (\case {})
decAny d (x : xs) = case d x of
  Yes px  -> Yes (Here px)
  No  npx -> case decAny d xs of
    Yes axs -> Yes (There axs)
    No naxs -> No (\case Here px -> npx px; There axs -> naxs axs)

-- | Decidability of list membership `In x xs` given decidable element equality (`∈?`).
decIn :: forall {a}.
         (foreach (x y :: a) -> Dec (x :~: y))
      -> foreach (x :: a) -> foreach (xs :: List a) -> Dec (In x xs)
decIn _     _ []       = No (\case {})
decIn decEq x (y : ys) = case decEq x y of
  Yes Refl -> Yes (Here Refl)
  No  neq  -> case decIn decEq x ys of
    Yes iys -> Yes (There iys)
    No niys -> No (\case { Here eq -> neq eq; There r -> niys r })

-- | Concrete membership proof: 0 ∈ [0, 1, 0] (zero ticks with NoListTuplePuns!).
zeroInList :: In (0 :: Nat) [0 :: Nat, 1 :: Nat, 0 :: Nat]
zeroInList = Here Refl

-- | Concrete non-membership proof: 3 ∉ [0, 1, 0, 2].
threeNotInList :: Not (In (3 :: Nat) [0 :: Nat, 1 :: Nat, 0 :: Nat, 2 :: Nat])
threeNotInList (Here eq)                          = case eq of {}
threeNotInList (There (Here eq))                  = case eq of {}
threeNotInList (There (There (Here eq)))          = case eq of {}
threeNotInList (There (There (There (Here eq))))  = case eq of {}
threeNotInList (There (There (There (There p))))  = case p of {}
