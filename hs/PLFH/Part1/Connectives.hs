-- Generated from content/part1/Connectives.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DependentTypes, ListTuplePuns #-}
{-# LINE 58 "content/part1/Connectives.md" #-}
module PLFH.Part1.Connectives
  ( swapProd
  , swapProdRT
  , prodCommIso
  , prodComm
  , prodAssoc
  , prodUnitR
  , prodUnitL
  , prodZeroR
  , prodZeroL
  , swapSum
  , swapSumRT
  , sumCommIso
  , sumComm
  , sumAssoc
  , sumZeroR
  , sumZeroL
  , prodDistribSum
  , prodDistribSumL
  , currying
  , expSum
  , expProd
  , expUnit
  , expZero
  , expToUnit
  , prodCong
  , sumCong
  , arrCong
  ) where

import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void, absurd)
import PLFH.Part1.Isomorphism (Iff (..), Iso (..))

{-# LINE 110 "content/part1/Connectives.md" #-}
-- | Swap the two components of a pair.
swapProd :: (a, b) -> (b, a)
swapProd (x, y) = (y, x)

-- | Swapping a pair twice returns the original pair.
swapProdRT :: foreach (p :: (a, b)) -> swapProd (swapProd p) :~: p
swapProdRT (_, _) = Refl

-- | Commutativity of conjunction as a true isomorphism: (a, b) ≃ (b, a).
prodCommIso :: Iso (a, b) (b, a)
prodCommIso = MkIso swapProd swapProd swapProdRT swapProdRT

-- | Commutativity of conjunction: (a, b) ⇔ (b, a).
prodComm :: Iff (a, b) (b, a)
prodComm = Iff swapProd swapProd

-- | Associativity of conjunction: ((a, b), c) ⇔ (a, (b, c)).
prodAssoc :: Iff ((a, b), c) (a, (b, c))
prodAssoc = Iff (\((x, y), z) -> (x, (y, z))) (\(x, (y, z)) -> ((x, y), z))

-- | Right identity of conjunction: (a, ()) ⇔ a.
prodUnitR :: Iff (a, ()) a
prodUnitR = Iff fst (\x -> (x, ()))

-- | Left identity of conjunction: ((), a) ⇔ a.
prodUnitL :: Iff ((), a) a
prodUnitL = Iff snd (\x -> ((), x))

-- | Right zero of conjunction: (a, Void) ⇔ Void.
prodZeroR :: Iff (a, Void) Void
prodZeroR = Iff snd absurd

-- | Left zero of conjunction: (Void, a) ⇔ Void.
prodZeroL :: Iff (Void, a) Void
prodZeroL = Iff fst absurd

{-# LINE 171 "content/part1/Connectives.md" #-}
-- | Swap the two branches of a sum.
swapSum :: Either a b -> Either b a
swapSum (Left x)  = Right x
swapSum (Right y) = Left y

-- | Swapping a sum twice returns the original sum.
swapSumRT :: foreach (s :: Either a b) -> swapSum (swapSum s) :~: s
swapSumRT (Left _)  = Refl
swapSumRT (Right _) = Refl

-- | Commutativity of disjunction as a true isomorphism: Either a b ≃ Either b a.
sumCommIso :: Iso (Either a b) (Either b a)
sumCommIso = MkIso swapSum swapSum swapSumRT swapSumRT

-- | Commutativity of disjunction: Either a b ⇔ Either b a.
sumComm :: Iff (Either a b) (Either b a)
sumComm = Iff swapSum swapSum

-- | Associativity of disjunction: Either (Either a b) c ⇔ Either a (Either b c).
sumAssoc :: Iff (Either (Either a b) c) (Either a (Either b c))
sumAssoc = Iff toF fromF
  where
    toF (Left (Left x))  = Left x
    toF (Left (Right y)) = Right (Left y)
    toF (Right z)        = Right (Right z)

    fromF (Left x)          = Left (Left x)
    fromF (Right (Left y))  = Left (Right y)
    fromF (Right (Right z)) = Right z

-- | Right identity of disjunction: Either a Void ⇔ a.
sumZeroR :: Iff (Either a Void) a
sumZeroR = Iff (either id absurd) Left

-- | Left identity of disjunction: Either Void a ⇔ a.
sumZeroL :: Iff (Either Void a) a
sumZeroL = Iff (either absurd id) Right

{-# LINE 217 "content/part1/Connectives.md" #-}
-- | Right distributivity: (Either a b, c) ⇔ Either (a, c) (b, c).
prodDistribSum :: Iff (Either a b, c) (Either (a, c) (b, c))
prodDistribSum = Iff toF fromF
  where
    toF (Left x, z)  = Left (x, z)
    toF (Right y, z) = Right (y, z)

    fromF (Left (x, z))  = (Left x, z)
    fromF (Right (y, z)) = (Right y, z)

-- | Left distributivity: (a, Either b c) ⇔ Either (a, b) (a, c).
prodDistribSumL :: Iff (a, Either b c) (Either (a, b) (a, c))
prodDistribSumL = Iff toF fromF
  where
    toF (x, Left y)  = Left (x, y)
    toF (x, Right z) = Right (x, z)

    fromF (Left (x, y))  = (x, Left y)
    fromF (Right (x, z)) = (x, Right z)

{-# LINE 258 "content/part1/Connectives.md" #-}
-- | Currying: (a -> b -> c) ⇔ ((a, b) -> c).
currying :: Iff (a -> b -> c) ((a, b) -> c)
currying = Iff uncurry curry

-- | Implication from a disjunction is a pair of implications: c^(a+b) ⇔ c^a × c^b.
expSum :: Iff (Either a b -> c) (a -> c, b -> c)
expSum = Iff (\f -> (f . Left, f . Right)) (\(f, g) -> either f g)

-- | Implication into a conjunction is a pair of implications: (a×b)^c ⇔ a^c × b^c.
expProd :: Iff (c -> (a, b)) (c -> a, c -> b)
expProd = Iff (\f -> (fst . f, snd . f)) (\(f, g) x -> (f x, g x))

-- | Exponent 1: (() -> a) ⇔ a.
expUnit :: Iff (() -> a) a
expUnit = Iff (\f -> f ()) const

-- | Exponent 0: (Void -> a) ⇔ ().
expZero :: Iff (Void -> a) ()
expZero = Iff (const ()) (\() -> absurd)

-- | Base 1: (a -> ()) ⇔ ().
expToUnit :: Iff (a -> ()) ()
expToUnit = Iff (const ()) (\() _ -> ())

{-# LINE 292 "content/part1/Connectives.md" #-}
-- | Congruence of conjunction under `Iff`.
prodCong :: Iff a a' -> Iff b b' -> Iff (a, b) (a', b')
prodCong (Iff fa ga) (Iff fb gb) = Iff (\(x, y) -> (fa x, fb y)) (\(x, y) -> (ga x, gb y))

-- | Congruence of disjunction under `Iff`.
sumCong :: Iff a a' -> Iff b b' -> Iff (Either a b) (Either a' b')
sumCong (Iff fa ga) (Iff fb gb) = Iff (either (Left . fa) (Right . fb)) (either (Left . ga) (Right . gb))

-- | Congruence of implication under `Iff` (contravariant in the domain).
arrCong :: Iff a a' -> Iff b b' -> Iff (a -> b) (a' -> b')
arrCong (Iff fa ga) (Iff fb gb) = Iff (\h -> fb . h . ga) (\h -> gb . h . fa)
