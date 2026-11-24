-- Generated from content/part1/Connectives.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LINE 12 "content/part1/Connectives.md" #-}
module PLFH.Part1.Connectives
  ( prodComm
  , prodAssoc
  , prodUnitR
  , prodUnitL
  , sumComm
  , sumAssoc
  , sumZeroR
  , sumZeroL
  , prodDistribSum
  , currying
  , expSum
  , expProd
  ) where

import Data.Void (Void, absurd)
import PLFH.Part1.Isomorphism (Iff (..))

{-# LINE 48 "content/part1/Connectives.md" #-}
-- | Commutativity of conjunction: (a, b) ⇔ (b, a).
prodComm :: Iff (a, b) (b, a)
prodComm = Iff (\(x, y) -> (y, x)) (\(y, x) -> (x, y))

-- | Associativity of conjunction: ((a, b), c) ⇔ (a, (b, c)).
prodAssoc :: Iff ((a, b), c) (a, (b, c))
prodAssoc = Iff (\((x, y), z) -> (x, (y, z))) (\(x, (y, z)) -> ((x, y), z))

-- | Right identity of conjunction: (a, ()) ⇔ a.
prodUnitR :: Iff (a, ()) a
prodUnitR = Iff fst (\x -> (x, ()))

-- | Left identity of conjunction: ((), a) ⇔ a.
prodUnitL :: Iff ((), a) a
prodUnitL = Iff snd (\x -> ((), x))

{-# LINE 70 "content/part1/Connectives.md" #-}
-- | Commutativity of disjunction: Either a b ⇔ Either b a.
sumComm :: Iff (Either a b) (Either b a)
sumComm = Iff (either Right Left) (either Right Left)

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

{-# LINE 101 "content/part1/Connectives.md" #-}
-- | Conjunction distributes over disjunction: (Either a b, c) ⇔ Either (a, c) (b, c).
prodDistribSum :: Iff (Either a b, c) (Either (a, c) (b, c))
prodDistribSum = Iff toF fromF
  where
    toF (Left x, z)  = Left (x, z)
    toF (Right y, z) = Right (y, z)

    fromF (Left (x, z))  = (Left x, z)
    fromF (Right (y, z)) = (Right y, z)

-- | Currying: (a -> b -> c) ⇔ ((a, b) -> c).
currying :: Iff (a -> b -> c) ((a, b) -> c)
currying = Iff uncurry curry

-- | Implication from a disjunction is a pair of implications.
expSum :: Iff (Either a b -> c) (a -> c, b -> c)
expSum = Iff (\f -> (f . Left, f . Right)) (\(f, g) -> either f g)

-- | Implication into a conjunction is a pair of implications.
expProd :: Iff (c -> (a, b)) (c -> a, c -> b)
expProd = Iff (\f -> (fst . f, snd . f)) (\(f, g) x -> (f x, g x))
