-- Generated from content/part1/Connectives.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DependentTypes, ListTuplePuns #-}
{-# LINE 58 "content/part1/Connectives.md" #-}
module PLFH.Part1.Connectives
  ( swapProd
  , swapProdRT
  , prodCommIso
  , prodComm
  , prodAssocTo
  , prodAssocFrom
  , prodAssocIso
  , prodAssoc
  , prodUnitRTo
  , prodUnitRFrom
  , prodUnitRIso
  , prodUnitR
  , prodUnitLTo
  , prodUnitLFrom
  , prodUnitLIso
  , prodUnitL
  , prodZeroRTo
  , prodZeroRFrom
  , prodZeroRIso
  , prodZeroR
  , prodZeroLTo
  , prodZeroLFrom
  , prodZeroLIso
  , prodZeroL
  , swapSum
  , swapSumRT
  , sumCommIso
  , sumComm
  , sumAssocTo
  , sumAssocFrom
  , sumAssocIso
  , sumAssoc
  , sumZeroRTo
  , sumZeroRIso
  , sumZeroR
  , sumZeroLTo
  , sumZeroLIso
  , sumZeroL
  , prodDistribSumTo
  , prodDistribSumFrom
  , prodDistribSumIso
  , prodDistribSum
  , prodDistribSumLTo
  , prodDistribSumLFrom
  , prodDistribSumLIso
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
  , etaProd
  , etaUnit
  , etaSum
  , etaArr
  , sumDistribProdTo
  , sumDistribProdFrom
  , sumDistribProd
  ) where

import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void, absurd)
import PLFH.Part1.Isomorphism (Embed (..), Iff (..), Iso (..), embedImpliesIff, isoImpliesEmbed)

{-# LINE 147 "content/part1/Connectives.md" #-}
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
prodComm = embedImpliesIff (isoImpliesEmbed prodCommIso)

-- | Forward map for product associativity.
prodAssocTo :: ((a, b), c) -> (a, (b, c))
prodAssocTo ((x, y), z) = (x, (y, z))

-- | Backward map for product associativity.
prodAssocFrom :: (a, (b, c)) -> ((a, b), c)
prodAssocFrom (x, (y, z)) = ((x, y), z)

prodAssocLR :: foreach (p :: ((a, b), c)) -> prodAssocFrom (prodAssocTo p) :~: p
prodAssocLR ((_, _), _) = Refl

prodAssocRL :: foreach (p :: (a, (b, c))) -> prodAssocTo (prodAssocFrom p) :~: p
prodAssocRL (_, (_, _)) = Refl

-- | Associativity of conjunction as a true isomorphism: ((a, b), c) ≃ (a, (b, c)).
prodAssocIso :: Iso ((a, b), c) (a, (b, c))
prodAssocIso = MkIso prodAssocTo prodAssocFrom prodAssocLR prodAssocRL

-- | Associativity of conjunction: ((a, b), c) ⇔ (a, (b, c)).
prodAssoc :: Iff ((a, b), c) (a, (b, c))
prodAssoc = embedImpliesIff (isoImpliesEmbed prodAssocIso)

-- | Right-identity maps for conjunction.
prodUnitRTo :: (a, ()) -> a
prodUnitRTo (x, ()) = x

prodUnitRFrom :: a -> (a, ())
prodUnitRFrom x = (x, ())

prodUnitRLR :: foreach (p :: (a, ())) -> prodUnitRFrom (prodUnitRTo p) :~: p
prodUnitRLR (_, ()) = Refl

prodUnitRRL :: foreach (x :: a) -> prodUnitRTo (prodUnitRFrom x) :~: x
prodUnitRRL _ = Refl

-- | Right identity of conjunction as a true isomorphism: (a, ()) ≃ a.
prodUnitRIso :: Iso (a, ()) a
prodUnitRIso = MkIso prodUnitRTo prodUnitRFrom prodUnitRLR prodUnitRRL

-- | Right identity of conjunction: (a, ()) ⇔ a.
prodUnitR :: Iff (a, ()) a
prodUnitR = embedImpliesIff (isoImpliesEmbed prodUnitRIso)

-- | Left-identity maps for conjunction.
prodUnitLTo :: ((), a) -> a
prodUnitLTo ((), x) = x

prodUnitLFrom :: a -> ((), a)
prodUnitLFrom x = ((), x)

prodUnitLLR :: foreach (p :: ((), a)) -> prodUnitLFrom (prodUnitLTo p) :~: p
prodUnitLLR ((), _) = Refl

prodUnitLRL :: foreach (x :: a) -> prodUnitLTo (prodUnitLFrom x) :~: x
prodUnitLRL _ = Refl

-- | Left identity of conjunction as a true isomorphism: ((), a) ≃ a.
prodUnitLIso :: Iso ((), a) a
prodUnitLIso = MkIso prodUnitLTo prodUnitLFrom prodUnitLLR prodUnitLRL

-- | Left identity of conjunction: ((), a) ⇔ a.
prodUnitL :: Iff ((), a) a
prodUnitL = embedImpliesIff (isoImpliesEmbed prodUnitLIso)

-- | Right-zero maps for conjunction.
prodZeroRTo :: (a, Void) -> Void
prodZeroRTo (_, v) = v

prodZeroRFrom :: Void -> (a, Void)
prodZeroRFrom = absurd

-- | Right zero of conjunction as a true isomorphism: (a, Void) ≃ Void.
prodZeroRIso :: forall a. Iso (a, Void) Void
prodZeroRIso = go prodZeroRTo prodZeroRFrom
  where
    go :: foreach (t :: (a, Void) -> Void) -> foreach (f :: Void -> (a, Void))
       -> Iso (a, Void) Void
    go t f = MkIso t f lr rl
      where
        lr :: foreach (p :: (a, Void)) -> f (t p) :~: p
        lr (_, v) = case v of {}
        rl :: foreach (v :: Void) -> t (f v) :~: v
        rl v = case v of {}

-- | Right zero of conjunction: (a, Void) ⇔ Void.
prodZeroR :: Iff (a, Void) Void
prodZeroR = embedImpliesIff (isoImpliesEmbed prodZeroRIso)

-- | Left-zero maps for conjunction.
prodZeroLTo :: (Void, a) -> Void
prodZeroLTo (v, _) = v

prodZeroLFrom :: Void -> (Void, a)
prodZeroLFrom = absurd

-- | Left zero of conjunction as a true isomorphism: (Void, a) ≃ Void.
prodZeroLIso :: forall a. Iso (Void, a) Void
prodZeroLIso = go prodZeroLTo prodZeroLFrom
  where
    go :: foreach (t :: (Void, a) -> Void) -> foreach (f :: Void -> (Void, a))
       -> Iso (Void, a) Void
    go t f = MkIso t f lr rl
      where
        lr :: foreach (p :: (Void, a)) -> f (t p) :~: p
        lr (v, _) = case v of {}
        rl :: foreach (v :: Void) -> t (f v) :~: v
        rl v = case v of {}

-- | Left zero of conjunction: (Void, a) ⇔ Void.
prodZeroL :: Iff (Void, a) Void
prodZeroL = embedImpliesIff (isoImpliesEmbed prodZeroLIso)

{-# LINE 300 "content/part1/Connectives.md" #-}
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
sumComm = embedImpliesIff (isoImpliesEmbed sumCommIso)

-- | Forward map for disjunction associativity.
sumAssocTo :: Either (Either a b) c -> Either a (Either b c)
sumAssocTo (Left (Left x))  = Left x
sumAssocTo (Left (Right y)) = Right (Left y)
sumAssocTo (Right z)        = Right (Right z)

-- | Backward map for disjunction associativity.
sumAssocFrom :: Either a (Either b c) -> Either (Either a b) c
sumAssocFrom (Left x)          = Left (Left x)
sumAssocFrom (Right (Left y))  = Left (Right y)
sumAssocFrom (Right (Right z)) = Right z

sumAssocLR :: foreach (s :: Either (Either a b) c) -> sumAssocFrom (sumAssocTo s) :~: s
sumAssocLR (Left (Left _))  = Refl
sumAssocLR (Left (Right _)) = Refl
sumAssocLR (Right _)        = Refl

sumAssocRL :: foreach (s :: Either a (Either b c)) -> sumAssocTo (sumAssocFrom s) :~: s
sumAssocRL (Left _)          = Refl
sumAssocRL (Right (Left _))  = Refl
sumAssocRL (Right (Right _)) = Refl

-- | Associativity of disjunction as a true isomorphism: Either (Either a b) c ≃ Either a (Either b c).
sumAssocIso :: Iso (Either (Either a b) c) (Either a (Either b c))
sumAssocIso = MkIso sumAssocTo sumAssocFrom sumAssocLR sumAssocRL

-- | Associativity of disjunction: Either (Either a b) c ⇔ Either a (Either b c).
sumAssoc :: Iff (Either (Either a b) c) (Either a (Either b c))
sumAssoc = embedImpliesIff (isoImpliesEmbed sumAssocIso)

-- | Right identity of disjunction as a true isomorphism: Either a Void ≃ a.
sumZeroRTo :: Either a Void -> a
sumZeroRTo (Left x)  = x
sumZeroRTo (Right v) = case v of {}

sumZeroRLR :: foreach (s :: Either a Void) -> Left (sumZeroRTo s) :~: s
sumZeroRLR (Left _)  = Refl
sumZeroRLR (Right v) = case v of {}

sumZeroRRL :: foreach (x :: a) -> sumZeroRTo (Left x) :~: x
sumZeroRRL _ = Refl

sumZeroRIso :: Iso (Either a Void) a
sumZeroRIso = MkIso sumZeroRTo Left sumZeroRLR sumZeroRRL

-- | Right identity of disjunction: Either a Void ⇔ a.
sumZeroR :: Iff (Either a Void) a
sumZeroR = embedImpliesIff (isoImpliesEmbed sumZeroRIso)

-- | Left identity of disjunction as a true isomorphism: Either Void a ≃ a.
sumZeroLTo :: Either Void a -> a
sumZeroLTo (Left v)  = case v of {}
sumZeroLTo (Right x) = x

sumZeroLLR :: foreach (s :: Either Void a) -> Right (sumZeroLTo s) :~: s
sumZeroLLR (Left v)  = case v of {}
sumZeroLLR (Right _) = Refl

sumZeroLRL :: foreach (x :: a) -> sumZeroLTo (Right x) :~: x
sumZeroLRL _ = Refl

sumZeroLIso :: Iso (Either Void a) a
sumZeroLIso = MkIso sumZeroLTo Right sumZeroLLR sumZeroLRL

-- | Left identity of disjunction: Either Void a ⇔ a.
sumZeroL :: Iff (Either Void a) a
sumZeroL = embedImpliesIff (isoImpliesEmbed sumZeroLIso)

{-# LINE 394 "content/part1/Connectives.md" #-}
-- | Forward and backward maps for right distributivity.
prodDistribSumTo :: (Either a b, c) -> Either (a, c) (b, c)
prodDistribSumTo (Left x, z)  = Left (x, z)
prodDistribSumTo (Right y, z) = Right (y, z)

prodDistribSumFrom :: Either (a, c) (b, c) -> (Either a b, c)
prodDistribSumFrom (Left (x, z))  = (Left x, z)
prodDistribSumFrom (Right (y, z)) = (Right y, z)

prodDistribSumLR :: foreach (p :: (Either a b, c)) -> prodDistribSumFrom (prodDistribSumTo p) :~: p
prodDistribSumLR (Left _, _)  = Refl
prodDistribSumLR (Right _, _) = Refl

prodDistribSumRL :: foreach (s :: Either (a, c) (b, c)) -> prodDistribSumTo (prodDistribSumFrom s) :~: s
prodDistribSumRL (Left (_, _))  = Refl
prodDistribSumRL (Right (_, _)) = Refl

-- | Right distributivity as a true isomorphism: (Either a b, c) ≃ Either (a, c) (b, c).
prodDistribSumIso :: Iso (Either a b, c) (Either (a, c) (b, c))
prodDistribSumIso = MkIso prodDistribSumTo prodDistribSumFrom prodDistribSumLR prodDistribSumRL

-- | Right distributivity: (Either a b, c) ⇔ Either (a, c) (b, c).
prodDistribSum :: Iff (Either a b, c) (Either (a, c) (b, c))
prodDistribSum = embedImpliesIff (isoImpliesEmbed prodDistribSumIso)

-- | Forward and backward maps for left distributivity.
prodDistribSumLTo :: (a, Either b c) -> Either (a, b) (a, c)
prodDistribSumLTo (x, Left y)  = Left (x, y)
prodDistribSumLTo (x, Right z) = Right (x, z)

prodDistribSumLFrom :: Either (a, b) (a, c) -> (a, Either b c)
prodDistribSumLFrom (Left (x, y))  = (x, Left y)
prodDistribSumLFrom (Right (x, z)) = (x, Right z)

prodDistribSumLLR :: foreach (p :: (a, Either b c)) -> prodDistribSumLFrom (prodDistribSumLTo p) :~: p
prodDistribSumLLR (_, Left _)  = Refl
prodDistribSumLLR (_, Right _) = Refl

prodDistribSumLRL :: foreach (s :: Either (a, b) (a, c)) -> prodDistribSumLTo (prodDistribSumLFrom s) :~: s
prodDistribSumLRL (Left (_, _))  = Refl
prodDistribSumLRL (Right (_, _)) = Refl

-- | Left distributivity as a true isomorphism: (a, Either b c) ≃ Either (a, b) (a, c).
prodDistribSumLIso :: Iso (a, Either b c) (Either (a, b) (a, c))
prodDistribSumLIso = MkIso prodDistribSumLTo prodDistribSumLFrom prodDistribSumLLR prodDistribSumLRL

-- | Left distributivity: (a, Either b c) ⇔ Either (a, b) (a, c).
prodDistribSumL :: Iff (a, Either b c) (Either (a, b) (a, c))
prodDistribSumL = embedImpliesIff (isoImpliesEmbed prodDistribSumLIso)

{-# LINE 465 "content/part1/Connectives.md" #-}
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

{-# LINE 499 "content/part1/Connectives.md" #-}
-- | Congruence of conjunction under `Iff`.
prodCong :: Iff a a' -> Iff b b' -> Iff (a, b) (a', b')
prodCong (Iff fa ga) (Iff fb gb) = Iff (\(x, y) -> (fa x, fb y)) (\(x, y) -> (ga x, gb y))

-- | Congruence of disjunction under `Iff`.
sumCong :: Iff a a' -> Iff b b' -> Iff (Either a b) (Either a' b')
sumCong (Iff fa ga) (Iff fb gb) = Iff (either (Left . fa) (Right . fb)) (either (Left . ga) (Right . gb))

-- | Congruence of implication under `Iff` (contravariant in the domain).
arrCong :: Iff a a' -> Iff b b' -> Iff (a -> b) (a' -> b')
arrCong (Iff fa ga) (Iff fb gb) = Iff (\h -> fb . h . ga) (\h -> gb . h . fa)

{-# LINE 521 "content/part1/Connectives.md" #-}
-- | Uniqueness (`η`) for products: every pair equals `(fst p, snd p)`.
etaProd :: foreach (p :: (a, b)) -> '(fst p, snd p) :~: p
etaProd (_, _) = Refl

-- | Uniqueness (`η`) for unit: every value of `()` equals `()`.
etaUnit :: foreach (u :: ()) -> '() :~: u
etaUnit () = Refl

-- | Sum eliminator specialized to `Left`/`Right`.
elimSum :: Either a b -> Either a b
elimSum (Left  x) = Left x
elimSum (Right y) = Right y

-- | Uniqueness (`η`) for sums: rebuilding a sum from `Left` and `Right` is the identity.
etaSum :: foreach (e :: Either a b) -> elimSum e :~: e
etaSum (Left  _) = Refl
etaSum (Right _) = Refl

-- | Uniqueness (`η`) for functions: pointwise reflexivity of function application.
etaArr :: foreach (f :: a -> b) -> foreach (x :: a) -> f x :~: f x
etaArr _ _ = Refl

-- | Embedding of disjunction over conjunction (`⊎-distrib-×`).
sumDistribProdTo :: Either (a, b) c -> (Either a c, Either b c)
sumDistribProdTo (Left (x, y)) = (Left x, Left y)
sumDistribProdTo (Right z)     = (Right z, Right z)

sumDistribProdLeft :: a -> Either b c -> Either (a, b) c
sumDistribProdLeft x (Left y)  = Left (x, y)
sumDistribProdLeft _ (Right z) = Right z

sumDistribProdStep :: Either a c -> Either b c -> Either (a, b) c
sumDistribProdStep (Left x)  r = sumDistribProdLeft x r
sumDistribProdStep (Right z) _ = Right z

sumDistribProdFrom :: (Either a c, Either b c) -> Either (a, b) c
sumDistribProdFrom (l, r) = sumDistribProdStep l r

sumDistribProdRT :: foreach (e :: Either (a, b) c)
                 -> sumDistribProdFrom (sumDistribProdTo e) :~: e
sumDistribProdRT (Left (_, _)) = Refl
sumDistribProdRT (Right _)     = Refl

sumDistribProd :: Embed (Either (a, b) c) (Either a c, Either b c)
sumDistribProd = MkEmbed sumDistribProdTo sumDistribProdFrom sumDistribProdRT
