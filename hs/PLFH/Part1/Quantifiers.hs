-- Generated from content/part1/Quantifiers.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DependentTypes, LambdaCase, ListTuplePuns, UndecidableInstances #-}
{-# LINE 41 "content/part1/Quantifiers.md" #-}
module PLFH.Part1.Quantifiers
  ( Exists
  , SumPred (..)
  , existsDistribSum
  , existsCurryTo
  , existsCurryFrom
  , Forall (..)
  , ProdPred (..)
  , forallDistribProd
  , notExistsToForallNot
  , forallNotToNotExists
  , NotPred (..)
  , existsNotImpliesForallNot
  , DPair (..)
  , sigmaDistribSumTo
  , sigmaDistribSumFrom
  , sigmaDistribSum
  , EvenSigma
  , evenZeroSigma
  , evenTwoSigma
  , SumSigma
  , sumSigmaTwo
  , CanBin
  , oneIrr
  , canIrr
  , toCanBin
  , fromCanBin
  , canBinEq
  , binIff
  , EvenWitness (..)
  , evenWitnessZero
  , evenWitnessSuc2
  , evenDouble
  , evenToWitness
  , witnessToEven
  , evenIffWitness
  , OddWitness (..)
  , oddToWitness
  , witnessToOdd
  , oddIffWitness
  ) where

import Data.Exists.Dependent (data Pack, mapExists, withExists)
import Data.Kind (Type)
import Data.Nat.Dependent (Nat (..), plus)
import Data.Nat.Dependent.Properties (plusSucc)
import Data.Type.Equality ((:~:) (Refl))
import Data.Type.Equality.Dependent (rewrite)
import GHC.Exists (Exists)
import GHC.Sigma (Sigma (Pair))
import PLFH.Part1.Induction (cong, fromTo)
import PLFH.Part1.Isomorphism (Iff (..), Iso (..))
import PLFH.Part1.Naturals (Bin (..), fromBin, toBin)
import PLFH.Part1.Negation (Not)
import PLFH.Part1.Relations (Can (..), Even (..), Odd (..), One (..), toBinCan, toFromCan)

{-# LINE 149 "content/part1/Quantifiers.md" #-}
-- | Pointwise disjunction of predicates.
data SumPred (p :: a -> Type) (q :: a -> Type) (x :: a) where
  InL :: p x -> SumPred p q x
  InR :: q x -> SumPred p q x

-- | Existentials distribute over disjunction (`∃-distrib-⊎`):
-- (∃ x. P x ∨ Q x) ⇔ (∃ x. P x) ∨ (∃ x. Q x).
existsDistribSum
  :: forall a (p :: a -> Type) (q :: a -> Type).
     Iff (Exists (SumPred p q)) (Either (Exists p) (Exists q))
existsDistribSum = Iff toF fromF
  where
    packP :: forall (x :: a). p x -> Exists p
    packP px = Pack (type x) px

    packQ :: forall (x :: a). q x -> Exists q
    packQ qx = Pack (type x) qx

    toF :: Exists (SumPred p q) -> Either (Exists p) (Exists q)
    toF pkg = case pkg of
      Pack (type _) s -> case s of
        InL px -> Left (packP px)
        InR qx -> Right (packQ qx)

    fromF :: Either (Exists p) (Exists q) -> Exists (SumPred p q)
    fromF (Left pkg)  = mapExists (\_ px -> InL px) pkg
    fromF (Right pkg) = mapExists (\_ qx -> InR qx) pkg

-- | Currying for existentials (`∀∃-currying`): ((∃ x. P x) -> C) ⇔ (∀ x. P x -> C).
existsCurryTo
  :: forall a (p :: a -> Type) c.
     (Exists p -> c) -> (forall x. p x -> c)
existsCurryTo f (px :: p x) = f (Pack (type x) px)

existsCurryFrom
  :: forall a (p :: a -> Type) c.
     (forall x. p x -> c) -> (Exists p -> c)
existsCurryFrom g pkg = withExists pkg $ \_ px -> g px

-- | First-class wrapper for universal quantification and pointwise conjunction.
newtype Forall (p :: a -> Type) = MkForall { unForall :: forall x. p x }
newtype ProdPred (p :: a -> Type) (q :: a -> Type) (x :: a) =
  MkProdPred { unProdPred :: (p x, q x) }

-- | Universals distribute over conjunction (`∀-distrib-×`):
-- (∀ x. P x ∧ Q x) ⇔ (∀ x. P x) ∧ (∀ x. Q x).
forallDistribProd :: Iff (Forall (ProdPred p q)) (Forall p, Forall q)
forallDistribProd =
  Iff (\f -> ( MkForall (fst (unProdPred (unForall f)))
             , MkForall (snd (unProdPred (unForall f))) ))
      (\(fp, fq) -> MkForall (MkProdPred (unForall fp, unForall fq)))

-- | De Morgan for quantifiers: ¬(∃ x. P x) ⇔ ∀ x. ¬(P x).
notExistsToForallNot
  :: forall a (p :: a -> Type).
     Not (Exists p) -> (forall x. Not (p x))
notExistsToForallNot ne (px :: p x) = ne (Pack (type x) px)

forallNotToNotExists
  :: forall a (p :: a -> Type).
     (forall x. Not (p x)) -> Not (Exists p)
forallNotToNotExists fn pkg = withExists pkg $ \_ px -> fn px

-- | Pointwise negation predicate wrapper for `Exists`.
newtype NotPred (p :: a -> Type) (x :: a) = MkNotPred { unNotPred :: Not (p x) }

-- | Constructive quantifier implication: (∃ x. ¬(P x)) -> ¬(∀ x. P x) (`∃¬-implies-¬∀`).
existsNotImpliesForallNot
  :: forall a (p :: a -> Type).
     Exists (NotPred p) -> Not (Forall p)
existsNotImpliesForallNot pkg (MkForall allP) =
  withExists pkg $ \(type x) (MkNotPred npx) -> npx (allP @x)

{-# LINE 227 "content/part1/Quantifiers.md" #-}
-- | Reusable retained dependent pair over a matchable predicate `p :: a -> Type`.
data DPair (a :: Type) (p :: a -> Type) where
  MkDPair :: foreach (x :: a) -> p x -> DPair a p

-- | Distributivity of retained dependent pairs over disjunction (`∃-distrib-⊎`).
sigmaDistribSumTo
  :: forall a (p :: a -> Type) (q :: a -> Type).
     DPair a (SumPred p q) -> Either (DPair a p) (DPair a q)
sigmaDistribSumTo (MkDPair x (InL px)) = Left  (MkDPair x px)
sigmaDistribSumTo (MkDPair x (InR qx)) = Right (MkDPair x qx)

sigmaDistribSumFrom
  :: forall a (p :: a -> Type) (q :: a -> Type).
     Either (DPair a p) (DPair a q) -> DPair a (SumPred p q)
sigmaDistribSumFrom (Left  (MkDPair x px)) = MkDPair x (InL px)
sigmaDistribSumFrom (Right (MkDPair x qx)) = MkDPair x (InR qx)

sigmaDistribSum
  :: forall a (p :: a -> Type) (q :: a -> Type).
     Iff (DPair a (SumPred p q)) (Either (DPair a p) (DPair a q))
sigmaDistribSum = Iff sigmaDistribSumTo sigmaDistribSumFrom

{-# LINE 267 "content/part1/Quantifiers.md" #-}
-- | Retained dependent sum: there exists a runtime `k` with `k + k = n`.
type EvenSigma (n :: Nat) = some (k :: Nat) | plus k k :~: n

evenZeroSigma :: EvenSigma 0
evenZeroSigma = Pair Zero Refl

evenTwoSigma :: EvenSigma 2
evenTwoSigma = Pair 1 Refl

-- | Multi-binder retained sum: there exist runtime `m` and `k` with `m + k = n`.
type SumSigma (n :: Nat) = some (m k :: Nat) | plus m k :~: n

sumSigmaTwo :: SumSigma 2
sumSigmaTwo = Pair 1 (Pair 1 Refl)

{-# LINE 294 "content/part1/Quantifiers.md" #-}
-- | Canonical binary numeral: a `Bin` paired with its `Can` proof.
type CanBin = some (b :: Bin) | Can b

-- | Proof irrelevance for `One`: any two derivations of `One b` are equal.
oneIrr :: forall (b :: Bin). foreach (o1 o2 :: One b) -> o1 :~: o2
oneIrr OneX1       o2 = case o2 of { OneX1     -> Refl }
oneIrr (OneX0  p1) o2 = case o2 of { OneX0  p2 -> case oneIrr p1 p2 of Refl -> Refl }
oneIrr (OneX1' p1) o2 = case o2 of { OneX1' p2 -> case oneIrr p1 p2 of Refl -> Refl }

-- | Proof irrelevance for `Can`: any two derivations of `Can b` are equal.
canIrr :: forall (b :: Bin). foreach (c1 c2 :: Can b) -> c1 :~: c2
canIrr CanZ        c2 = case c2 of { CanZ      -> Refl }
canIrr (CanOne p1) c2 = case c2 of { CanOne p2 -> case oneIrr p1 p2 of Refl -> Refl }

toCanBin :: Nat -> CanBin
toCanBin n = Pair (toBin n) (toBinCan n)

fromCanBin :: CanBin -> Nat
fromCanBin (Pair b _) = fromBin b

-- | Two `CanBin` pairs with equal underlying `Bin` numerals are equal (by proof irrelevance of `Can`).
canBinEq :: forall (b1 b2 :: Bin). foreach (c1 :: Can b1) -> foreach (c2 :: Can b2)
         -> b1 :~: b2 -> (Pair b1 c1 :: CanBin) :~: Pair b2 c2
canBinEq c1 c2 Refl = case canIrr c1 c2 of Refl -> Refl

-- | Bijection between `Nat` and canonical binary numerals (`Bin-isomorphism` via `fromTo`, `toFromCan`, and `canBinEq`).
binIff :: Iff Nat CanBin
binIff = Iff toCanBin fromCanBin

{-# LINE 330 "content/part1/Quantifiers.md" #-}
-- | Retained existential witness that `n` is double some runtime `k`.
data EvenWitness (n :: Nat) where
  MkEvenWitness :: foreach (k :: Nat) -> plus k k :~: n -> EvenWitness n

evenWitnessZero :: EvenWitness Zero
evenWitnessZero = MkEvenWitness Zero Refl

evenWitnessSuc2 :: EvenWitness n -> EvenWitness (Succ (Succ n))
evenWitnessSuc2 (MkEvenWitness k Refl) =
  MkEvenWitness (Succ k) (cong Succ (plusSucc k k))

-- | Every double `k + k` is even (proved directly using `rewrite`).
evenDouble :: foreach (k :: Nat) -> Even (plus k k)
evenDouble Zero     = EvenZ
evenDouble (Succ k) = rewrite (plusSucc k k) (EvenS (OddS (evenDouble k)))

-- | Every inductive `Even n` derivation yields a runtime half `k` with `k + k = n`.
evenToWitness :: Even n -> EvenWitness n
evenToWitness EvenZ              = evenWitnessZero
evenToWitness (EvenS (OddS evn)) = evenWitnessSuc2 (evenToWitness evn)

-- | Converse: a runtime witness `k + k = n` reconstructs `Even n`.
witnessToEven :: EvenWitness n -> Even n
witnessToEven (MkEvenWitness k Refl) = evenDouble k

-- | Full bi-implication: `Even n ⇔ (∃ k. k + k = n)`.
evenIffWitness :: Iff (Even n) (EvenWitness n)
evenIffWitness = Iff evenToWitness witnessToEven

-- | Retained existential witness that `n = Succ (k + k)` for some runtime `k`.
data OddWitness (n :: Nat) where
  MkOddWitness :: foreach (k :: Nat) -> Succ (plus k k) :~: n -> OddWitness n

oddToWitness :: Odd n -> OddWitness n
oddToWitness (OddS ev) = case evenToWitness ev of
  MkEvenWitness k Refl -> MkOddWitness k Refl

witnessToOdd :: OddWitness n -> Odd n
witnessToOdd (MkOddWitness k Refl) = OddS (evenDouble k)

-- | Full bi-implication: `Odd n ⇔ (∃ k. Succ (k + k) = n)`.
oddIffWitness :: Iff (Odd n) (OddWitness n)
oddIffWitness = Iff oddToWitness witnessToOdd
