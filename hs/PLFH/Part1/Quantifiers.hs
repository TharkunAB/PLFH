-- Generated from content/part1/Quantifiers.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DependentTypes, ListTuplePuns, UndecidableInstances #-}
{-# LINE 37 "content/part1/Quantifiers.md" #-}
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
  , EvenSigma
  , evenZeroSigma
  , evenTwoSigma
  , SumSigma
  , sumSigmaTwo
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

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import GHC.Sigma (Sigma (Pair))
import HaskLib (rewrite)
import HaskLib.Exists (Exists, data Pack, mapExists, withExists)
import HaskLib.Nat (Nat (..), plus, plusSucc)
import PLFH.Part1.Decidable (Not)
import PLFH.Part1.Induction (cong)
import PLFH.Part1.Isomorphism (Iff (..))
import PLFH.Part1.Relations (Even (..), Odd (..))

{-# LINE 129 "content/part1/Quantifiers.md" #-}
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

{-# LINE 210 "content/part1/Quantifiers.md" #-}
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

{-# LINE 232 "content/part1/Quantifiers.md" #-}
-- | Retained existential witness that `n` is double some runtime `k`.
data EvenWitness (n :: Nat) where
  MkEvenWitness :: foreach (k :: Nat) -> plus k k :~: n -> EvenWitness n

evenWitnessZero :: EvenWitness Zero
evenWitnessZero = MkEvenWitness Zero Refl

evenWitnessSuc2 :: EvenWitness n -> EvenWitness (Succ (Succ n))
evenWitnessSuc2 (MkEvenWitness k Refl) =
  MkEvenWitness (Succ k) (cong Succ (plusSucc k k))

-- | Every double `k + k` is even (proved directly using `HaskLib.rewrite`).
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
