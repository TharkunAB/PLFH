-- Generated from content/part1/Decidable.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DependentTypes, ListTuplePuns #-}
{-# LINE 31 "content/part1/Decidable.md" #-}
module PLFH.Part1.Decidable
  ( Not
  , Dec (..)
  , decNot
  , decAnd
  , decOr
  , decImp
  , decIff
  , zeroNeqSucc
  , decEqSize
  , decLeSize
  , decLtSize
  , decEven
  , decOdd
  , decEqBin
  , decOne
  , decCan
  , Reflects (..)
  , reflectsToDec
  , Sigma (..)
  , SizeWitness
  , mkSizeWitness
  , plusExists
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void, absurd)
import GHC.Sigma (Sigma (Pair))
import HaskLib.Nat (Nat (..), plus)
import PLFH.Part1.Induction (cong)
import PLFH.Part1.Isomorphism (Iff (..))
import PLFH.Part1.Naturals (Bin (..))
import PLFH.Part1.Relations (Can (..), Even (..), LE (..), LT' (..), Odd (..), One (..), invSleS)

{-# LINE 86 "content/part1/Decidable.md" #-}
-- | Logical negation: evidence that a proposition implies falsehood (Void).
type Not a = a -> Void

-- | Peano's postulate: Zero is never equal to any successor.
zeroNeqSucc :: Not (Zero :~: Succ n)
zeroNeqSucc eq = case eq of {}

{-# LINE 100 "content/part1/Decidable.md" #-}
-- | Evidence that a proposition `p` is decidable.
data Dec (p :: Type) where
  Yes :: p     -> Dec p
  No  :: Not p -> Dec p

{-# LINE 117 "content/part1/Decidable.md" #-}
-- | Decidable propositions are closed under negation, conjunction, disjunction,
-- implication, and bi-implication.
decNot :: Dec p -> Dec (Not p)
decNot (Yes p)  = No (\np -> np p)
decNot (No  np) = Yes np

decAnd :: Dec p -> Dec q -> Dec (p, q)
decAnd (Yes p) (Yes q) = Yes (p, q)
decAnd (No np) _       = No (\(p, _) -> np p)
decAnd _       (No nq) = No (\(_, q) -> nq q)

decOr :: Dec p -> Dec q -> Dec (Either p q)
decOr (Yes p) _       = Yes (Left p)
decOr _       (Yes q) = Yes (Right q)
decOr (No np) (No nq) = No (either np nq)

decImp :: Dec p -> Dec q -> Dec (p -> q)
decImp (No np) _       = Yes (\p -> absurd (np p))
decImp _       (Yes q) = Yes (const q)
decImp (Yes p) (No nq) = No (\f -> nq (f p))

decIff :: Dec p -> Dec q -> Dec (Iff p q)
decIff dp dq = case decAnd (decImp dp dq) (decImp dq dp) of
  Yes (f, g) -> Yes (Iff f g)
  No nfg     -> No (\(Iff f g) -> nfg (f, g))

{-# LINE 156 "content/part1/Decidable.md" #-}
-- | Decidable propositional equality on Nat (`_≡ℕ?_`).
decEqSize :: foreach (m n :: Nat) -> Dec (m :~: n)
decEqSize Zero     Zero     = Yes Refl
decEqSize Zero     (Succ _) = No (\case {})
decEqSize (Succ _) Zero     = No (\case {})
decEqSize (Succ m) (Succ n) = case decEqSize m n of
  Yes eq -> Yes (cong Succ eq)
  No neq -> No (\Refl -> neq Refl)

-- | Decidable less-than-or-equal relation on Nat (`_≤?_`).
decLeSize :: foreach (m n :: Nat) -> Dec (LE m n)
decLeSize Zero     _        = Yes ZleN
decLeSize (Succ _) Zero     = No (\case {})
decLeSize (Succ m) (Succ n) = case decLeSize m n of
  Yes p -> Yes (SleS p)
  No np -> No (\p -> np (invSleS p))

-- | Decidable strict less-than relation on Nat (`_<?_`).
decLtSize :: foreach (m n :: Nat) -> Dec (LT' m n)
decLtSize Zero     Zero     = No (\case {})
decLtSize Zero     (Succ _) = Yes ZltS
decLtSize (Succ _) Zero     = No (\case {})
decLtSize (Succ m) (Succ n) = case decLtSize m n of
  Yes p -> Yes (SltS p)
  No np -> No (\case SltS q -> np q)

{-# LINE 198 "content/part1/Decidable.md" #-}
-- | Decidable evenness predicate on Nat.
decEven :: foreach (n :: Nat) -> Dec (Even n)
decEven Zero            = Yes EvenZ
decEven (Succ Zero)     = No (\case EvenS o -> case o of {})
decEven (Succ (Succ n)) = case decEven n of
  Yes ev  -> Yes (EvenS (OddS ev))
  No  nev -> No (\case EvenS (OddS ev) -> nev ev)

-- | Decidable oddness predicate on Nat.
decOdd :: foreach (n :: Nat) -> Dec (Odd n)
decOdd Zero            = No (\case {})
decOdd (Succ Zero)     = Yes (OddS EvenZ)
decOdd (Succ (Succ n)) = case decOdd n of
  Yes od  -> Yes (OddS (EvenS od))
  No  nod -> No (\case OddS (EvenS od) -> nod od)

-- | Boolean reflection: ties a proposition `p` to a promoted `Bool` `b`.
data Reflects (p :: Type) (b :: Bool) where
  OfTrue  :: p -> Reflects p True
  OfFalse :: Not p -> Reflects p False

-- | Reflecting a Boolean yields a decision procedure.
reflectsToDec :: foreach (b :: Bool) -> Reflects p b -> Dec p
reflectsToDec True  (OfTrue p)   = Yes p
reflectsToDec False (OfFalse np) = No np

-- | Decidable equality on binary numbers (`Bin`).
decEqBin :: foreach (a b :: Bin) -> Dec (a :~: b)
decEqBin Nil    Nil    = Yes Refl
decEqBin Nil    (X0 _) = No (\case {})
decEqBin Nil    (X1 _) = No (\case {})
decEqBin (X0 _) Nil    = No (\case {})
decEqBin (X0 _) (X1 _) = No (\case {})
decEqBin (X0 a) (X0 b) = case decEqBin a b of
  Yes Refl -> Yes Refl
  No  neq  -> No (\Refl -> neq Refl)
decEqBin (X1 _) Nil    = No (\case {})
decEqBin (X1 _) (X0 _) = No (\case {})
decEqBin (X1 a) (X1 b) = case decEqBin a b of
  Yes Refl -> Yes Refl
  No  neq  -> No (\Refl -> neq Refl)

-- | Decidable `One` predicate (`One?`).
decOne :: foreach (b :: Bin) -> Dec (One b)
decOne Nil         = No (\case {})
decOne (X0 b)      = case decOne b of
  Yes o  -> Yes (OneX0 o)
  No  no -> No (\case OneX0 o -> no o)
decOne (X1 Nil)    = Yes OneX1
decOne (X1 (X0 b)) = case decOne (X0 b) of
  Yes o  -> Yes (OneX1' o)
  No  no -> No (\case OneX1' o -> no o)
decOne (X1 (X1 b)) = case decOne (X1 b) of
  Yes o  -> Yes (OneX1' o)
  No  no -> No (\case OneX1' o -> no o)

-- | Decidable canonical-form predicate (`Can?`).
decCan :: foreach (b :: Bin) -> Dec (Can b)
decCan Nil         = No (\case CanOne o -> case o of {})
decCan (X0 Nil)    = Yes CanZ
decCan (X0 (X0 b)) = case decOne (X0 b) of
  Yes o  -> Yes (CanOne (OneX0 o))
  No  no -> No (\case CanOne (OneX0 o) -> no o)
decCan (X0 (X1 b)) = case decOne (X1 b) of
  Yes o  -> Yes (CanOne (OneX0 o))
  No  no -> No (\case CanOne (OneX0 o) -> no o)
decCan (X1 b)      = case decOne (X1 b) of
  Yes o  -> Yes (CanOne o)
  No  no -> No (\case CanOne o -> no o)

{-# LINE 281 "content/part1/Decidable.md" #-}
-- | A dependent pair carrying a runtime size `k` and evidence that Zero <= k.
type SizeWitness = some (k :: Nat) | LE Zero k

-- | Package any runtime size with its proof of Zero <= k.
mkSizeWitness :: Nat -> SizeWitness
mkSizeWitness k = Pair k ZleN

-- | Inline retained dependent sum returned directly from a `foreach` function.
plusExists :: foreach (m n :: Nat)
           -> some (k :: Nat) | k :~: plus m n
plusExists m n = Pair (plus m n) Refl
