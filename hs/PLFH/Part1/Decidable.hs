-- Generated from content/part1/Decidable.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs, TypeOperators #-}
{-# LINE 12 "content/part1/Decidable.md" #-}
module PLFH.Part1.Decidable
  ( Not
  , Dec (..)
  , zeroNeqSucc
  , decEqSize
  , decLeSize
  , decEven
  , decOdd
  , Reflects (..)
  , reflectsToDec
  , Sigma (..)
  , SizeWitness
  , mkSizeWitness
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void)
import GHC.Sigma (Sigma (Pair))
import HaskLib.Size (Size (..), congSucc, plus)
import PLFH.Part1.Relations (Even (..), LE (..), Odd (..), invSleS)

{-# LINE 46 "content/part1/Decidable.md" #-}
-- | Logical negation: evidence that a proposition implies falsehood (Void).
type Not a = a -> Void

-- | Zero is never equal to any successor.
zeroNeqSucc :: Not ('Zero :~: 'Succ n)
zeroNeqSucc eq = case eq of {}

{-# LINE 70 "content/part1/Decidable.md" #-}
-- | Evidence that a proposition `p` is decidable.
data Dec (p :: Type) where
  Yes :: p     -> Dec p
  No  :: Not p -> Dec p

{-# LINE 82 "content/part1/Decidable.md" #-}
-- | Decidable propositional equality on Size.
decEqSize :: foreach (m :: Size) -> foreach (n :: Size) -> Dec (m :~: n)
decEqSize Zero n = case n of
  Zero   -> Yes Refl
  Succ _ -> No (\case {})
decEqSize (Succ m) n = case n of
  Zero    -> No (\case {})
  Succ n' -> case decEqSize m n' of
    Yes eq -> Yes (congSucc eq)
    No neq -> No (\Refl -> neq Refl)

{-# LINE 99 "content/part1/Decidable.md" #-}
-- | Decidable less-than-or-equal relation on Size.
decLeSize :: foreach (m :: Size) -> foreach (n :: Size) -> Dec (LE m n)
decLeSize Zero _ = Yes ZleN
decLeSize (Succ m) n = case n of
  Zero    -> No (\case {})
  Succ n' -> case decLeSize m n' of
    Yes p  -> Yes (SleS p)
    No np  -> No (\p -> np (invSleS p))

{-# LINE 117 "content/part1/Decidable.md" #-}
-- | Decidable evenness predicate on Size.
decEven :: foreach (n :: Size) -> Dec (Even n)
decEven Zero     = Yes EvenZ
decEven (Succ n) = case n of
  Zero    -> No (\case EvenS o -> case o of {})
  Succ n' -> case decEven n' of
    Yes ev  -> Yes (EvenS (OddS ev))
    No  nev -> No (\case EvenS (OddS ev) -> nev ev)

-- | Decidable oddness predicate on Size.
decOdd :: foreach (n :: Size) -> Dec (Odd n)
decOdd Zero     = No (\case {})
decOdd (Succ n) = case n of
  Zero    -> Yes (OddS EvenZ)
  Succ n' -> case decOdd n' of
    Yes od  -> Yes (OddS (EvenS od))
    No  nod -> No (\case OddS (EvenS od) -> nod od)

-- | Boolean reflection: ties a proposition `p` to a promoted `Bool` `b`.
data Reflects (p :: Type) (b :: Bool) where
  OfTrue  :: p -> Reflects p 'True
  OfFalse :: Not p -> Reflects p 'False

-- | Reflecting a Boolean yields a decision procedure.
reflectsToDec :: foreach (b :: Bool) -> Reflects p b -> Dec p
reflectsToDec True  (OfTrue p)   = Yes p
reflectsToDec False (OfFalse np) = No np

{-# LINE 153 "content/part1/Decidable.md" #-}
-- | A dependent pair carrying a runtime size `k` and evidence that Zero <= k.
type SizeWitness = some (k :: Size) | LE 'Zero k

-- | Package any runtime size with its proof of Zero <= k.
mkSizeWitness :: Size -> SizeWitness
mkSizeWitness k = Pair k ZleN
