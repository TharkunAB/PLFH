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
  , Sigma (..)
  , SizeWitness
  , mkSizeWitness
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void)
import GHC.Sigma (Sigma (Pair))
import HaskLib.Size (Size (..), congSucc, plus)
import PLFH.Part1.Relations (LE (..), invSleS)

{-# LINE 42 "content/part1/Decidable.md" #-}
-- | Logical negation: evidence that a proposition implies falsehood (Void).
type Not a = a -> Void

-- | Zero is never equal to any successor.
zeroNeqSucc :: Not ('Zero :~: 'Succ n)
zeroNeqSucc eq = case eq of {}

{-# LINE 66 "content/part1/Decidable.md" #-}
-- | Evidence that a proposition `p` is decidable.
data Dec (p :: Type) where
  Yes :: p     -> Dec p
  No  :: Not p -> Dec p

{-# LINE 78 "content/part1/Decidable.md" #-}
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

{-# LINE 95 "content/part1/Decidable.md" #-}
-- | Decidable less-than-or-equal relation on Size.
decLeSize :: foreach (m :: Size) -> foreach (n :: Size) -> Dec (LE m n)
decLeSize Zero _ = Yes ZleN
decLeSize (Succ m) n = case n of
  Zero    -> No (\case {})
  Succ n' -> case decLeSize m n' of
    Yes p  -> Yes (SleS p)
    No np  -> No (\p -> np (invSleS p))

{-# LINE 112 "content/part1/Decidable.md" #-}
-- | A dependent pair carrying a runtime size `k` and evidence that Zero <= k.
type SizeWitness = some (k :: Size) | LE 'Zero k

-- | Package any runtime size with its proof of Zero <= k.
mkSizeWitness :: Size -> SizeWitness
mkSizeWitness k = Pair k ZleN
