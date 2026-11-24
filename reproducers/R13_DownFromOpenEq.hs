{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (R13/R16): structural recursion on `Size` producing a
-- list `[Size]` (`downFrom`, and even `zeros`) fails GHC-68947 ("No checked
-- equations are available for 'downFrom' in a type").
--
-- Blocks PLFA Part 1 Lists `downFrom` length proofs.
module R13_DownFromOpenEq (downFrom, lengthDownFrom) where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib (size)
import HaskLib.Size (Size (..))

downFrom :: Size -> [Size]
downFrom Zero     = []
downFrom (Succ n) = n : downFrom n

lengthDownFrom :: foreach (n :: Size) -> size (downFrom n) :~: n
lengthDownFrom Zero     = Refl
lengthDownFrom (Succ n) = case lengthDownFrom n of { Refl -> Refl }
