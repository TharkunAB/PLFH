-- Generated from content/part1/Naturals.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
{-# LINE 12 "content/part1/Naturals.md" #-}
module PLFH.Part1.Naturals
  ( Size (..)
  , plus
  , times
  , monus
  , pow
  , Bin (..)
  , inc
  , toBin
  , fromBin
  , twoPlusThree
  , twoPlusThreeRefl
  ) where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Size (Size (..), plus)

{-# LINE 114 "content/part1/Naturals.md" #-}
-- | Evidence that 2 + 3 = 5 using ordinary Haskell `plus`.
twoPlusThree :: plus ('Succ ('Succ 'Zero)) ('Succ ('Succ ('Succ 'Zero)))
            :~: 'Succ ('Succ ('Succ ('Succ ('Succ 'Zero))))
twoPlusThree = Refl

-- | Compact synonym showing reflexivity directly.
twoPlusThreeRefl :: plus ('Succ ('Succ 'Zero)) ('Succ ('Succ ('Succ 'Zero)))
                :~: 'Succ ('Succ ('Succ ('Succ ('Succ 'Zero))))
twoPlusThreeRefl = Refl

{-# LINE 155 "content/part1/Naturals.md" #-}
-- | Multiply two sizes by recursion on the first argument.
times :: Size -> Size -> Size
times Zero     n = Zero
times (Succ m) n = plus n (times m n)

{-# LINE 188 "content/part1/Naturals.md" #-}
-- | Exponentiation by recursion on the second argument.
pow :: Size -> Size -> Size
pow m Zero     = Succ Zero
pow m (Succ n) = times m (pow m n)

{-# LINE 210 "content/part1/Naturals.md" #-}
-- | Truncated subtraction (monus), matching PLFA's exact clause order.
monus :: Size -> Size -> Size
monus m        Zero     = m
monus Zero     (Succ n) = Zero
monus (Succ m) (Succ n) = monus m n

{-# LINE 234 "content/part1/Naturals.md" #-}
-- | Least-significant-bit-first binary natural numbers.
data Bin
  = Nil
  | X0 Bin
  | X1 Bin
  deriving (Show)

-- | Increment a binary bitstring by one.
inc :: Bin -> Bin
inc Nil    = X1 Nil
inc (X0 b) = X1 b
inc (X1 b) = X0 (inc b)

-- | Convert unary `Size` to `Bin`.
toBin :: Size -> Bin
toBin Zero     = X0 Nil
toBin (Succ n) = inc (toBin n)

-- | Convert `Bin` back to unary `Size`.
fromBin :: Bin -> Size
fromBin Nil    = Zero
fromBin (X0 b) = plus (fromBin b) (fromBin b)
fromBin (X1 b) = Succ (plus (fromBin b) (fromBin b))
