-- Generated from content/part1/Naturals.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, ExplicitNamespaces, ExperimentalDependentTypes, GADTs, TypeOperators #-}
{-# LINE 12 "content/part1/Naturals.md" #-}
module PLFH.Part1.Naturals
  ( Nat (..)
  , plus
  , type (+)
  , times
  , monus
  , pow
  , Bin (..)
  , inc
  , toBin
  , fromBin
  , twoPlusThree
  , twoPlusThreeInfix
  , fiveAtRuntime
  , twoTimesThree
  , threePowFour
  , threeMonusTwo
  , twoMonusThree
  ) where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..), plus, type (+))

{-# LINE 390 "content/part1/Naturals.md" #-}
-- | Evidence that 2 + 3 = 5 using ordinary Haskell `plus` and decimal numerals.
twoPlusThree :: plus 2 3 :~: 5
twoPlusThree = Refl

-- | The same proof using `HaskLib.Nat`'s infix type operator `(+)`.
twoPlusThreeInfix :: (2 + 3 :: Nat) :~: 5
twoPlusThreeInfix = Refl

-- | Ordinary runtime arithmetic using the same `Nat` and `Num` instance.
fiveAtRuntime :: Nat
fiveAtRuntime = 2 + 3

{-# LINE 436 "content/part1/Naturals.md" #-}
-- | Multiply two natural numbers by recursion on the first argument.
times :: Nat -> Nat -> Nat
times Zero     n = Zero
times (Succ m) n = plus n (times m n)

{-# LINE 480 "content/part1/Naturals.md" #-}
-- | Evidence that 2 * 3 = 6 using ordinary `times` and decimal numerals.
twoTimesThree :: times 2 3 :~: 6
twoTimesThree = Refl

{-# LINE 520 "content/part1/Naturals.md" #-}
-- | Exponentiation by recursion on the second argument.
pow :: Nat -> Nat -> Nat
pow m Zero     = Succ Zero
pow m (Succ n) = times m (pow m n)

{-# LINE 527 "content/part1/Naturals.md" #-}
-- | Concrete same-module exponentiation example: 3 ^ 4 = 81.
threePowFour :: pow 3 4 :~: 81
threePowFour = Refl

{-# LINE 543 "content/part1/Naturals.md" #-}
-- | Truncated subtraction (monus), matching PLFA's exact clause order.
monus :: Nat -> Nat -> Nat
monus m        Zero     = m
monus Zero     (Succ n) = Zero
monus (Succ m) (Succ n) = monus m n

{-# LINE 567 "content/part1/Naturals.md" #-}
-- | Concrete same-module truncated subtraction examples: 3 ∸ 2 = 1 and 2 ∸ 3 = 0.
threeMonusTwo :: monus 3 2 :~: 1
threeMonusTwo = Refl

twoMonusThree :: monus 2 3 :~: 0
twoMonusThree = Refl

{-# LINE 704 "content/part1/Naturals.md" #-}
-- | Least-significant-bit-first binary natural numbers.
data Bin
  = Nil
  | X0 Bin
  | X1 Bin
  deriving (Show)

{-# LINE 723 "content/part1/Naturals.md" #-}
-- | Increment a binary bitstring by one.
inc :: Bin -> Bin
inc Nil    = X1 Nil
inc (X0 b) = X1 b
inc (X1 b) = X0 (inc b)

-- | Convert unary `Nat` to `Bin`.
toBin :: Nat -> Bin
toBin Zero     = X0 Nil
toBin (Succ n) = inc (toBin n)

-- | Convert `Bin` back to unary `Nat`.
fromBin :: Bin -> Nat
fromBin Nil    = Zero
fromBin (X0 b) = plus (fromBin b) (fromBin b)
fromBin (X1 b) = Succ (plus (fromBin b) (fromBin b))
