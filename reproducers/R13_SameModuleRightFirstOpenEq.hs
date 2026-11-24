{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (Serokell R13/R16):
-- Right-argument `pow` and two-column `monus` BOTH have checked open equations
-- when imported cross-module (see `reproducers/fixed/R13_PowOpenEq.hs` and
-- `reproducers/fixed/R13_MonusOpenEq.hs`), yet using EITHER `pow` or `monus`
-- in a type in the SAME module where they are defined fails with GHC-68947
-- ("No checked equations are available for `pow' / `monus' in a type").
-- Meanwhile left-first `times` DOES check in the same module (`twoTimesThree`).
-- Blocks PLFA `Naturals` examples `threePowFour`, `threeMonusTwo`, and
-- `twoMonusThree` inside `PLFH.Part1.Naturals`.
module R13_SameModuleRightFirstOpenEq where

import Data.Type.Equality ((:~:) (Refl))

data Nat = Zero | Succ Nat

plus :: Nat -> Nat -> Nat
plus Zero     n = n
plus (Succ m) n = Succ (plus m n)

times :: Nat -> Nat -> Nat
times Zero     n = Zero
times (Succ m) n = plus n (times m n)

-- Control: left-first `times` WORKS in the same module!
twoTimesTwo :: times (Succ (Succ Zero)) (Succ (Succ Zero)) :~: Succ (Succ (Succ (Succ Zero)))
twoTimesTwo = Refl

pow :: Nat -> Nat -> Nat
pow m Zero     = Succ Zero
pow m (Succ n) = times m (pow m n)

-- FAILS with GHC-68947 in its defining module (passes cross-module!):
twoPowTwo :: pow (Succ (Succ Zero)) (Succ (Succ Zero)) :~: Succ (Succ (Succ (Succ Zero)))
twoPowTwo = Refl

monus :: Nat -> Nat -> Nat
monus m        Zero     = m
monus Zero     (Succ n) = Zero
monus (Succ m) (Succ n) = monus m n

-- ALSO FAILS with GHC-68947 in its defining module (passes cross-module!):
threeMonusTwo :: monus (Succ (Succ (Succ Zero))) (Succ (Succ Zero)) :~: Succ Zero
threeMonusTwo = Refl
