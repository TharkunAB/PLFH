{-# LANGUAGE DataKinds, ExperimentalDependentTypes #-}
-- | Shared ordinary Haskell definitions imported by minimal R13/R16
-- reproducers so each reproducer isolates the open-equation failure
-- across a compiled module interface (avoiding same-module confounding).
module ReproOps
  ( timesWild
  , timesNamed
  , monus
  , pow
  , eqSize
  , app
  , rev
  , foldrL
  , Term (..)
  , substTerm
  ) where

import HaskLib.Nat (Nat (..), plus)

timesWild :: Nat -> Nat -> Nat
timesWild Zero     _ = Zero
timesWild (Succ m) n = plus n (timesWild m n)

timesNamed :: Nat -> Nat -> Nat
timesNamed Zero     n = Zero
timesNamed (Succ m) n = plus n (timesNamed m n)

monus :: Nat -> Nat -> Nat
monus m        Zero     = m
monus Zero     (Succ n) = Zero
monus (Succ m) (Succ n) = monus m n

pow :: Nat -> Nat -> Nat
pow m Zero     = Succ Zero
pow m (Succ n) = timesNamed m (pow m n)

eqSize :: Nat -> Nat -> Bool
eqSize Zero     Zero     = True
eqSize Zero     (Succ _) = False
eqSize (Succ _) Zero     = False
eqSize (Succ m) (Succ n) = eqSize m n

app :: [a] -> [a] -> [a]
app []       ys = ys
app (x : xs) ys = x : app xs ys

rev :: [a] -> [a]
rev []       = []
rev (x : xs) = app (rev xs) [x]

foldrL :: (a -> b -> b) -> b -> [a] -> b
foldrL f z []       = z
foldrL f z (x : xs) = f x (foldrL f z xs)

data Term
  = Var Nat
  | Lam Nat Term
  | App Term Term
  | TZero
  | TSuc Term

substTerm :: Term -> Nat -> Term -> Term
substTerm (Var x) y v = case eqSize x y of
  True  -> v
  False -> Var x
substTerm (Lam x n) y v = case eqSize x y of
  True  -> Lam x n
  False -> Lam x (substTerm n y v)
substTerm (App l m) y v = App (substTerm l y v) (substTerm m y v)
substTerm TZero _ _ = TZero
substTerm (TSuc m) y v = TSuc (substTerm m y v)
