{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, ScopedTypeVariables, StandaloneKindSignatures #-}
-- | Minimal reproducer (Serokell R03):
-- While `foreach (m :: Term 'CEmpty a) -> IsVal m` passes on a GADT whose
-- constructors refine a return index (see `reproducers/fixed/R03_ForEachGadtCase.hs`
-- and `reproducers/fixed/R03_ForEachGadtEquations.hs`), the non-uniform nested
-- datatype `UTerm (n :: Nat)` (where every constructor returns uniform `UTerm n`
-- and `ULam :: UTerm ('Succ n) -> UTerm n` shifts the parameter) fails BOTH:
--   1. `case m of` (`parReflCase`): GHC-83865 ("Couldn't match type 'ULam b' with 'm'")
--   2. Direct equations (`parReflEq`): GHC-83605 ("A retained constructor match
--      requires unguarded equations...").
-- Blocks `PLFH.Part2.Confluence.parRefl` and `betaToPar`!
module R03_NestedDatatypeForEach where

import Data.Kind (Type)

data Nat = Zero | Succ Nat

type Fin :: Nat -> Type
data Fin n where
  FZ :: Fin ('Succ n)
  FS :: Fin n -> Fin ('Succ n)

type UTerm :: Nat -> Type
data UTerm n where
  UVar :: Fin n -> UTerm n
  ULam :: UTerm ('Succ n) -> UTerm n
  UApp :: UTerm n -> UTerm n -> UTerm n

type Par :: forall (n :: Nat). UTerm n -> UTerm n -> Type
data Par t t' where
  PVar :: Par ('UVar x) ('UVar x)
  PLam :: Par b b' -> Par ('ULam b) ('ULam b')
  PApp :: Par l l' -> Par m m' -> Par ('UApp l m) ('UApp l' m')

-- Fails with GHC-83865 (no refinement `m ~ UVar x` / `m ~ ULam b` / `m ~ UApp l r`):
parReflCase :: forall (n :: Nat). foreach (m :: UTerm n) -> Par m m
parReflCase m = case m of
  UVar _   -> PVar
  ULam b   -> PLam (parReflCase b)
  UApp l r -> PApp (parReflCase l) (parReflCase r)

-- Also fails with GHC-83605:
parReflEq :: forall (n :: Nat). foreach (m :: UTerm n) -> Par m m
parReflEq (UVar _)   = PVar
parReflEq (ULam b)   = PLam (parReflEq b)
parReflEq (UApp l r) = PApp (parReflEq l) (parReflEq r)
