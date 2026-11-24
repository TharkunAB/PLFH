-- Minimal reproducer: open source equations for GADT-indexed higher-order
-- single-variable substitution (`substSingleU`) on well-scoped untyped terms.
--
-- Triggered in: PLFH.Part2.Untyped (`Beta`), PLFH.Part2.Confluence (`PBeta`),
--               PLFH.Part3.Soundness (`substSinglePres`).
-- Card: R13 / R16 (open equations for higher-order GADT-indexed functions).
--
-- Expected behavior: `substSingleU ('UVar 'FZ) w` reduces to `w`, so
-- `substId = Refl` checks.
-- Actual behavior on published GHC 1a02a866e7 (590): fails with GHC-68947
-- ("No checked equations are available for 'substSingleU' in a type").
-- (Also: omitting explicit `forall` in a GADT constructor mentioning
-- unqualified `substSingleU` silently quantifies `substSingleU` as an
-- unconstrained fresh type variable rather than reporting GHC-68947.)

{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, PolyKinds, RankNTypes, TypeOperators #-}
module R13_SubstSingleUOpenEq (substId) where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..))

data Fin (n :: Nat) where
  FZ :: Fin ('Succ n)
  FS :: Fin n -> Fin ('Succ n)

data UTerm (n :: Nat) where
  UVar :: Fin n -> UTerm n
  ULam :: UTerm ('Succ n) -> UTerm n
  UApp :: UTerm n -> UTerm n -> UTerm n

extU :: (Fin m -> Fin n) -> Fin ('Succ m) -> Fin ('Succ n)
extU _   FZ     = FZ
extU rho (FS x) = FS (rho x)

renameU :: (Fin m -> Fin n) -> UTerm m -> UTerm n
renameU rho (UVar x)   = UVar (rho x)
renameU rho (ULam b)   = ULam (renameU (extU rho) b)
renameU rho (UApp l m) = UApp (renameU rho l) (renameU rho m)

extsU :: (Fin m -> UTerm n) -> Fin ('Succ m) -> UTerm ('Succ n)
extsU _     FZ     = UVar FZ
extsU sigma (FS x) = renameU FS (sigma x)

substU :: (Fin m -> UTerm n) -> UTerm m -> UTerm n
substU sigma (UVar x)   = sigma x
substU sigma (ULam b)   = ULam (substU (extsU sigma) b)
substU sigma (UApp l m) = UApp (substU sigma l) (substU sigma m)

substSingleU :: UTerm ('Succ n) -> UTerm n -> UTerm n
substSingleU b w = substU (\case { FZ -> w; FS x -> UVar x }) b

substId :: forall (n :: Nat) (w :: UTerm n). substSingleU ('UVar 'FZ) w :~: w
substId = Refl
