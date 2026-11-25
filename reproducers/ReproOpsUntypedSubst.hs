{-# LANGUAGE DependentTypes #-}
-- | Minimal provider for `R16_UntypedSubstOpenEq.hs` (skipped as ReproOps*).
-- Mirrors `PLFH.Part2.Untyped`'s 1-index scope-indexed `Fin n` / `UTerm n`
-- simultaneous renaming (`renameU`) and substitution (`substU`), plus
-- `substSingleU` (which already publishes a private closure family, whereas
-- `shiftFin`/`extU`/`renameU`/`extsU`/`substU` publish none because
-- `GHC.Tc.Gen.SourceClosure` hardcodes 2-index `(Ctx, Ty)` GADTs).
module ReproOpsUntypedSubst where

import HaskLib.Nat (Nat (..))

data Fin (n :: Nat) where
  FZ :: Fin (Succ n)
  FS :: Fin n -> Fin (Succ n)

data UTerm (n :: Nat) where
  UVar :: Fin n -> UTerm n
  ULam :: UTerm (Succ n) -> UTerm n
  UApp :: UTerm n -> UTerm n -> UTerm n

shiftFin :: Fin m -> Fin (Succ m)
shiftFin x = FS x

extU :: (Fin m -> Fin n) -> Fin (Succ m) -> Fin (Succ n)
extU _   FZ     = FZ
extU rho (FS x) = FS (rho x)

renameU :: (Fin m -> Fin n) -> UTerm m -> UTerm n
renameU rho (UVar x)   = UVar (rho x)
renameU rho (ULam b)   = ULam (renameU (extU rho) b)
renameU rho (UApp l m) = UApp (renameU rho l) (renameU rho m)

extsU :: (Fin m -> UTerm n) -> Fin (Succ m) -> UTerm (Succ n)
extsU _     FZ     = UVar FZ
extsU sigma (FS x) = renameU shiftFin (sigma x)

substU :: (Fin m -> UTerm n) -> UTerm m -> UTerm n
substU sigma (UVar x)   = sigma x
substU sigma (ULam b)   = ULam (substU (extsU sigma) b)
substU sigma (UApp l m) = UApp (substU sigma l) (substU sigma m)

substSingleU :: UTerm (Succ n) -> UTerm n -> UTerm n
substSingleU b w = substU (\case { FZ -> w; FS x -> UVar x }) b
