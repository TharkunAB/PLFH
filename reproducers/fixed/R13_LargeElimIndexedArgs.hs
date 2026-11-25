{-# LANGUAGE DependentTypes, ListTuplePuns #-}
-- | Minimal reproducer (Serokell R06 / R13 Large Elimination follow-up to
-- `fixed/R13_LargeElimTermToType.hs`; GHC Proposals #378, #281, #509):
-- Wave 3+4A (`ae37d20205`) fixed vanilla `Val -> Type` large eliminations
-- (`fixed/R13_LargeElimTermToType.hs`), but `PLFH.Part3.Adequacy.LogVLam`
-- has kind `forall (n :: Nat). Value -> Env n -> UTerm (Succ n) -> Type`,
-- carrying a `Nat`-kinded `forall` binder and GADT-indexed arguments (`Env n`,
-- `UTerm (Succ n)`) — or an existential GADT `Clos`.
--
-- Root cause (`GHC.Tc.Gen.SourceTable`): `checkedDomains` / `ordinary_binder`
-- requires all `forall` binders to have kind `Type` (`tcIsLiftedTypeKind`),
-- and `ordinaryDataType` rejects indexed/existential GADTs as carried arguments,
-- failing below with `GHC-68947` ("No checked equations are available for
-- `logVLam' in a type").
module R13_LargeElimIndexedArgs (Val (..), Box (..), logVLam, botProof) where

import Data.Kind (Type)
import HaskLib.Nat (Nat (..))

data Val = Bot | Join Val Val

data Box (n :: Nat) where
  MkBox :: Box n

logVLam :: forall (n :: Nat). Val -> Box n -> Type
logVLam Bot        b = type ()
logVLam (Join u v) b = type (logVLam u b, logVLam v b)

botProof :: logVLam Bot (MkBox @Zero)
botProof = ()
