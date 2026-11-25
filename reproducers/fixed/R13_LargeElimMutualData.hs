{-# LANGUAGE DependentTypes, ListTuplePuns #-}
-- | Minimal reproducer (Serokell R06 / R13 Large Elimination follow-up to
-- `fixed/R13_LargeElimIndexedArgs.hs`; GHC Proposals #378, #281, #509):
-- Wave 5+6 (`91a63517fc`) fixed non-mutual term-to-`Type` large eliminations
-- with promoted `forall (n :: Nat)` binders and GADT-indexed arguments
-- (`fixed/R13_LargeElimIndexedArgs.hs`), but PLFA `Adequacy`'s logical relation
-- `logVLam` is inherently mutually recursive with its existential halting
-- witness `HaltsV` and impredicative wrapper `LogArr`:
--   `HaltsV` -> `logVLam` -> `LogArr` -> `HaltsV`.
--
-- Root cause (`GHC.Rename.Module.splitLocalSourceTables` / `independent_types`):
-- `splitLocalSourceTables` requires all local datatypes mentioned in a
-- term-to-`Type` function to be schedulable strictly before it, rejecting
-- mutually recursive `data`/`newtype` <-> term-to-`Type` SCCs with `GHC-68947`
-- ("No checked equations are available for 'logVLam' in a type").
module R13_LargeElimMutualData
  ( Val (..)
  , HaltsV (..)
  , LogArr (..)
  , logVLam
  , botProof
  ) where

import Data.Kind (Type)
import HaskLib.Nat (Nat (..))

data Val = Bot | Arr Val Val | Join Val Val

type HaltsV :: Val -> Type
data HaltsV v where
  MkHaltsV :: logVLam v -> HaltsV v

newtype LogArr (v :: Val) (w :: Val) =
  MkLogArr { runLogArr :: HaltsV v -> HaltsV w }

logVLam :: Val -> Type
logVLam Bot        = type ()
logVLam (Arr v w)  = type (LogArr v w)
logVLam (Join u v) = type (logVLam u, logVLam v)

botProof :: logVLam Bot
botProof = ()
