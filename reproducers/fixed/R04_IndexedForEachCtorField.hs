{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
-- | Minimal reproducer (Serokell R04 / R03):
-- While `foreach (t :: UTerm n) -> ...` works in function signatures
-- (`R03_NestedDatatypeForEach.hs`), binding an indexed GADT (`UTerm n` or
-- `Fin n`) as a `foreach` argument of a data constructor is rejected with
-- `GHC-83605` ("A retained value argument requires a lifted type parameter
-- or a supported algebraic type. Its declared domain is: UTerm n").
-- Likewise, packing a constructed indexed GADT value such as `Pair (ULam b')`
-- into `GHC.Sigma.Sigma` (`some (t' :: UTerm n) | ...`) is rejected with
-- `GHC-83605` ("GHC cannot use this expression as a retained index").
-- This blocks constructive normal-order evaluation (`Untyped.evalNormal`)
-- returning a retained reduct `t' :: UTerm n` with `BetaSteps t t'`.
module R04_IndexedForEachCtorField where

import Data.Kind (Type)
import HaskLib.Nat (Nat (..))

data UTerm (n :: Nat) where
  ULam :: UTerm (Succ n) -> UTerm n

type Wrap :: forall (n :: Nat). UTerm n -> Type
data Wrap t where
  MkWrap :: foreach (t :: UTerm n) -> Wrap t
