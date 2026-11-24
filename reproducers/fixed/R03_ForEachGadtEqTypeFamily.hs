-- Minimal reproducer: GADT Given equality under a retained `foreach` binder
-- fails to rewrite a closed type family application!
--
-- Triggered in: PLFH.Part3.Adequacy (`subLogVLam` over closed type family `LogV`).
-- Card: R03 (retained binder skolem interaction with GADT Given equalities & type families).
--
-- Expected behavior: `testForEach` and `testForEachZero` both typecheck, just
-- like the erased `forall` control `ctrlErased`.
-- Actual behavior on published GHC 1a02a866e7 (590): fails with GHC-05617:
--   Could not deduce 'F v1 ~ F u2' from the context: v1 ~ u2
--   Could not deduce 'F u1 ~ ()' from the context: Zero ~ u1

{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeFamilies #-}
module R03_ForEachGadtEqTypeFamily (ctrlErased, testForEach, testForEachZero) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..))

type family F (n :: Nat) :: Type where
  F 'Zero     = ()
  F ('Succ n) = F n

-- Passing control with erased `forall`:
ctrlErased :: forall (u :: Nat) (v :: Nat). u :~: v -> F v -> F u
ctrlErased Refl x = x

-- Failing test 1: retained `foreach` + Given `v1 ~ u2` cannot prove `F v1 ~ F u2`:
testForEach :: foreach (u :: Nat) -> foreach (v :: Nat) -> u :~: v -> F v -> F u
testForEach _ _ eq x = case eq of
  Refl -> x

-- Failing test 2: retained `foreach` + Given `Zero ~ u1` cannot prove `F u1 ~ ()`:
testForEachZero :: foreach (u :: Nat) -> u :~: 'Zero -> F u
testForEachZero _ eq = case eq of
  Refl -> ()
