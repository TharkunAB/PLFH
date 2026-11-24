{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (R03 Desugar Core Lint): nested dependent `case` on two
-- fields of a retained constructor produces an out-of-scope coercion variable
-- in Core Lint immediately after Desugar (before optimization).
--
-- Triggered while proving `subInvDist` in PLFH.Part3.Denotational.
-- Note: splitting the inner `case r of` into a separate helper function
-- passes Core Lint cleanly.
module R03_NestedDepCaseCoreLint (bad) where

import Data.Type.Equality ((:~:) (Refl))

data V = B | A V V | J V V

bad :: foreach (x :: V) -> (x :~: 'J ('A a b) ('A a c)) -> x :~: 'J ('A a b) ('A a c)
bad B       eq = case eq of {}
bad (A _ _) eq = case eq of {}
bad (J l r) eq = case l of
  B     -> case eq of {}
  J _ _ -> case eq of {}
  A _ _ -> case r of
    B     -> case eq of {}
    J _ _ -> case eq of {}
    A _ _ -> case eq of
      Refl -> Refl
