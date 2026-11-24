{-# LANGUAGE ExperimentalDependentTypes, GADTs, TypeOperators #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}
-- | Minimal reproducer (Serokell R13/R16):
-- Generic reflexivity of polymorphic `Iso a a` requires reducing `id (id x) :~: x`,
-- which fails with GHC-70565 because polymorphic `id` has no checked open equation.
module R13_PolymorphicIsoIdentity where

import Data.Type.Equality ((:~:) (Refl))

-- | Reflexivity of a polymorphic isomorphism needs this round trip.
identityRoundTrip :: foreach (x :: a) -> id (id x) :~: x
identityRoundTrip _ = Refl
