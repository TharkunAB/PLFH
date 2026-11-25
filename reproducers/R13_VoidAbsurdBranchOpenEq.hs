{-# LANGUAGE DependentTypes #-}
-- | Minimal reproducer (Serokell R13 Open Evaluation follow-up to
-- `fixed/R13_PolyNestedDomainOpenEq.hs`; GHC Proposals #378, #509):
-- Wave 8A (`22b6548540`) certified polymorphic functions over nested/concrete
-- domains (`((a, b), c)`, `(a, ())`, `(Either a b, c)`), unblocking 10 of 12
-- `Connectives` semiring `Iso`s. Remaining two (`sumZeroRIso :: Iso (Either a Void) a`
-- and `sumZeroLIso :: Iso (Either Void a) a`) define `sumZeroRTo :: Either a Void -> a`
-- with an uninhabited `Right v -> case v of {}` (or `absurd v`) branch.
--
-- Actual: `GHC-68947` ("No checked equations are available for `sumZeroRTo' in a type"),
-- because `SourceTable` requires every constructor branch RHS to be a checked
-- constructor/variable/call expression and rejects empty-case / `absurd` branches
-- on zero-constructor datatypes like `Data.Void.Void`.
module R13_VoidAbsurdBranchOpenEq
  ( sumZeroRTo
  , sumZeroRLR
  , sumZeroRRL
  ) where

import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void)

sumZeroRTo :: Either a Void -> a
sumZeroRTo (Left x)  = x
sumZeroRTo (Right v) = case v of {}

sumZeroRLR :: foreach (s :: Either a Void) -> Left (sumZeroRTo s) :~: s
sumZeroRLR (Left _)  = Refl
sumZeroRLR (Right v) = case v of {}

sumZeroRRL :: foreach (x :: a) -> sumZeroRTo (Left x) :~: x
sumZeroRRL _ = Refl
