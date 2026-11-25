{-# LANGUAGE DependentTypes, ListTuplePuns #-}
-- | Minimal reproducer (Serokell R13 / R16; GHC Proposals #378 & #509):
-- Polymorphic source functions whose input datatype has distinct type-variable
-- parameters (like `swapProd :: (a, b) -> (b, a)`) publish checked equations,
-- whereas polymorphic functions whose input datatype applies a nested or
-- concrete type argument (like `assocProdTo :: ((a, b), c) -> (a, (b, c))`,
-- `unitRTo :: (a, ()) -> a`, or `distribRTo :: (Either a b, c) -> ...`) are
-- rejected with `GHC-68947` because `SourceTable.checkedDomains` requires
-- `traverse getTyVar_maybe args` and `null carried`.
--
-- Hit when upgrading the remaining commutative semiring laws (`prodAssoc`,
-- `prodUnitR`, `sumAssoc`, `prodDistribSum`) in `PLFH.Part1.Connectives` from
-- `Iff` to full polymorphic `Iso` bijections.
module R13_PolyNestedDomainOpenEq
  ( assocProdTo
  , assocProdFrom
  , assocProdRT
  ) where

import Data.Type.Equality ((:~:) (Refl))

assocPairR :: (a, b) -> c -> (a, (b, c))
assocPairR (x, y) z = (x, (y, z))

assocProdTo :: ((a, b), c) -> (a, (b, c))
assocProdTo (p, z) = assocPairR p z

assocPairL :: (b, c) -> a -> ((a, b), c)
assocPairL (y, z) x = ((x, y), z)

assocProdFrom :: (a, (b, c)) -> ((a, b), c)
assocProdFrom (x, p) = assocPairL p x

assocProdRT :: foreach (p :: ((a, b), c)) -> assocProdFrom (assocProdTo p) :~: p
assocProdRT ((_, _), _) = Refl
