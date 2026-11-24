{-# LANGUAGE ExperimentalDependentTypes, GADTs, ScopedTypeVariables, TypeApplications, TypeOperators #-}
-- | Minimal reproducer (Serokell R04):
-- Transitivity of polymorphic `Iso a b` needs local composite functions
-- `to x = h (f x)` and `from y = g (k y)` to fill `MkIso`'s retained function
-- fields, yet the nested-call round-trip proofs do not reduce to those opaque
-- local composite names (GHC-83865).
module R04_ComposedIsoFields where

import Data.Type.Equality ((:~:))

data Iso a b where
    MkIso :: foreach (to :: a -> b) -> foreach (from :: b -> a)
          -> (foreach (x :: a) -> from (to x) :~: x)
          -> (foreach (y :: b) -> to (from y) :~: y)
          -> Iso a b

-- | The nested calls do not reduce to the two local composite functions.
pack :: forall a b c. foreach (f :: a -> b) -> foreach (g :: b -> a)
     -> foreach (h :: b -> c) -> foreach (k :: c -> b)
     -> (foreach (x :: a) -> g (k (h (f x))) :~: x)
     -> (foreach (y :: c) -> h (f (g (k y))) :~: y)
     -> Iso a c
pack f g h k left right = MkIso @a @c to from left right
  where
    to :: a -> c
    to x = h (f x)
    from :: c -> a
    from y = g (k y)
