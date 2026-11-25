{-# LANGUAGE AllowAmbiguousTypes, DependentTypes #-}
-- | Full polymorphic membership isomorphism `Iso (Any p xs) (AnyWitness p xs)`
-- (`Any-∃`), proving both inverse laws (`witnessToAny (anyToWitness r) :~: r`
-- and `anyToWitness (witnessToAny w) :~: w`) directly over the ordinary
-- converters exported by `PLFH.Part1.Lists`.
module PLFH.Part1.AnyWitnessIso (anyIsoWitness) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import GHC.Types (List)
import HaskLib (Matchability, rewrite)
import PLFH.Part1.Isomorphism (Iso (MkIso))
import PLFH.Part1.Lists (Any (..), AnyWitness (..), In)
import qualified PLFH.Part1.Lists as L

membershipRoundTrip
  :: forall {a} {m :: Matchability} (p :: a %m -> Type) {x :: a} {xs :: List a} (d :: p x).
     foreach (r :: In x xs) ->
     L.anyToWitness (L.witnessToAny (MkAnyWitness r d :: AnyWitness p xs)) :~: MkAnyWitness r d
membershipRoundTrip (Here equality) = case equality of Refl -> Refl
membershipRoundTrip (There r)       = rewrite (membershipRoundTrip @p @d r) Refl

-- | Keep the shape of the encoded package with the proof that it decodes back.
type Encoded :: forall {a} {m :: Matchability}.
                forall (p :: a %m -> Type) (xs :: List a) ->
                Any p xs -> AnyWitness p xs -> Type
data Encoded p xs input result where
  Encoded :: forall {a} {m :: Matchability} {p :: a %m -> Type}
                    {xs :: List a} {x :: a} (member :: In x xs) (d :: p x)
                    (input :: Any p xs).
             L.witnessToAny (MkAnyWitness member d :: AnyWitness p xs) :~: input
          -> Encoded p xs input (MkAnyWitness member d)

encodedRoundTrip
  :: forall {a} {m :: Matchability} (p :: a %m -> Type) {xs :: List a}.
     foreach (r :: Any p xs) -> Encoded p xs r (L.anyToWitness r)
encodedRoundTrip (Here d)  = Encoded @(Here Refl) @d @(Here d) Refl
encodedRoundTrip (There r) = case encodedRoundTrip @p r of
  Encoded @member @d Refl -> Encoded @(There member) @d @(There r) Refl

anyRoundTrip
  :: forall {a} {m :: Matchability} (p :: a %m -> Type) {xs :: List a}.
     foreach (r :: Any p xs) -> L.witnessToAny (L.anyToWitness r) :~: r
anyRoundTrip r = case encodedRoundTrip @p r of
  Encoded proof -> proof

witnessRoundTrip
  :: forall {a} {m :: Matchability} (p :: a %m -> Type) {xs :: List a}.
     foreach (w :: AnyWitness p xs) -> L.anyToWitness (L.witnessToAny w) :~: w
witnessRoundTrip (MkAnyWitness r d) = membershipRoundTrip @p @d r

-- | Both ordinary converters preserve the selected occurrence and its evidence (`Any-∃`).
anyIsoWitness
  :: forall {a} {m :: Matchability} (p :: a %m -> Type) (xs :: List a).
     Iso (Any p xs) (AnyWitness p xs)
anyIsoWitness =
  MkIso L.anyToWitness L.witnessToAny (anyRoundTrip @p) (witnessRoundTrip @p)
