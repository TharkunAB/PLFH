-- Generated from content/part1/Isomorphism.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications, TypeOperators #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}
{-# LINE 36 "content/part1/Isomorphism.md" #-}
module PLFH.Part1.Isomorphism
  ( Iff (..)
  , iffRefl
  , iffSym
  , iffTrans
  , Iso (..)
  , identityRoundTrip
  , isoRefl
  , isoSym
  , composeLeft
  , isoTrans
  , natIsoRefl
  , Embed (..)
  , embedRefl
  , embedTrans
  , isoImpliesEmbed
  , embedImpliesIff
  , binEmbedding
  , IsoSize (..)
  , idSize
  , idSizeId
  , isoSizeRefl
  , isoSizeSym
  ) where

import Data.Type.Equality ((:~:) (Refl), trans)
import HaskLib.Nat (Nat (..))
import PLFH.Part1.Induction (cong, fromTo)
import PLFH.Part1.Naturals (Bin (..), fromBin, toBin)

{-# LINE 73 "content/part1/Isomorphism.md" #-}
-- From Prelude:
-- (.) :: (b -> c) -> (a -> b) -> (a -> c)
-- (g . f) x = g (f x)

{-# LINE 108 "content/part1/Isomorphism.md" #-}
-- | Polymorphic isomorphism witness between `a` and `b`.
data Iso a b where
  MkIso :: foreach (to :: a -> b) -> foreach (from :: b -> a)
        -> (foreach (x :: a) -> from (to x) :~: x)
        -> (foreach (y :: b) -> to (from y) :~: y)
        -> Iso a b

-- | Symmetry: reverse an isomorphism.
isoSym :: Iso a b -> Iso b a
isoSym (MkIso to from fromTo' toFrom) = MkIso from to toFrom fromTo'

{-# LINE 126 "content/part1/Isomorphism.md" #-}
-- | Round-trip identity at any lifted type.
identityRoundTrip :: foreach (x :: a) -> id (id x) :~: x
identityRoundTrip _ = Refl

-- | Generic reflexivity of isomorphism (`≃-refl`).
isoRefl :: Iso a a
isoRefl = MkIso id id identityRoundTrip identityRoundTrip

{-# LINE 139 "content/part1/Isomorphism.md" #-}
-- | Identity function on Nat with explicit structural equations.
idSize :: Nat -> Nat
idSize Zero     = Zero
idSize (Succ n) = Succ n

-- | Round-trip identity proof for `idSize`.
idSizeId :: foreach (x :: Nat) -> idSize (idSize x) :~: x
idSizeId Zero     = Refl
idSizeId (Succ _) = Refl

-- | Reflexivity of the polymorphic witness at Nat.
natIsoRefl :: Iso Nat Nat
natIsoRefl = MkIso idSize idSize idSizeId idSizeId

-- | Monomorphic isomorphism witness on Nat.
data IsoSize where
  MkIsoSize :: foreach (to :: Nat -> Nat) -> foreach (from :: Nat -> Nat)
            -> (foreach (x :: Nat) -> from (to x) :~: x)
            -> (foreach (y :: Nat) -> to (from y) :~: y)
            -> IsoSize

-- | Reflexivity of `IsoSize`.
isoSizeRefl :: IsoSize
isoSizeRefl = MkIsoSize idSize idSize idSizeId idSizeId

-- | Symmetry of `IsoSize`: swap `to`/`from` and their round-trip proofs.
isoSizeSym :: IsoSize -> IsoSize
isoSizeSym (MkIsoSize to from fromTo' toFrom) = MkIsoSize from to toFrom fromTo'

{-# LINE 180 "content/part1/Isomorphism.md" #-}
-- | Cancel the inner round trip, then use the outer left inverse.
composeLeft :: foreach (f :: a -> b) -> foreach (g :: b -> a)
            -> foreach (h :: b -> c) -> foreach (k :: c -> b)
            -> (foreach (x :: a) -> g (f x) :~: x)
            -> (foreach (y :: b) -> k (h y) :~: y)
            -> foreach (x :: a) -> g (k (h (f x))) :~: x
composeLeft f g _ _ gf kh x = trans (cong g (kh (f x))) (gf x)

-- | Generic transitivity of isomorphism (`≃-trans`).
isoTrans :: forall a b c. Iso a b -> Iso b c -> Iso a c
isoTrans (MkIso f g gf fg) (MkIso h k kh hk) =
  MkIso @a @c (h . f) (g . k)
    (composeLeft f g h k gf kh)
    (composeLeft k h g f hk fg)

{-# LINE 207 "content/part1/Isomorphism.md" #-}
-- | Polymorphic embedding witness: `a` embeds faithfully in `b`.
data Embed a b where
  MkEmbed :: foreach (to :: a -> b) -> foreach (from :: b -> a)
          -> (foreach (x :: a) -> from (to x) :~: x)
          -> Embed a b

{-# LINE 221 "content/part1/Isomorphism.md" #-}
-- | Every isomorphism gives an embedding.
isoImpliesEmbed :: Iso a b -> Embed a b
isoImpliesEmbed (MkIso to from left _) = MkEmbed to from left

-- | Generic reflexivity of embedding (`≲-refl`).
embedRefl :: Embed a a
embedRefl = isoImpliesEmbed isoRefl

-- | Generic transitivity of embedding (`≲-trans`).
embedTrans :: forall a b c. Embed a b -> Embed b c -> Embed a c
embedTrans (MkEmbed f g gf) (MkEmbed h k kh) =
  MkEmbed @a @c (h . f) (g . k) (composeLeft f g h k gf kh)

-- | Every embedding gives a logical equivalence.
embedImpliesIff :: Embed a b -> Iff a b
embedImpliesIff (MkEmbed to from _) = Iff to from

{-# LINE 246 "content/part1/Isomorphism.md" #-}
-- | Natural numbers embed in binary numerals (`ℕ ≲ Bin`).
binEmbedding :: Embed Nat Bin
binEmbedding = MkEmbed toBin fromBin fromTo

{-# LINE 280 "content/part1/Isomorphism.md" #-}
-- | Logical equivalence (bi-implication) between propositions `a` and `b`.
data Iff a b = Iff
  { toIff   :: a -> b
  , fromIff :: b -> a
  }

-- | Reflexivity of logical equivalence.
iffRefl :: Iff a a
iffRefl = Iff id id

-- | Symmetry of logical equivalence.
iffSym :: Iff a b -> Iff b a
iffSym (Iff f g) = Iff g f

-- | Transitivity of logical equivalence.
iffTrans :: Iff a b -> Iff b c -> Iff a c
iffTrans (Iff f1 g1) (Iff f2 g2) = Iff (f2 . f1) (g1 . g2)
