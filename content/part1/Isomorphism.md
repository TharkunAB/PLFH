---
title: "Isomorphism: Isomorphism and embedding"
prev: /equality/
next: /connectives/
src: content/part1/Isomorphism.md
module: PLFH.Part1.Isomorphism
plfaChapter: https://plfa.inf.ed.ac.uk/Isomorphism/
---

In this chapter we introduce three ways of comparing two types `a` and `b`
by constructing functions between them:

- **Isomorphism** (`Iso a b`, written `A ≃ B` in PLFA): functions
  `to :: a -> b` and `from :: b -> a` together with proofs that both round
  trips are the identity (`from (to x) :~: x` and `to (from y) :~: y`). Two
  types are isomorphic when their elements stand in one-to-one correspondence.
- **Embedding** (`Embed a b`, written `A ≲ B` in PLFA): `to` and `from`
  together with the left-inverse proof `from (to x) :~: x`. Every element of
  `a` maps faithfully into `b`, though `b` may contain extra elements (or
  duplicate representations).
- **Logical equivalence** (`Iff a b`, written `A ⇔ B` in PLFA): `to` and
  `from` with no round-trip equations at all. When types are read as
  propositions, `Iff a b` says that `a` holds if and only if `b` holds.

## Imports

We import propositional equality `(:~:)`, equality transitivity `trans`,
dependent composition `(.)` from `Data.Function.Dependent`, congruence `cong`,
`Nat` and `plus` from `Data.Nat.Dependent`, binary numerals `Bin`, `fromBin`,
`toBin` from [Naturals](/naturals/), and `plusComm` / `fromTo` from
[Induction](/induction/).

```haskell
{-# LANGUAGE DependentTypes #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}
module PLFH.Part1.Isomorphism
  ( Iff (..)
  , iffRefl
  , iffSym
  , iffTrans
  , FunExt
  , plus'
  , sameApp
  , samePlus
  , Iso (..)
  , identityRoundTrip
  , isoRefl
  , isoSym
  , composeLeft
  , isoTrans
  , Embed (..)
  , embedRefl
  , embedTrans
  , isoImpliesEmbed
  , embedImpliesIff
  , binEmbedding
  ) where

import Prelude hiding ((.))
import Data.Function.Dependent ((.))
import Data.Kind (Type)
import GHC.Matchability (U)
import Data.Nat.Dependent (Nat (..), plus)
import Data.Type.Equality ((:~:) (Refl), trans)
import PLFH.Part1.Induction (cong, fromTo, plusComm)
import PLFH.Part1.Naturals (Bin (..), fromBin, toBin)
```

## Lambda expressions and function composition

Just as in Agda, Haskell writes anonymous functions with a backslash
(`\x -> body`) and composes functions with `()`. In `dependent-base`,
[`Data.Function.Dependent`](/dependent-base/#datafunctiondependent) generalizes
`Prelude.()` so the outer consumer may depend on the intermediate value `f x`
while remaining transparent for ordinary functions:

```haskell
-- From Data.Function.Dependent:
-- (.) :: forall {a} {b} {m :: Matchability} (c :: b %m -> Type).
--        (foreach (y :: b) -> c y)
--     -> foreach (f :: a -> b)
--     -> foreach (x :: a)
--     -> c (f x)
-- (g . f) x = g (f x)
```

Notice that function composition is associative (`(h. g). f = h. (g. f)`)
and has `id` as both left and right identity, pointwise for every `x`.

## Extensionality

When are two functions `f, g :: a -> b` equal? **Function extensionality**
asserts that if two functions agree on every input (`foreach (x :: a) -> f x :~: g x`),
then the functions themselves are equal (`f :~: g`).

Just like Agda (and Martin-Löf intensional type theory), Dependent Haskell
does **not** prove function extensionality internally. In PLFA, extensionality
is introduced via `postulate` when needed for isomorphisms involving function
types (such as `currying` in [Connectives](/connectives/)). In PLFH, we keep
our checked modules completely axiom-free (no `postulate` or `unsafeCoerce`),
either stating function-space equivalences via `Iff` or taking an explicit
`FunExt` hypothesis as a function argument. For instance, `plus'` recurses on
its second argument rather than its first; `sameApp` proves they agree at every
pair of inputs, and `samePlus` lifts that pointwise agreement to `plus :~: plus'`
given explicit `FunExt` hypotheses:

```haskell
-- | Function extensionality stated as an explicit type hypothesis (no axiom).
type FunExt (a :: Type) (b :: Type) =
  forall (f g :: a %U -> b). (foreach (x :: a) -> f x :~: g x) -> f :~: g

-- | Addition defined by recursion on its second argument (`_+′_` in PLFA).
plus' :: Nat -> Nat -> Nat
plus' m Zero     = m
plus' m (Succ n) = Succ (plus' m n)

-- | `plus` and `plus'` agree pointwise on all natural numbers (`same-app`).
sameApp :: foreach (m n :: Nat) -> plus m n :~: plus' m n
sameApp m Zero     = plusComm m Zero
sameApp m (Succ n) = trans (plusComm m (Succ n)) (cong Succ (trans (plusComm n m) (sameApp m n)))

-- | Given function extensionality, `plus` and `plus'` are equal as functions (`same`).
samePlus :: FunExt Nat (Nat %U -> Nat) -> FunExt Nat Nat -> plus :~: plus'
samePlus ext1 ext2 = ext1 (\m -> ext2 (\n -> sameApp m n))
```

## Isomorphism (`_≃_`)

Two types `a` and `b` are **isomorphic** if there are retained functions
`to :: a -> b` and `from :: b -> a` together with higher-rank `foreach`
proofs witnessing that `from` is a left inverse of `to` and `to` is a left
inverse of `from`.

Because `to` and `from` are bound with `foreach` inside `MkIso`, both
functions are in scope inside the types of the two round-trip proof fields.
Taking the inverse (`isoSym`) simply exchanges the two functions along with
their proofs:

```haskell
-- | Polymorphic isomorphism witness between `a` and `b`.
data Iso a b where
  MkIso :: foreach (to :: a -> b) -> foreach (from :: b -> a)
        -> (foreach (x :: a) -> from (to x) :~: x)
        -> (foreach (y :: b) -> to (from y) :~: y)
        -> Iso a b

-- | Symmetry: reverse an isomorphism.
isoSym :: Iso a b -> Iso b a
isoSym (MkIso to from fromTo' toFrom) = MkIso from to toFrom fromTo'
```

**Reflexivity** (`isoRefl :: Iso a a`) uses Prelude's polymorphic `id` in both
directions at any lifted type `a`. GHC's checked equation for `id` reduces
`id (id x)` directly to `x` (we pass `-fno-enable-rewrite-rules` for the
module so GHC's `GHC.Base` rewrite rules on `id`/`()` do not inhibit checked
open-equation reduction):

```haskell
-- | Round-trip identity at any lifted type.
identityRoundTrip :: foreach (x :: a) -> id (id x) :~: x
identityRoundTrip _ = Refl

-- | Generic reflexivity of isomorphism (`≃-refl`).
isoRefl :: Iso a a
isoRefl = MkIso id id identityRoundTrip identityRoundTrip
```

### Transitivity of isomorphism (`≃-trans`)

Given an isomorphism `Iso a b` with maps `f :: a -> b` and `g :: b -> a`, and
an isomorphism `Iso b c` with maps `h :: b -> c` and `k :: c -> b`, we compose
the forward maps directly as `h . f` and the reverse maps as `g . k` using
`Data.Function.Dependent.(.)`.

To prove the left round trip `g (k (h (f x))) :~: x`, the inner inverse proof
`kh (f x)` gives `k (h (f x)) :~: f x`; applying `cong g` surrounds both sides
with `g`, and `trans` composes that step with the outer inverse proof `gf x`:

```haskell
-- | Cancel the inner round trip, then use the outer left inverse.
composeLeft :: foreach (f :: a -> b) -> foreach (g :: b -> a)
            -> foreach (h :: b -> c) -> foreach (k :: c -> b)
            -> (foreach (x :: a) -> g (f x) :~: x)
            -> (foreach (y :: b) -> k (h y) :~: y)
            -> foreach (x :: a) -> g (k (h (f x))) :~: x
composeLeft f g _ _ gf kh x = trans (cong g (kh (f x))) (gf x)

-- | Generic transitivity of isomorphism (`≃-trans`), composing maps directly
-- with `Data.Function.Dependent.(.)`.
isoTrans :: forall a b c. Iso a b -> Iso b c -> Iso a c
isoTrans (MkIso f g gf fg) (MkIso h k kh hk) =
  MkIso @a @c (h . f) (g . k)
    (composeLeft f g h k gf kh)
    (composeLeft k h g f hk fg)
```

Exchanging the roles of `(f, g, gf)` and `(k, h, hk)` gives the reverse round
trip by the exact same lemma `composeLeft`.

## Embedding (`_≲_`)

An **embedding** weakens isomorphism by requiring only the left inverse
`from (to x) :~: x`, dropping the reverse round-trip obligation `to (from y) :~: y`.
In other words, `a` sits faithfully inside `b`, while `b` may have additional
inhabitants (or multiple representations of the same element of `a`).

```haskell
-- | Polymorphic embedding witness: `a` embeds faithfully in `b`.
data Embed a b where
  MkEmbed :: foreach (to :: a -> b) -> foreach (from :: b -> a)
          -> (foreach (x :: a) -> from (to x) :~: x)
          -> Embed a b
```

Every isomorphism immediately gives an embedding by forgetting the reverse
round-trip proof (`isoImpliesEmbed`), giving generic embedding reflexivity
`embedRefl` immediately, and `composeLeft` gives generic embedding transitivity
`embedTrans` (`≲-trans`) as well. Finally, forgetting the remaining round-trip
proof gives logical equivalence (`embedImpliesIff`):

```haskell
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
```

### Example: embedding `Nat` in `Bin`

In [Induction](/induction/) we proved `fromTo :: foreach (n :: Nat) -> fromBin (toBin n) :~: n`.
That proof is *precisely* the left-inverse witness needed to embed natural
numbers into binary bitstrings.

```haskell
-- | Natural numbers embed in binary numerals (`ℕ ≲ Bin`).
binEmbedding :: Embed Nat Bin
binEmbedding = MkEmbed toBin fromBin fromTo
```

Why is `binEmbedding` only an embedding and *not* an isomorphism `Iso Nat Bin`?
Because the reverse round trip can change a non-canonical bitstring into its
canonical form. For instance, `fromBin Nil` is `0`, and `toBin 0` is
`X0 Nil`, not `Nil`. Trying to prove `toBin (fromBin Nil) :~: Nil` is rejected
by GHC (`GHC-83865`):

```{.haskell .fail name="NegBinReverseRoundTrip" expect="GHC-83865"}
{-# LANGUAGE DependentTypes #-}
module NegBinReverseRoundTrip where

import Data.Type.Equality ((:~:) (Refl))
import PLFH.Part1.Naturals (Bin (..), fromBin, toBin)

reverseRoundTrip :: toBin (fromBin Nil) :~: Nil
reverseRoundTrip = Refl
```

(When we restrict `Bin` to *canonical* bitstrings satisfying `Can b`,
`Relations.toBinCan` and `Relations.toFromCan` complete the reverse round
trip, establishing the full bijection between `Nat` and canonical `Bin`)

## Logical equivalence (`_⇔_`)

Dropping *both* round-trip proofs leaves **logical equivalence**
(bi-implication, `Iff a b`): two functions going back and forth with no
equality obligations. Logical equivalence is an equivalence relation on all
types (`iffRefl`, `iffSym`, `iffTrans`):

```haskell
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
```

## Exercises

### Exercise `≃-implies-≲` on functions (practice)

Given `Iso a b` and `Iso c d`, write a function constructing `Iff (a -> c) (b -> d)`
and explain why upgrading that equivalence to `Iso (a -> c) (b -> d)` requires
function extensionality (`FunExt`).

### Exercise `≲-preorder-not-partial-order` (practice)

Give two distinct types `a` and `b` together with embeddings `Embed a b` and
`Embed b a` that are not isomorphic (`Not (Iso a b)`), or explain what extra
condition on the round-trip proofs turns mutual embedding into an isomorphism.

## Changes from PLFA

- Represents `Iso a b` and `Embed a b` with retained function fields (`foreach (to :: a -> b) -> foreach (from :: b -> a) -> ...`) composed via `Data.Function.Dependent.(.)`.
- Dependent Haskell does not postulate function extensionality; extensional identities take an explicit `FunExt` hypothesis where needed.
