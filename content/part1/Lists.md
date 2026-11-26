---
title: "Lists: Lists and higher-order functions"
prev: /Decidable/
next: /Lambda/
src: content/part1/Lists.md
module: PLFH.Part1.Lists
plfaChapter: https://plfa.inf.ed.ac.uk/Lists/
---

This chapter discusses the **list** datatype. It brings together the
techniques we have developed throughout Part 1—induction, congruence,
rewriting, decidability, and indexed predicates—and applies them to
polymorphic data structures and **higher-order functions** (`map`, `foldr`,
monoids, and the list quantifiers `All`, `Any`, and membership `In`).

On this Dependent Haskell fork, **ordinary Prelude lists**, **Prelude `(++)`**,
**Prelude `map`**, and **Prelude `reverse`** already have checked open source
equations—so we prove classic list laws directly over standard Haskell lists
with no shadow `List` datatype! Moreover, `-XDependentTypes` enables
`-XNoListTuplePuns` automatically, so importing `List` from `GHC.Types` lets us
write the promoted empty list `[]`, cons `x : xs`, and list literals `[0, 1, 0]`
at the type level **without a single leading `'` tick**!

## Imports

We import `Type`, `(:~:)` and `gcastWith`, `Void`, `List` from `GHC.Types`,
`Matchability` and `rewrite` from `Data.Type.Equality.Dependent`, `size` and
`foldr` from `Data.List.Dependent`, `lengthReverse` from
`Data.List.Dependent.Properties`, `Nat` and `plus` from `Data.Nat.Dependent`,
`plusZero` from `Data.Nat.Dependent.Properties`, `Dec`/`Not` from
[Decidable](/Decidable/), and `Iff` from [Isomorphism](/Isomorphism/).

```haskell
{-# LANGUAGE AllowAmbiguousTypes, DependentTypes #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}
module PLFH.Part1.Lists
  ( appendAssoc
  , appendNilR
  , lengthAppendLaw
  , lengthMapLaw
  , lengthReverseLaw
  , mapAppend
  , mapCompose
  , mapId
  , shunt
  , shuntAppend
  , rev
  , revAppend
  , revInvolutive
  , shuntRev
  , reverses
  , downFrom
  , zeros
  , lengthDownFrom
  , lengthZeros
  , foldrPlusSeed
  , foldrPlusAppend
  , foldrTimesSeed
  , foldrTimesAppend
  , All (..)
  , Any (..)
  , In
  , allAppend
  , allAppendInv
  , allMap
  , anyAppendL
  , anyAppendR
  , anyAppendInv
  , notAnyToAllNot
  , allNotToNotAny
  , notAnyIffAllNot
  , allToIn
  , inToAll
  , AnyWitness (..)
  , anyToWitness
  , witnessToAny
  , anyIffWitness
  , memberValue
  , decAll
  , decAny
  , decIn
  , zeroInList
  , threeNotInList
  ) where

import Prelude hiding (foldr)
import Data.Kind (Type)
import Data.List.Dependent (foldr, size)
import Data.List.Dependent.Properties (lengthReverse)
import Data.Nat.Dependent (Nat (..), plus)
import Data.Nat.Dependent.Properties (plusZero)
import Data.Type.Equality ((:~:) (Refl), gcastWith, sym, trans)
import Data.Type.Equality.Dependent (Matchability, rewrite)
import Data.Void (Void)
import GHC.Tuple (Tuple2)
import GHC.Types (List)
import PLFH.Part1.Decidable (Dec (..), Not)
import PLFH.Part1.Induction (cong, plusAssoc, timesAssoc)
import PLFH.Part1.Isomorphism (Iff (..))
import PLFH.Part1.Naturals (times)
```

## Lists and Append (`++`)

In Haskell, a list of elements of type `a` has type `List a` (ordinarily
written `[a]`, which puns the term-level list bracket syntax; with
`-XNoListTuplePuns` we write the type constructor as `List a` so that `[]`,
`:`, and `[0, 1, 0]` refer unambiguously to the data constructors even in
types!). As PLFA observes, *"A list is a strange beast: it has a head and a
tail, nothing in between, and the tail is itself another list!"*

Prelude `(++)` appends two lists in time linear in the length of the first
list:

```text
[]       ++ ys = ys
(x : xs) ++ ys = x : (xs ++ ys)
```

Using Prelude `(++)` directly in both types and terms, we prove that append
is associative (`appendAssoc`) and has `[]` as its right identity
(`appendNilR`; left identity `[] ++ xs :~: xs` holds immediately by `Refl`).
Together, `(++)` and `[]` form a **monoid** over lists:

```haskell
-- | Associativity of Prelude list append: (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
appendAssoc :: forall a. foreach (xs ys zs :: List a)
            -> ((xs ++ ys) ++ zs) :~: (xs ++ (ys ++ zs))
appendAssoc []       _  _  = Refl
appendAssoc (_ : xs) ys zs = rewrite (appendAssoc xs ys zs) Refl

-- | Right identity of Prelude list append: xs ++ [] = xs.
appendNilR :: forall a. foreach (xs :: List a) -> (xs ++ []) :~: xs
appendNilR []       = Refl
appendNilR (_ : xs) = rewrite (appendNilR xs) Refl
```

## Length laws (`size`)

PLFA defines `length` and proves `length (xs ++ ys) ≡ length xs + length ys`,
along with length preservation for `map` and `reverse`. Using
[`Data.List.Dependent.size`](/DependentBase/#datalistdependent) (`size :: List a -> Nat`) over
ordinary Prelude `(++)` and `map`, we prove `lengthAppendLaw` and
`lengthMapLaw` directly by structural induction on `xs` (the same proofs are
also exported by [`Data.List.Dependent.Properties`](/DependentBase/#datalistdependentproperties) as `lengthAppend` and
`lengthMap`, alongside `lengthReverse` for Prelude's tail-recursive `reverse`):

```haskell
-- | Length of append: size (xs ++ ys) = size xs + size ys.
lengthAppendLaw :: forall a. foreach (xs ys :: List a)
                -> size (xs ++ ys) :~: plus (size xs) (size ys)
lengthAppendLaw []       _  = Refl
lengthAppendLaw (_ : xs) ys = cong Succ (lengthAppendLaw xs ys)

-- | Length of map: size (map f xs) = size xs.
lengthMapLaw :: forall a b. foreach (f :: a -> b) -> foreach (xs :: List a)
             -> size (map f xs) :~: size xs
lengthMapLaw _ []       = Refl
lengthMapLaw f (_ : xs) = cong Succ (lengthMapLaw f xs)

-- | Length of Prelude reverse (proved via accumulator in Data.List.Dependent.Properties.lengthReverse).
lengthReverseLaw :: forall a. foreach (xs :: List a)
                 -> size (reverse xs) :~: size xs
lengthReverseLaw = lengthReverse
```

<div class="note-box">
<strong>Rewrite rules note:</strong>
As documented in the GHC fork's README, modules using <code>lengthMap</code>
disable rewrite rules (<code>-fno-enable-rewrite-rules</code>) because stock
list-fusion rewrite rules can change demand on partial inputs.
</div>

## Higher-order list laws: `map`

`map` is a **higher-order function**—it takes a function `f :: a -> b` as an
argument and applies `f` to every element of a list. Because
`foreach (f :: a -> b)` retains an arbitrary unknown Haskell function, we can
prove the append-homomorphism and functor laws (`mapAppend`, `mapCompose`,
`mapId`) for **ordinary Prelude `map`** and **`(.)`**:

```haskell
-- | Map distributes over append: map f (xs ++ ys) = map f xs ++ map f ys.
mapAppend :: forall a b. foreach (f :: a -> b) -> foreach (xs :: List a) -> foreach (ys :: List a)
          -> map f (xs ++ ys) :~: (map f xs ++ map f ys)
mapAppend _ []       _  = Refl
mapAppend f (_ : xs) ys = gcastWith (mapAppend f xs ys) Refl

-- | Functor composition law: map (g . f) xs = map g (map f xs).
mapCompose :: forall a b c. foreach (g :: b -> c) -> foreach (f :: a -> b) -> foreach (xs :: List a)
           -> map (g . f) xs :~: map g (map f xs)
mapCompose _ _ []       = Refl
mapCompose g f (_ : xs) = gcastWith (mapCompose g f xs) Refl

-- | Functor identity law: map id xs = xs.
mapId :: forall a. foreach (xs :: List a) -> map id xs :~: xs
mapId []       = Refl
mapId (_ : xs) = gcastWith (mapId xs) Refl
```

## Faster reverse (`shunt`), countdown lists (`downFrom`, `zeros`), and `foldr`

Naive list reversal (`rev (x : xs) = rev xs ++ [x]`) takes **quadratic**
time because each step appends to the end of the growing reversed tail.
PLFA introduces the accumulating helper **`shunt`**—whose second argument
grows as its first argument shrinks—so `shunt xs []` reverses a list in
**linear** time! *"Generalising on an auxiliary argument, which becomes
larger as the argument on which we recurse or induct becomes smaller, is a
common trick. It belongs in your quiver of arrows, ready to slay the right
problem."*

Both `shunt` / `shuntAppend` and PLFA's `downFrom` / `zeros` countdown lists
check directly:

```haskell
-- | Accumulating linear-time list reversal helper `shunt`.
shunt :: List a -> List a -> List a
shunt []     ys = ys
shunt (x:xs) ys = shunt xs (x : ys)

-- | Distributivity of `shunt` over append (`shunt-++`).
shuntAppend :: forall a. foreach (xs ys zs :: List a)
            -> shunt (xs ++ ys) zs :~: shunt ys (shunt xs zs)
shuntAppend []     _  _  = Refl
shuntAppend (x:xs) ys zs = shuntAppend xs ys (x : zs)

-- | Naive quadratic list reversal (`reverse` in PLFA).
rev :: List a -> List a
rev []     = []
rev (x:xs) = rev xs ++ [x]

-- | Reversal distributes contravariantly over append (`reverse-++-distrib`).
revAppend :: forall a. foreach (xs ys :: List a)
          -> rev (xs ++ ys) :~: (rev ys ++ rev xs)
revAppend []     ys = sym (appendNilR @a (rev ys))
revAppend (x:xs) ys =
  case revAppend xs ys of
    Refl -> case appendAssoc (rev ys) (rev xs) [x] of
      Refl -> Refl

-- | Reversing a list twice returns the original list (`reverse-involutive`).
revInvolutive :: forall a. foreach (xs :: List a) -> rev (rev xs) :~: xs
revInvolutive []     = Refl
revInvolutive (x:xs) =
  case revAppend (rev xs) [x] of
    Refl -> case revInvolutive xs of
      Refl -> Refl

-- | Relating `shunt` to naive `rev` (`shunt-reverse`): `shunt xs ys = rev xs ++ ys`.
shuntRev :: forall a. foreach (xs ys :: List a)
         -> shunt xs ys :~: (rev xs ++ ys)
shuntRev []     _  = Refl
shuntRev (x:xs) ys =
  case shuntRev xs (x : ys) of
    Refl -> case appendAssoc (rev xs) [x] ys of
      Refl -> Refl

-- | Fast linear-time reversal `shunt xs []` agrees with naive `rev xs` (`reverses`)!
reverses :: forall a. foreach (xs :: List a) -> shunt xs [] :~: rev xs
reverses xs =
  case shuntRev xs [] of
    Refl -> appendNilR (rev xs)

-- | Countdown list from `n - 1` down to `0` (`downFrom`).
downFrom :: Nat -> List Nat
downFrom Zero     = []
downFrom (Succ n) = n : downFrom n

-- | A list of `n` copies of `Zero`.
zeros :: Nat -> List Nat
zeros Zero     = []
zeros (Succ n) = Zero : zeros n

-- | Length of `downFrom n` equals `n`.
lengthDownFrom :: foreach (n :: Nat) -> size (downFrom n) :~: n
lengthDownFrom Zero     = Refl
lengthDownFrom (Succ n) = case lengthDownFrom n of { Refl -> Refl }

-- | Length of `zeros n` equals `n`.
lengthZeros :: foreach (n :: Nat) -> size (zeros n) :~: n
lengthZeros Zero     = Refl
lengthZeros (Succ n) = case lengthZeros n of { Refl -> Refl }
```

### Right folds and monoid homomorphisms (`foldr`)

Using `Data.List.Dependent.foldr` (wrapping the standard library's list `foldr`), we prove PLFA's
monoid-homomorphism fold laws (`foldr-monoid-++`) for both `(Nat, plus, 0)`
and `(Nat, times, 1)`—moving the seed outside a right fold (`foldrPlusSeed`,
`foldrTimesSeed`) and proving that folding a concatenated list equals combining
the individual folds (`foldrPlusAppend`, `foldrTimesAppend`), using our visible
`cong (plus x)` / `cong (times x)` and `sym (plusAssoc ...)` / `sym (timesAssoc ...)`
from [Induction](/Induction/):

```haskell
-- | Move the seed to the right of the zero-seeded fold.
foldrPlusSeed :: foreach (xs :: List Nat) -> foreach (z :: Nat)
              -> foldr plus z xs :~: plus (foldr plus Zero xs) z
foldrPlusSeed []       _ = Refl
foldrPlusSeed (x : xs) z =
  trans (cong (plus x) (foldrPlusSeed xs z))
        (sym (plusAssoc x (foldr plus Zero xs) z))

-- | Sum concatenated lists by adding their individual sums (`foldr-monoid-++` for `+`).
foldrPlusAppend :: foreach (xs ys :: List Nat)
                -> foldr plus Zero (xs ++ ys)
               :~: plus (foldr plus Zero xs) (foldr plus Zero ys)
foldrPlusAppend []       _  = Refl
foldrPlusAppend (x : xs) ys =
  trans (cong (plus x) (foldrPlusAppend xs ys))
        (sym (plusAssoc x (foldr plus Zero xs) (foldr plus Zero ys)))

-- | Move the seed to the right of a multiplicative right fold.
foldrTimesSeed :: foreach (xs :: List Nat) -> foreach (z :: Nat)
               -> foldr times z xs :~: times (foldr times 1 xs) z
foldrTimesSeed []       z = sym (plusZero z)
foldrTimesSeed (x : xs) z =
  trans (cong (times x) (foldrTimesSeed xs z))
        (sym (timesAssoc x (foldr times 1 xs) z))

-- | Multiply concatenated lists by multiplying their individual products (`foldr-monoid-++` for `*`).
foldrTimesAppend :: foreach (xs ys :: List Nat)
                 -> foldr times 1 (xs ++ ys)
                :~: times (foldr times 1 xs) (foldr times 1 ys)
foldrTimesAppend []       ys = sym (plusZero (foldr times 1 ys))
foldrTimesAppend (x : xs) ys =
  trans (cong (times x) (foldrTimesAppend xs ys))
        (sym (timesAssoc x (foldr times 1 xs) (foldr times 1 ys)))
```

> **Why `-fno-enable-rewrite-rules` at `-O2`?**
> Spine-strict accumulator proofs like `shuntAppend` check at default `-O2`,
> whereas `mapAppend` disables Prelude list-fusion rewrite rules via
> `-fno-enable-rewrite-rules`. This is a **deliberate soundness guard**, not a
> compiler bug: stock `-O2` `build`/`augment`/`map` fusion can alter strictness
> (for example, `null (map not (build producer ++ error "ys"))` forces `ys`
> under fusion while `null (map not (build producer) ++ map not (error "ys"))`
> returns `False`), so GHC refuses to certify `mapAppend` when list-fusion
> rules are active at `-O2`.

## Predicates on lists: `All`, `Any`, and membership (`∈`)

We now define the two fundamental indexed predicates over lists:

- **`All p xs`**: predicate `p` holds for *every* element of `xs`.
- **`Any p xs`**: predicate `p` holds for *at least one* element of `xs`.
- **List membership `In x xs`** (`x ∈ xs`): defined concisely as
  `Any ((:~:) x) xs`—some element of `xs` equals `x`!

By quantifying both `All` and `Any` over `{m :: Matchability}` (`p :: a %m -> Type`),
they accept **both** matchable GADT predicates (like `Even` or `(:~:) x`) **and**
unmatchable inline type-level lambdas (like `\x -> Not (p x)` for De Morgan's
law below!)—and with `-XNoListTuplePuns`, `[]`, `:`, and `[0, 1, 0]` all
appear without a single tick!

```haskell
-- | Matchability-polymorphic universal list predicate: `p` holds for every element of `xs`.
type All :: forall {a} {m :: Matchability}. (a %m -> Type) -> List a -> Type
data All p xs where
  AllNil  :: forall {a} {m :: Matchability} {p :: a %m -> Type}. All p []
  AllCons :: forall {a} {m :: Matchability} {p :: a %m -> Type} {x} {xs}.
             p x -> All p xs -> All p (x : xs)

-- | Matchability-polymorphic existential list predicate: `p` holds for some element of `xs`.
type Any :: forall {a} {m :: Matchability}. (a %m -> Type) -> List a -> Type
data Any p xs where
  Here  :: forall {a} {m :: Matchability} (p :: a %m -> Type) (x :: a) (xs :: List a).
           p x -> Any p (x : xs)
  There :: forall {a} {m :: Matchability} (p :: a %m -> Type) (xs :: List a) (x :: a).
           Any p xs -> Any p (x : xs)

-- | List membership (`_∈_`): `x` appears in `xs`.
type In (x :: a) (xs :: List a) = Any ((:~:) x) xs
```

### `All`, `Any`, and append (`++`)

A predicate holds for every element of `xs ++ ys` if and only if it holds for
every element of `xs` and every element of `ys` (`allAppend` / `allAppendInv`).
Dually, a predicate holds for *some* element of `xs ++ ys` if and only if it
holds for some element of `xs` or some element of `ys` (`anyAppendL`,
`anyAppendR`, `anyAppendInv`):

```haskell
-- | If `p` holds for all of `xs` and all of `ys`, it holds for `xs ++ ys`.
allAppend :: forall {a} {m :: Matchability} {p :: a %m -> Type} {xs} {ys}.
             All p xs -> All p ys -> All p (xs ++ ys)
allAppend AllNil           pys = pys
allAppend (AllCons px pxs) pys = AllCons px (allAppend pxs pys)

-- | Transforming element proofs under `All`.
allMap :: forall {a} {m1 :: Matchability} {m2 :: Matchability}
                 {p :: a %m1 -> Type} {q :: a %m2 -> Type} {xs}.
          (forall x. p x -> q x) -> All p xs -> All q xs
allMap _ AllNil           = AllNil
allMap f (AllCons px pxs) = AllCons (f px) (allMap f pxs)

-- | Inversion of `All` over append: `All p (xs ++ ys)` splits into `All p xs` and `All p ys`.
allAppendInv :: forall {a} {m :: Matchability} {p :: a %m -> Type} {ys}.
                foreach (xs :: List a) -> All p (xs ++ ys) -> Tuple2 (All p xs) (All p ys)
allAppendInv []     ays            = (AllNil, ays)
allAppendInv (_:xs) (AllCons px r) =
  case allAppendInv xs r of
    (axs, ays) -> (AllCons px axs, ays)

-- | Left introduction for `Any` over append.
anyAppendL :: forall a {m :: Matchability} (p :: a %m -> Type) (xs :: List a) (ys :: List a).
              Any p xs -> Any p (xs ++ ys)
anyAppendL (Here px) = Here px
anyAppendL (There r) = There (anyAppendL @a @p @_ @ys r)

-- | Right introduction for `Any` over append.
anyAppendR :: forall a {m :: Matchability} (p :: a %m -> Type) (ys :: List a).
              foreach (xs :: List a) -> Any p ys -> Any p (xs ++ ys)
anyAppendR []     ays = ays
anyAppendR (x:xs) ays = There @p @(xs ++ ys) @x (anyAppendR @a @p @ys xs ays)

-- | Inversion of `Any` over append: `Any p (xs ++ ys)` comes from `xs` or `ys`.
anyAppendInv :: forall {a} {m :: Matchability} {p :: a %m -> Type} {ys}.
                foreach (xs :: List a) -> Any p (xs ++ ys) -> Either (Any p xs) (Any p ys)
anyAppendInv []     ays       = Right ays
anyAppendInv (_:_)  (Here px) = Left (Here px)
anyAppendInv (_:xs) (There r) =
  case anyAppendInv xs r of
    Left  axs -> Left (There axs)
    Right ays -> Right ays
```

### De Morgan's Law for `Any` and `All` (`¬Any ⇔ All ¬`)

Because `All` and `Any` are matchability-polymorphic (`p :: a %m -> Type`),
PLFA's De Morgan equivalence between `Not (Any p xs)` and
`All (\x -> Not (p x)) xs` checks directly using an inline type-level lambda!

```haskell
mkNotHere :: forall {a} {m :: Matchability} {p :: a %m -> Type} {x} {xs}.
             Not (Any p (x : xs)) -> Not (p x)
mkNotHere nany px = nany (Here px)

-- | De Morgan forward: `¬(Any p xs) -> All (¬ ∘ p) xs` using an inline type lambda!
notAnyToAllNot :: forall {a} {m :: Matchability} (p :: a %m -> Type).
                  foreach (xs :: List a) -> Not (Any p xs) -> All (\x -> Not (p x)) xs
notAnyToAllNot []     _    = AllNil
notAnyToAllNot (_:xs) nany =
  AllCons (mkNotHere nany) (notAnyToAllNot @p xs (\anyXs -> nany (There anyXs)))

-- | De Morgan backward: `All (¬ ∘ p) xs -> ¬(Any p xs)`.
allNotToNotAny :: forall {a} {m :: Matchability} (p :: a %m -> Type) (xs :: List a).
                  All (\x -> Not (p x)) xs -> Not (Any p xs)
allNotToNotAny (AllCons npx _) (Here px) = npx px
allNotToNotAny (AllCons _ nxs) (There r) = allNotToNotAny @p nxs r

-- | Full De Morgan bi-implication (`¬Any⇔All¬`): `Not (Any p xs) ⇔ All (\x -> Not (p x)) xs`.
notAnyIffAllNot :: forall {a} {m :: Matchability} (p :: a %m -> Type).
                   foreach (xs :: List a) -> Iff (Not (Any p xs)) (All (\x -> Not (p x)) xs)
notAnyIffAllNot [] = Iff (\_ -> AllNil) (\_ anyNil -> case anyNil of {})
notAnyIffAllNot (_:xs) = case notAnyIffAllNot @p xs of
  Iff toTail fromTail ->
    Iff (\nany -> AllCons (mkNotHere nany) (toTail (\r -> nany (There r))))
        (\case AllCons npx nxs -> \case { Here px -> npx px; There r -> fromTail nxs r })
```

### An explicit witness for `Any` (`Any-∃`)

An `Any p xs` proof marks a position in `xs` and carries evidence for the
element at that position. We can unpack this proof into an existential index
`x`, a proof that `x` occurs in `xs`, and a proof of `p x`. Because the
membership proof remembers *which* occurrence we selected, `memberValue`
recovers that element from the list without comparing elements:

```haskell
-- | Evidence that a member of the list satisfies the predicate.
type AnyWitness :: forall {a} {m :: Matchability}. (a %m -> Type) -> List a -> Type
data AnyWitness p xs where
  MkAnyWitness :: forall {a} {m :: Matchability} {p :: a %m -> Type} {x} {xs}.
                  In x xs -> p x -> AnyWitness p xs

anyToWitness :: forall {a} {m :: Matchability} {p :: a %m -> Type} {xs}.
                Any p xs -> AnyWitness p xs
anyToWitness (Here px) = MkAnyWitness (Here Refl) px
anyToWitness (There r) = case anyToWitness r of
  MkAnyWitness member px -> MkAnyWitness (There member) px

witnessToAny :: forall {a} {m :: Matchability} {p :: a %m -> Type} {xs}.
                AnyWitness p xs -> Any p xs
witnessToAny (MkAnyWitness (Here Refl) px) = Here px
witnessToAny (MkAnyWitness (There member) px) =
  There (witnessToAny (MkAnyWitness member px))

-- | `Any` holds exactly when a list member satisfies the predicate (`Any-∃`).
anyIffWitness :: forall {a} {m :: Matchability} (p :: a %m -> Type) (xs :: List a).
                 Iff (Any p xs) (AnyWitness p xs)
anyIffWitness = Iff anyToWitness witnessToAny

-- | Read the element at the position selected by a membership proof.
memberValue :: forall a (x :: a). foreach (xs :: List a) -> In x xs -> a
memberValue []       r           = case r of {}
memberValue (x : _)  (Here Refl) = x
memberValue (_ : xs) (There r)   = memberValue xs r
```

Because `PLFH.Part1.Lists` compiles with `-XDependentTypes`, GHC automatically
publishes checked equations for `witnessToAny` and `anyToWitness` into
`Lists.hi`! Downstream clients prove both:

- `PLFH.Part1.ListsProof` (`clients/PLFH/Part1/ListsProof.hs`): polymorphic
  head/tail decoding (`witnessToAnyHere`, `witnessToAnyThere`) and
  retained-`foreach` tail preservation (`witnessToAnyEvenThere`) with zero
  promoted-constructor ticks; and
- `PLFH.Part1.AnyWitnessIso` (`clients/PLFH/Part1/AnyWitnessIso.hs`): the
  **full polymorphic isomorphism** `anyIsoWitness :: Iso (Any p xs) (AnyWitness p xs)`
  proving *both* inverse laws (`witnessToAny (anyToWitness r) :~: r` and
  `anyToWitness (witnessToAny w) :~: w`) directly over the ordinary `Lists`
  converters!

### Decidability of `All` and `Any` (`All?`, `Any?`), and concrete examples

If a predicate `p` is decidable (`foreach (x :: a) -> Dec (p x)`), then both
`All p xs` and `Any p xs` are decidable for every finite list `xs`:

```haskell
-- | Pointwise characterization of `All`: if `p` holds for all elements of `xs`
-- and `x ∈ xs`, then `p x` (`All-to-∈`).
allToIn :: forall {a} {m :: Matchability} {p :: a %m -> Type} {x} {xs}.
           All p xs -> In x xs -> p x
allToIn (AllCons px _)   (Here Refl) = px
allToIn (AllCons _  pxs) (There r)   = allToIn pxs r

-- | Converse (`∈-to-All`): if `p x` holds for every member `x ∈ xs`, then `All p xs`.
inToAll :: forall {a} {m :: Matchability} {p :: a %m -> Type}.
           foreach (xs :: List a) -> (forall (x :: a). In x xs -> p x) -> All p xs
inToAll []       _ = AllNil
inToAll (x : xs) f = AllCons (f @x (Here Refl)) (inToAll xs (\r -> f (There r)))

-- | Decidability of universal list quantification `All p xs` (`All?`).
decAll :: forall {a} {m :: Matchability} {p :: a %m -> Type}.
          (foreach (x :: a) -> Dec (p x)) -> foreach (xs :: List a) -> Dec (All p xs)
decAll _ []       = Yes AllNil
decAll d (x : xs) = case d x of
  No npx -> No (\case AllCons px _ -> npx px)
  Yes px -> case decAll d xs of
    Yes axs -> Yes (AllCons px axs)
    No naxs -> No (\case AllCons _ axs -> naxs axs)

-- | Decidability of existential list quantification `Any p xs` (`Any?`).
decAny :: forall {a} {m :: Matchability} {p :: a %m -> Type}.
          (foreach (x :: a) -> Dec (p x)) -> foreach (xs :: List a) -> Dec (Any p xs)
decAny _ []       = No (\case {})
decAny d (x : xs) = case d x of
  Yes px  -> Yes (Here px)
  No  npx -> case decAny d xs of
    Yes axs -> Yes (There axs)
    No naxs -> No (\case Here px -> npx px; There axs -> naxs axs)

-- | Decidability of list membership `In x xs` given decidable element equality (`∈?`).
decIn :: forall {a}.
         (foreach (x y :: a) -> Dec (x :~: y))
      -> foreach (x :: a) -> foreach (xs :: List a) -> Dec (In x xs)
decIn _     _ []       = No (\case {})
decIn decEq x (y : ys) = case decEq x y of
  Yes Refl -> Yes (Here Refl)
  No  neq  -> case decIn decEq x ys of
    Yes iys -> Yes (There iys)
    No niys -> No (\case { Here eq -> neq eq; There r -> niys r })

-- | Concrete membership proof: 0 ∈ [0, 1, 0].
zeroInList :: In (0 :: Nat) [0 :: Nat, 1 :: Nat, 0 :: Nat]
zeroInList = Here Refl

-- | Concrete non-membership proof: 3 ∉ [0, 1, 0, 2].
threeNotInList :: Not (In (3 :: Nat) [0 :: Nat, 1 :: Nat, 0 :: Nat, 2 :: Nat])
threeNotInList (Here eq)                          = case eq of {}
threeNotInList (There (Here eq))                  = case eq of {}
threeNotInList (There (There (Here eq)))          = case eq of {}
threeNotInList (There (There (There (Here eq))))  = case eq of {}
threeNotInList (There (There (There (There p))))  = case p of {}
```

## Exercises

#### Exercise `map-Tree` and `fold-Tree` (practice)

Define binary trees `data Tree a b = Leaf a | Node (Tree a b) b (Tree a b)`
and write `mapTree :: (a -> c) -> (b -> d) -> Tree a b -> Tree c d` and
`foldTree :: (a -> c) -> (c -> b -> c -> c) -> Tree a b -> c`.

#### Exercise `All-∀` and `Any-∃` (practice)

The two directions of `All-∀` are checked above as `allToIn` and `inToAll`,
and `anyIffWitness` packages both directions of `Any-∃`. Trace `anyIffWitness`
on a list with repeated elements such as `[1, 2, 1, 2]`: which occurrence does
the membership proof identify?

#### Exercise `split` (stretch)

Using `decAll`, `decAny`, and an inductive `Merge xs ys zs` relation
(`MergeNil`, `MergeL`, `MergeR`), design a certified list-filtering function
that splits a list `zs` into the elements satisfying `p` and those satisfying
`\x -> Not (p x)` together with a `Merge` proof!

## Changes from PLFA

- Adapted from [Lists](https://plfa.inf.ed.ac.uk/Lists/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part1/Lists.lagda.md)),
  licensed under CC BY 4.0.
- Used standard Prelude lists (`GHC.Types.List`), `(++)`, and `map` directly,
  with `-XNoListTuplePuns` so promoted `[]`, `:`, and `[0, 1, 0]` require
  zero leading `'` ticks!
- Reused `dependent-base`'s `size`, `foldr`, and `lengthReverse` (`Data.List.Dependent` / `Data.List.Dependent.Properties`).
- Made `All` and `Any` matchability-polymorphic (`p :: a %m -> Type`),
  unlocking PLFA's full inline type-lambda De Morgan theorem
  (`notAnyToAllNot`, `allNotToNotAny`, `notAnyIffAllNot`).
- Ports `appendAssoc`, `appendNilR`, `mapAppend`,
  `mapCompose`, `mapId`, `shunt`/`shuntAppend`, `rev`/`revAppend`/
  `revInvolutive`/`shuntRev`/`reverses`, `downFrom`/`zeros`/
  `lengthDownFrom`/`lengthZeros`, `foldrPlusSeed`/`foldrPlusAppend` over
  `Data.List.Dependent.foldr`, `All`, `Any`, `In`, `allAppend`/`Inv`,
  `anyAppend*`/`Inv`, `allMap`, `notAnyIffAllNot`, `allToIn`, `inToAll`,
  `decAll`, `decAny`, `decIn`, `zeroInList`, and `threeNotInList`.
- Documented GHC's intentional `-O2` list-fusion soundness guard on `mapAppend`
  (`-fno-enable-rewrite-rules`).
