---
title: "dependent-base Reference"
description: "Complete typed API reference for TharkunAB/dependent-base: Prelude.Dependent, Data.Function.Dependent, Data.Type.Equality.Dependent, Data.Nat.Dependent, Data.List.Dependent, Data.Vec.Dependent, Data.Fin.Dependent, Sigma, Exists, Decision, and Prelude type laws."
prev: /contextualequivalence/
next: /source/
src: content/DependentBase.md
---

[`TharkunAB/dependent-base`](https://github.com/TharkunAB/dependent-base) is
the Dependent Haskell standard library for
[`TharkunAB/ghc`](https://github.com/TharkunAB/ghc/tree/dependent-haskell),
modeled on `linear-base` and `agda-prelude`. It works directly on stock
`Prelude` types (`Bool`, `Maybe`, `Either`, `(,)`, `[a]`, `(:~:)`, `Void`), and
plain `Haskell2010` modules can import its compiled `.hi` interfaces without
enabling `-XDependentTypes`.

Every module in `dependent-base` is precompiled into the browser WebAssembly
bundle and available in PLFH's interactive GHCi sessions.

## How `dependent-base` reuse relates to PLFA

In [*Programming Language Foundations in Agda*](https://plfa.inf.ed.ac.uk/)
(PLFA), `Naturals` defines `ℕ` and `_+_` from scratch, binds Agda's
`{-# BUILTIN NATURAL ℕ #-}` pragma for decimal numerals, and later chapters
switch to Agda's standard library (`Data.Nat`, `Data.List`,
`Relation.Binary.PropositionalEquality`).

In PLFH, Haskell datatypes are nominal and `Num Nat` / `FromNatural Nat`
instances are global. Reusing `Data.Nat.Dependent.Nat` and stock `Prelude`
`List a` keeps one shared `Nat` and one shared list type across all 25
chapters, while chapters such as [Induction](/induction/) and [Lists](/lists/)
still prove the inductive theorems (`plusIdentityR`, `plusSuc`, `plusAssoc`,
`plusComm`, `appendAssoc`, `lengthAppendLaw`, `lengthMapLaw`) inline.

## Interactive GHCi tips

Inspect any module in the browser GHCi prompt with `:browse Prelude.Dependent`,
`:browse Data.Nat.Dependent`, `:browse Data.Function.Dependent`,
`:browse Data.Vec.Dependent`, or `:browse PLFH.Part1.Naturals`.

`Data.Nat.Dependent.Nat` derives `Show` (printing `Succ (Succ Zero)`) and
provides `Num Nat` / `FromNatural Nat` for decimal literals (`2 :: Nat`). Use
`natToInt` or `natToInteger` to print a Peano natural in decimal:

```text
ghci> natToInt (plus 2 3)
5
```

## Module index and exported API

- [`Prelude.Dependent`](#preludedependent)
- [`Data.Function.Dependent`](#datafunctiondependent)
- [`Data.Type.Equality.Dependent`](#datatypeequalitydependent)
- [`Data.Nat.Dependent`](#datanatdependent) &middot; [`Data.Nat.Dependent.Properties`](#datanatdependentproperties)
- [`Data.List.Dependent`](#datalistdependent) &middot; [`Data.List.Dependent.Properties`](#datalistdependentproperties) &middot; [`Data.List.Dependent.All`](#datalistdependentall)
- [`Data.Vec.Dependent`](#datavecdependent) &middot; [`Data.Vec.Dependent.Properties`](#datavecdependentproperties)
- [`Data.Fin.Dependent`](#datafindependent)
- [`Data.Sigma.Dependent`](#datasigmadependent) &middot; [`Data.Exists.Dependent`](#dataexistsdependent)
- [`Data.Decision`](#datadecision)
- [`Data.Bool.Dependent`](#databooldependent) &middot; [`Data.Maybe.Dependent`](#datamaybedependent) &middot; [`Data.Either.Dependent`](#dataeitherdependent) &middot; [`Data.Tuple.Dependent`](#datatupledependent)

---

### `Prelude.Dependent` {#preludedependent}

Source: [on-site `Prelude/Dependent.hs`](/source/dependent-base/prelude/dependent/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Prelude/Dependent.hs)

Umbrella prelude re-exporting core `base` types and classes (`Type`,
`Matchability (..)`, `M`, `U`, `Eq (..)`, `Ord (..)`, `Show (..)`, `Num (..)`,
`Int`, `Integer`, `Char`, `String`, `Ordering (..)`) together with the primary
operations and types from all `Data.*.Dependent` modules and `Data.Decision`.
Every re-exported symbol's exact type appears in its defining module below.

---

### `Data.Function.Dependent` {#datafunctiondependent}

Source: [on-site `Data/Function/Dependent.hs`](/source/dependent-base/data/function/dependent/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/Function/Dependent.hs)

Dependent and matchability-polymorphic function combinators that generalize
ordinary `Prelude` operations without breaking non-dependent call sites.

```haskell
infixr 9 .
(.) :: forall {a} {b} {m :: Matchability} (c :: b %m -> Type).
       (foreach (y :: b) -> c y)
    -> foreach (f :: a -> b)
    -> foreach (x :: a)
    -> c (f x)

composeDep :: forall {a} {mb :: Matchability} {b :: a %mb -> Type}
                     {mc :: Matchability} (c :: a %mc -> Type).
              (foreach (x :: a) -> b x -> c x)
           -> (foreach (x :: a) -> b x)
           -> foreach (x :: a)
           -> c x

composeSigma :: forall {a} (b :: a %U -> Type) {d}.
                (Sigma a b -> d)
             -> (foreach (x :: a) -> b x)
             -> foreach (x :: a)
             -> d

infixr 0 $
($) :: forall {a} {m :: Matchability} (b :: a %m -> Type).
       (foreach (x :: a) -> b x)
    -> foreach (x :: a)
    -> b x

applyDep :: forall {a} {m :: Matchability} (b :: a %m -> Type).
            (foreach (x :: a) -> b x)
         -> foreach (x :: a)
         -> b x

id       :: a -> a
idDep    :: forall {a}. foreach (x :: a) -> a
const    :: a -> b -> a
constDep :: forall {a} {b}. a -> foreach (y :: b) -> a
flip     :: (a -> b -> c) -> b -> a -> c

flipDep :: forall {a} {b} {m :: Matchability} (c :: a %U -> b %m -> Type).
           (foreach (x :: a) -> foreach (y :: b) -> c x y)
        -> foreach (y :: b)
        -> foreach (x :: a)
        -> c x y

infixl 0 `on`
on :: forall a b c. (b -> b -> c) -> (a -> b) -> a -> a -> c
```

---

### `Data.Type.Equality.Dependent` {#datatypeequalitydependent}

Source: [on-site `Data/Type/Equality/Dependent.hs`](/source/dependent-base/data/type/equality/dependent/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/Type/Equality/Dependent.hs)

Propositional equality, visible matchability-polymorphic congruence,
substitution, ASCII equational reasoning, and the `Inspect` view idiom.

```haskell
-- Re-exported equality and matchability types
data (a :: k) :~: (b :: k) where
  Refl :: a :~: a

data (a :: k1) :~~: (b :: k2) where
  HRefl :: a :~~: a

type (~) :: forall {k}. k -> k -> Constraint
data Matchability = Matchable | Unmatchable
type M = Matchable
type U = Unmatchable

-- Symmetry, transitivity, and transport
sym       :: (a :~: b) -> (b :~: a)
trans     :: (a :~: b) -> (b :~: c) -> (a :~: c)
castWith  :: (a :~: b) -> a -> b
gcastWith :: (a :~: b) -> ((a ~ b) => r) -> r

-- Visible matchability-polymorphic congruence
cong :: forall {a} {b} {m :: Matchability}.
        forall (f :: a %m -> b)
     -> forall (x :: a) (y :: a).
        x :~: y -> f x :~: f y

cong2 :: forall {a} {b} {c} {m1 :: Matchability} {m2 :: Matchability}.
         forall (f :: a %m1 -> b %m2 -> c)
      -> forall (x1 :: a) (y1 :: a) (x2 :: b) (y2 :: b).
         x1 :~: y1 -> x2 :~: y2 -> f x1 x2 :~: f y1 y2

congApp :: forall {a} {b} {m :: Matchability} {f :: a %m -> b} {g :: a %m -> b} (x :: a).
           f :~: g -> f x :~: g x

-- Substitution and local rewriting
subst :: forall {k} {m :: Matchability}.
         forall (p :: k %m -> Type)
      -> forall {x :: k} {y :: k}.
         x :~: y -> p x -> p y

substImplicit :: forall {k} {m :: Matchability} (p :: k %m -> Type) {x :: k} {y :: k}.
                 x :~: y -> p x -> p y

rewrite      :: forall {k} (a :: k) (b :: k) r. (a :~: b) -> ((a ~ b) => r) -> r
withEquality :: forall {k} (a :: k) (b :: k) r. (a :~: b) -> ((a ~ b) => r) -> r

-- ASCII equational reasoning
begin    :: forall {k} (x :: k) (y :: k). (x :~: y) -> (x :~: y)
stepEq   :: forall {k} (y :: k) {x :: k} {z :: k}. (x :~: y) -> (y :~: z) -> (x :~: z)  -- infixr 2
stepRefl :: forall {k} (x :: k) (y :: k). (x :~: y) -> (x :~: y)
(===)    :: forall {k} (x :: k) (y :: k) (z :: k). (x :~: y) -> (y :~: z) -> (x :~: z)  -- infixr 2
qed      :: forall {k} (x :: k). x :~: x

-- Inspect view idiom
data Inspect (lhs :: b) where
  Reveal :: foreach (y :: b) -> (lhs :~: y) -> Inspect lhs

inspect :: forall {a} {b}. foreach (f :: a -> b) -> foreach (x :: a) -> Inspect (f x)
```

---

### `Data.Nat.Dependent` {#datanatdependent}

Source: [on-site `Data/Nat/Dependent.hs`](/source/dependent-base/data/nat/dependent/) ·
[`Internal.hs`](/source/dependent-base/data/nat/dependent/internal/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/Nat/Dependent.hs)

Peano natural numbers (`Nat`) with `Eq`, `Ord`, `Show`, `Num`, and
`FromNatural` numeral literals (`0`, `1`, `2`, ...), total structural
arithmetic with checked open source equations, and inductive ordering
relations.

```haskell
data Nat = Zero | Succ Nat  -- deriving (Eq, Ord, Show); instances Num Nat, FromNatural Nat
type Size = Nat

infixl 6 type +
type (m :: Nat) + (n :: Nat) = plus m n

plus       :: Nat -> Nat -> Nat
mul        :: Nat -> Nat -> Nat
minus      :: Nat -> Nat -> Nat
minNat     :: Nat -> Nat -> Nat
maxNat     :: Nat -> Nat -> Nat
minSize    :: Nat -> Nat -> Nat
eqNat      :: Nat -> Nat -> Bool
eqSize     :: Nat -> Nat -> Bool
compareNat :: Nat -> Nat -> Ordering

natToInt     :: Nat -> Int
natToInteger :: Nat -> Integer

data LE (m :: Nat) (n :: Nat) where
  LEZero :: forall {n :: Nat}. LE Zero n
  LESucc :: forall {m :: Nat} {n :: Nat}. LE m n -> LE (Succ m) (Succ n)

type LTNat (m :: Nat) (n :: Nat) = LE (Succ m) n
```

### `Data.Nat.Dependent.Properties` {#datanatdependentproperties}

Source: [on-site `Data/Nat/Dependent/Properties.hs`](/source/dependent-base/data/nat/dependent/properties/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/Nat/Dependent/Properties.hs)

Arithmetic and order lemmas for Peano naturals.

```haskell
congSucc      :: forall (m :: Nat) (n :: Nat). m :~: n -> Succ m :~: Succ n
congFirst     :: forall (f :: Nat %U -> Nat %U -> Nat) r m n. m :~: n -> f m r :~: f n r
succInjective :: forall {m :: Nat} {n :: Nat}. Succ m :~: Succ n -> m :~: n
eqSizeRefl    :: foreach (n :: Nat) -> eqSize n n :~: True
eqNatRefl     :: foreach (n :: Nat) -> eqSize n n :~: True

-- Addition
plusZero  :: foreach (m :: Nat) -> plus m Zero :~: m
plusSucc  :: foreach (m :: Nat) -> foreach (n :: Nat) -> plus m (Succ n) :~: Succ (plus m n)
plusAssoc :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
          -> plus (plus m n) p :~: plus m (plus n p)
plusComm  :: foreach (m :: Nat) -> foreach (n :: Nat) -> plus m n :~: plus n m

-- Multiplication
mulZero     :: foreach (m :: Nat) -> mul m Zero :~: Zero
mulSucc     :: foreach (m :: Nat) -> foreach (n :: Nat) -> mul m (Succ n) :~: plus m (mul m n)
mulOneL     :: foreach (n :: Nat) -> mul (Succ Zero) n :~: n
mulOneR     :: foreach (m :: Nat) -> mul m (Succ Zero) :~: m
mulDistribR :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
            -> mul (plus m n) p :~: plus (mul m p) (mul n p)
mulDistribL :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
            -> mul m (plus n p) :~: plus (mul m n) (mul m p)
mulAssoc    :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
            -> mul (mul m n) p :~: mul m (mul n p)
mulComm     :: foreach (m :: Nat) -> foreach (n :: Nat) -> mul m n :~: mul n m

-- Truncated subtraction (monus)
minusZeroR :: foreach (m :: Nat) -> minus m Zero :~: m
minusDiag  :: foreach (n :: Nat) -> minus n n :~: Zero

-- Order (LE)
leRefl    :: foreach (n :: Nat) -> LE n n
leTrans   :: forall {m :: Nat} {n :: Nat} {p :: Nat}. LE m n -> LE n p -> LE m p
leAntisym :: forall {m :: Nat} {n :: Nat}. LE m n -> LE n m -> m :~: n
leSuccR   :: forall {m :: Nat} {n :: Nat}. LE m n -> LE m (Succ n)
invLESucc :: forall {m :: Nat} {n :: Nat}. LE (Succ m) (Succ n) -> LE m n
decLE     :: foreach (m :: Nat) -> foreach (n :: Nat) -> Dec (LE m n)
```

---

### `Data.List.Dependent` {#datalistdependent}

Source: [on-site `Data/List/Dependent.hs`](/source/dependent-base/data/list/dependent/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/List/Dependent.hs)

Certified total operations directly over stock `Prelude` lists `[a]`.

```haskell
size         :: forall a. [a] -> Nat
lengthNat    :: forall a. [a] -> Nat
(++)         :: [a] -> [a] -> [a]
append       :: forall a. [a] -> [a] -> [a]
map          :: (a -> b) -> [a] -> [b]
foldr        :: (a -> b -> b) -> b -> [a] -> b
zip          :: [a] -> [b] -> [(a, b)]
zipWith      :: (a -> b -> c) -> [a] -> [b] -> [c]
reverse      :: [a] -> [a]
shunt        :: forall a. [a] -> [a] -> [a]
reverseShunt :: forall a. [a] -> [a]
takeSize     :: forall a. Nat -> [a] -> [a]
```

### `Data.List.Dependent.Properties` {#datalistdependentproperties}

Source: [on-site `Data/List/Dependent/Properties.hs`](/source/dependent-base/data/list/dependent/properties/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/List/Dependent/Properties.hs)

Length, concatenation, functor, zip, and reversal laws for stock lists.

```haskell
consCong :: forall {a}. foreach (x :: a)
         -> forall {xs :: [a]} {ys :: [a]}. xs :~: ys -> (x : xs) :~: (x : ys)

appendNilR  :: forall a. foreach (xs :: [a]) -> (xs ++ '[]) :~: xs
appendAssoc :: forall a. foreach (xs :: [a]) -> foreach (ys :: [a]) -> foreach (zs :: [a])
            -> ((xs ++ ys) ++ zs) :~: (xs ++ (ys ++ zs))

mapId      :: forall a. foreach (xs :: [a]) -> map id xs :~: xs
mapCompose :: forall a b c. foreach (g :: b -> c) -> foreach (f :: a -> b) -> foreach (xs :: [a])
           -> map (g . f) xs :~: map g (map f xs)
mapAppend  :: forall a b. foreach (f :: a -> b) -> foreach (xs :: [a]) -> foreach (ys :: [a])
           -> map f (xs ++ ys) :~: (map f xs ++ map f ys)

lengthAppend     :: forall a. foreach (xs :: [a]) -> foreach (ys :: [a])
                 -> size (xs ++ ys) :~: plus (size xs) (size ys)
lengthAppendList :: forall a. foreach (xs :: [a]) -> foreach (ys :: [a])
                 -> size (append xs ys) :~: plus (size xs) (size ys)
lengthMap        :: forall a b. foreach (f :: a -> b) -> foreach (xs :: [a])
                 -> size (map f xs) :~: size xs
lengthZip        :: forall a b. foreach (xs :: [a]) -> foreach (ys :: [b])
                 -> size (zip xs ys) :~: minSize (size xs) (size ys)
lengthZipWith    :: forall a b c. foreach (f :: a -> b -> c) -> foreach (xs :: [a]) -> foreach (ys :: [b])
                 -> size (zipWith f xs ys) :~: minSize (size xs) (size ys)
lengthZipMap     :: forall a b c d. foreach (pre :: a -> b) -> foreach (combine :: b -> c -> d)
                 -> foreach (xs :: [a]) -> foreach (ys :: [c])
                 -> size (zipWith combine (map pre xs) ys) :~: minSize (size xs) (size ys)
lengthMapZip     :: forall a b c. foreach (f :: (a, b) -> c) -> foreach (xs :: [a]) -> foreach (ys :: [b])
                 -> size (map f (zip xs ys)) :~: minSize (size xs) (size ys)

lengthReverse          :: forall a. foreach (xs :: [a]) -> size (reverse xs) :~: size xs
lengthShunt            :: forall a. foreach (xs :: [a]) -> foreach (acc :: [a])
                       -> size (shunt xs acc) :~: plus (size xs) (size acc)
lengthReverseShunt     :: forall a. foreach (xs :: [a]) -> size (reverseShunt xs) :~: size xs
shuntAppend            :: forall a. foreach (xs :: [a]) -> foreach (ys :: [a])
                       -> shunt xs ys :~: (reverseShunt xs ++ ys)
reverseShuntInvolutive :: forall a. foreach (xs :: [a]) -> reverseShunt (reverseShunt xs) :~: xs
lengthTakeSize         :: forall a. foreach (n :: Nat) -> foreach (xs :: [a])
                       -> size (takeSize n xs) :~: minSize n (size xs)
```

### `Data.List.Dependent.All` {#datalistdependentall}

Source: [on-site `Data/List/Dependent/All.hs`](/source/dependent-base/data/list/dependent/all/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/List/Dependent/All.hs)

Matchability-polymorphic universal (`All`) and existential (`Any`) list
predicates, typed list membership (`Elem`), and decision procedures.

```haskell
type All :: forall {a} {m :: Matchability}. (a %m -> Type) -> [a] -> Type
data All p xs where
  AllNil  :: forall {a} {m :: Matchability} {p :: a %m -> Type}. All p '[]
  AllCons :: forall {a} {m :: Matchability} {p :: a %m -> Type} {x :: a} {xs :: [a]}.
             p x -> All p xs -> All p (x : xs)

type Any :: forall {a} {m :: Matchability}. (a %m -> Type) -> [a] -> Type
data Any p xs where
  Here  :: forall {a} {m :: Matchability} {p :: a %m -> Type} {x :: a} {xs :: [a]}.
           p x -> Any p (x : xs)
  There :: forall {a} {m :: Matchability} {p :: a %m -> Type} {x :: a} {xs :: [a]}.
           Any p xs -> Any p (x : xs)

type Elem :: forall {a}. a -> [a] -> Type
type Elem x xs = Any ((:~:) x) xs

lookupAll :: forall {a} {m :: Matchability} {p :: a %m -> Type} {x :: a} {xs :: [a]}.
             All p xs -> Elem x xs -> p x

tabulateAll :: forall {a} {m :: Matchability} {p :: a %m -> Type}.
               foreach (xs :: [a]) -> (forall (x :: a). Elem x xs -> p x) -> All p xs

mapAll :: forall {a} {m1 :: Matchability} {m2 :: Matchability}
                 {p :: a %m1 -> Type} {q :: a %m2 -> Type} {xs :: [a]}.
          (forall {x :: a}. p x -> q x) -> All p xs -> All q xs

mapAny :: forall {a} {m1 :: Matchability} {m2 :: Matchability}
                 {p :: a %m1 -> Type} {q :: a %m2 -> Type} {xs :: [a]}.
          (forall {x :: a}. p x -> q x) -> Any p xs -> Any q xs

allAppend :: forall {a} {m :: Matchability} {p :: a %m -> Type} {xs :: [a]} {ys :: [a]}.
             All p xs -> All p ys -> All p (xs ++ ys)

splitAllAppend :: forall {a} {m :: Matchability} {p :: a %m -> Type} (ys :: [a]).
                  foreach (xs :: [a]) -> All p (xs ++ ys) -> (All p xs, All p ys)

decAll  :: forall {a} {m :: Matchability} {p :: a %m -> Type}.
           (foreach (x :: a) -> Dec (p x)) -> foreach (xs :: [a]) -> Dec (All p xs)
decAny  :: forall {a} {m :: Matchability} {p :: a %m -> Type}.
           (foreach (x :: a) -> Dec (p x)) -> foreach (xs :: [a]) -> Dec (Any p xs)
decElem :: forall {a}. DecEq a
        => foreach (x :: a) -> foreach (xs :: [a]) -> Dec (Elem x xs)
```

---

### `Data.Vec.Dependent` {#datavecdependent}

Source: [on-site `Data/Vec/Dependent.hs`](/source/dependent-base/data/vec/dependent/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/Vec/Dependent.hs)

Length-indexed vectors (`Vec`), total `Fin`-indexed lookup and update, and
verified adapters to and from stock `[a]`.

```haskell
data Vec a (n :: Nat) where
  VNil  :: Vec a Zero
  VCons :: a -> Vec a n -> Vec a (Succ n)

type SomeVec a = some (n :: Nat) | Vec a n

headVec       :: Vec a (Succ n) -> a
tailVec       :: Vec a (Succ n) -> Vec a n
snocVec       :: Vec a n -> a -> Vec a (Succ n)
initVec       :: Vec a (Succ n) -> Vec a n
lastVec       :: Vec a (Succ n) -> a
appendVec     :: Vec a n -> Vec a m -> Vec a (plus n m)
mapVec        :: (a -> b) -> Vec a n -> Vec b n
zipVec        :: Vec a n -> Vec b n -> Vec (a, b) n
zipWithVec    :: (a -> b -> c) -> Vec a n -> Vec b n -> Vec c n
replicateVec  :: forall a. foreach (n :: Nat) -> a -> Vec a n
lookupVec     :: Fin n -> Vec a n -> a
mkFinVec      :: Vec a n -> Int -> Maybe (Fin n)
tabulateVec   :: foreach (n :: Nat) -> (Fin n -> a) -> Vec a n
updateAtVec   :: Fin n -> (a -> a) -> Vec a n -> Vec a n
reverseVec    :: Vec a n -> Vec a n
foldrVec      :: (a -> b -> b) -> b -> Vec a n -> b
toListVec     :: Vec a n -> [a]
fromListVec   :: forall a. foreach (xs :: [a]) -> Vec a (size xs)
fromListExact :: foreach (n :: Nat) -> [a] -> Maybe (Vec a n)
packListVec   :: [a] -> SomeVec a
```

### `Data.Vec.Dependent.Properties` {#datavecdependentproperties}

Source: [on-site `Data/Vec/Dependent/Properties.hs`](/source/dependent-base/data/vec/dependent/properties/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/Vec/Dependent/Properties.hs)

Congruence, concatenation, and splitting laws for `Vec`.

```haskell
type SplitVec a (n :: Nat) (m :: Nat) (xs :: Vec a (n + m)) =
  some (left :: Vec a n) | (some (right :: Vec a m) | appendVec left right :~: xs)

vconsCong :: forall {a} {n :: Nat}. foreach (x :: a)
          -> forall {xs :: Vec a n} {ys :: Vec a n}.
             xs :~: ys -> VCons x xs :~: VCons x ys

appendVecNilL :: forall {a} {n :: Nat}. foreach (xs :: Vec a n)
              -> appendVec VNil xs :~: xs

appendVecCons :: forall {a} {m :: Nat} {n :: Nat}.
                 foreach (x :: a) -> foreach (xs :: Vec a m) -> foreach (ys :: Vec a n)
              -> appendVec (VCons x xs) ys :~: VCons x (appendVec xs ys)

appendVecNilR :: forall a {n :: Nat}. foreach (xs :: Vec a n)
              -> appendVec xs (VNil :: Vec a Zero) :~~: xs

appendVecAssoc :: forall a {m :: Nat} {n :: Nat} {p :: Nat}.
                  foreach (xs :: Vec a m) -> foreach (ys :: Vec a n) -> foreach (zs :: Vec a p)
               -> appendVec (appendVec xs ys) zs :~~: appendVec xs (appendVec ys zs)

splitAtAppendVec :: forall a m.
                    foreach (n :: Nat) -> foreach (xs :: Vec a (plus n m))
                 -> SplitVec a n m xs
```

---

### `Data.Fin.Dependent` {#datafindependent}

Source: [on-site `Data/Fin/Dependent.hs`](/source/dependent-base/data/fin/dependent/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/Fin/Dependent.hs)

Bounded natural positions strictly below `n :: Nat` (distinct constructors `FZ`
and `FS`, no partial `Num` instance) with compile-time bounds-checked numerals
via `fin 1`, `#2` (`IsLabel` under `-XOverloadedLabels`), and `FromNatural (Fin n)`.

```haskell
data Fin (n :: Nat) where
  FZ :: Fin (Succ n)
  FS :: Fin n -> Fin (Succ n)

-- Compile-time bounds-checked Fin numerals (also instances IsLabel sym (Fin n), FromNatural (Fin n))
class KnownFin (k :: GHC.TypeNats.Nat) (n :: Nat) where
  finVal :: Fin n

fin :: forall (k :: GHC.TypeNats.Nat) -> forall {n :: Nat}. KnownFin k n => Fin n

-- Conversions and position combinators
finToNat      :: forall (n :: Nat). Fin n -> Nat
finToInt      :: forall (n :: Nat). Fin n -> Int
mkFin         :: foreach (n :: Nat) -> Int -> Maybe (Fin n)
weakenFin     :: forall (n :: Nat). Fin n -> Fin (Succ n)
shiftFin      :: forall (n :: Nat). foreach (m :: Nat) -> Fin n -> Fin (plus m n)
absurdFinZero :: forall a. Fin Zero -> a
lastFin       :: foreach (n :: Nat) -> Fin (Succ n)
oppositeFin   :: foreach (n :: Nat) -> Fin n -> Fin n
```

---

### `Data.Sigma.Dependent` {#datasigmadependent}

Source: [on-site `Data/Sigma/Dependent.hs`](/source/dependent-base/data/sigma/dependent/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/Sigma/Dependent.hs)

Retained dependent pairs (`some (x :: a) | p x`, backed by `GHC.Sigma.Sigma`)
and projection, mapping, and currying combinators.

```haskell
data Sigma (a :: Type) (p :: a %U -> Type) where
  Pair :: forall (a :: Type) (p :: a %U -> Type).
          foreach (x :: a) -> p x -> Sigma a p

first     :: Sigma a p -> a
second    :: foreach (p :: Sigma a b) -> b (first p)
withSigma :: Sigma a p -> (foreach (x :: a) -> p x -> r) -> r

mapSigma :: forall {a} {b} (p :: a %U -> Type) (q :: b %U -> Type).
            foreach (f :: a -> b) -> (foreach (x :: a) -> p x -> q (f x))
         -> Sigma a p -> Sigma b q

mapSigmaSecond :: forall {a} (p :: a %U -> Type) (q :: a %U -> Type).
                  (foreach (x :: a) -> p x -> q x)
               -> Sigma a p -> Sigma a q

currySigma   :: forall {a} (p :: a %U -> Type) {r}.
                (Sigma a p -> r) -> foreach (x :: a) -> p x -> r
uncurrySigma :: forall {a} (p :: a %U -> Type) {r}.
                (foreach (x :: a) -> p x -> r) -> Sigma a p -> r
```

### `Data.Exists.Dependent` {#dataexistsdependent}

Source: [on-site `Data/Exists/Dependent.hs`](/source/dependent-base/data/exists/dependent/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/Exists/Dependent.hs)

Proposal `#473` erased existential packages (`exists (x :: k) | p x`),
constraint pairing (`/\`), witness tokens (`Witness`), and elimination
combinators re-exported from `GHC.Exists`.

```haskell
-- Special existential pack syntax (`Pack (type x) payload`)
pattern Pack

infixr 2 /\
type (/\) :: Constraint -> Type -> Type
data c /\ a where
  MkCPair :: c => a -> c /\ a

discardEvidence :: (c /\ a) -> a
withEvidence    :: (c /\ a) -> (c => a -> r) -> r

type Witness :: forall {k}. k -> Type
data Witness a where
  Witness :: forall {k} (a :: k). Witness a

withExists :: forall {k} {m :: Matchability} (p :: k %m -> Type) r.
              (exists (x :: k) | p x) -> (forall (x :: k) -> p x -> r) -> r

mapExists :: forall {k} {mp :: Matchability} {mq :: Matchability}
                    (p :: k %mp -> Type) (q :: k %mq -> Type).
             (forall (x :: k) -> p x -> q x)
          -> (exists (x :: k) | p x) -> (exists (x :: k) | q x)

uncurryExists :: forall {k1} {k2} {m1 :: Matchability} {m2 :: Matchability}
                        (p :: k1 %m1 -> k2 %m2 -> Type) r.
                 (exists (x :: k1) (y :: k2) | p x y)
              -> (forall (x :: k1) (y :: k2) -> p x y -> r) -> r
```

---

### `Data.Decision` {#datadecision}

Source: [on-site `Data/Decision.hs`](/source/dependent-base/data/decision/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/Decision.hs)

Constructive decidability (`Dec`), Boolean reflection (`Reflects`),
propositional negation (`Not`), and certified decidable equality (`DecEq`, with
instances for `()`, `Bool`, `Ordering`, `Nat`, `Fin n`, `Maybe a`, `Either a b`,
`(a, b)`, `[a]`, and `Vec a n`).

```haskell
data Void                    -- uninhabited type from Data.Void
absurd :: Void -> a
type Not (p :: Type) = p -> Void

data Dec (p :: Type) = Yes p | No (Not p)
decToBool :: forall p. Dec p -> Bool

data Reflects (p :: Type) (b :: Bool) where
  OfTrue  :: forall {p}. p -> Reflects p True
  OfFalse :: forall {p}. Not p -> Reflects p False

data ReflectsBool (p :: Type) where
  ReflectTrue  :: forall {p}. p -> ReflectsBool p
  ReflectFalse :: forall {p}. Not p -> ReflectsBool p

decToReflectsBool :: forall p. Dec p -> ReflectsBool p
reflectsBoolToDec :: forall p. ReflectsBool p -> Dec p

decNot :: forall p. Dec p -> Dec (Not p)
decAnd :: forall p q. Dec p -> Dec q -> Dec (p, q)
decOr  :: forall p q. Dec p -> Dec q -> Dec (Either p q)
decImp :: forall p q. Dec p -> Dec q -> Dec (p -> q)

class DecEq a where
  decEq :: foreach (x :: a) -> foreach (y :: a) -> Dec (x :~: y)
```

---

### `Data.Bool.Dependent` {#databooldependent}

Source: [on-site `Data/Bool/Dependent.hs`](/source/dependent-base/data/bool/dependent/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/Bool/Dependent.hs)

Certified total Boolean operations and fundamental algebraic laws.

```haskell
data Bool = False | True
not       :: Bool -> Bool
(&&)      :: Bool -> Bool -> Bool
(||)      :: Bool -> Bool -> Bool
otherwise :: Bool
bool      :: forall a. a -> a -> Bool -> a

notInvolutive :: foreach (b :: Bool) -> not (not b) :~: b
andTrueL      :: foreach (b :: Bool) -> (True && b) :~: b
andTrueR      :: foreach (b :: Bool) -> (b && True) :~: b
andFalseR     :: foreach (b :: Bool) -> (b && False) :~: False
orFalseL      :: foreach (b :: Bool) -> (False || b) :~: b
orFalseR      :: foreach (b :: Bool) -> (b || False) :~: b
orTrueR       :: foreach (b :: Bool) -> (b || True) :~: True
andAssoc      :: foreach (x :: Bool) -> foreach (y :: Bool) -> foreach (z :: Bool)
              -> ((x && y) && z) :~: (x && (y && z))
orAssoc       :: foreach (x :: Bool) -> foreach (y :: Bool) -> foreach (z :: Bool)
              -> ((x || y) || z) :~: (x || (y || z))
andComm       :: foreach (x :: Bool) -> foreach (y :: Bool) -> (x && y) :~: (y && x)
orComm        :: foreach (x :: Bool) -> foreach (y :: Bool) -> (x || y) :~: (y || x)
deMorganAnd   :: foreach (x :: Bool) -> foreach (y :: Bool) -> not (x && y) :~: (not x || not y)
deMorganOr    :: foreach (x :: Bool) -> foreach (y :: Bool) -> not (x || y) :~: (not x && not y)
```

### `Data.Maybe.Dependent` {#datamaybedependent}

Source: [on-site `Data/Maybe/Dependent.hs`](/source/dependent-base/data/maybe/dependent/) ·
[`Internal.hs`](/source/dependent-base/data/maybe/dependent/internal/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/Maybe/Dependent.hs)

Certified `Maybe` operations with functor and list round-trip laws.

```haskell
data Maybe a = Nothing | Just a
maybe       :: forall a b. b -> (a -> b) -> Maybe a -> b
fromMaybe   :: forall a. a -> Maybe a -> a
isJust      :: forall a. Maybe a -> Bool
isNothing   :: forall a. Maybe a -> Bool
fmapMaybe   :: forall a b. (a -> b) -> Maybe a -> Maybe b
maybeToList :: forall a. Maybe a -> [a]
listToMaybe :: forall a. [a] -> Maybe a
mapMaybe    :: forall a b. (a -> Maybe b) -> [a] -> [b]
catMaybes   :: forall a. [Maybe a] -> [a]

fmapMaybeId            :: forall a. foreach (mx :: Maybe a) -> fmapMaybe id mx :~: mx
fmapMaybeCompose       :: forall a b c. foreach (g :: b -> c) -> foreach (f :: a -> b) -> foreach (mx :: Maybe a)
                       -> fmapMaybe (g . f) mx :~: fmapMaybe g (fmapMaybe f mx)
isJustJust             :: forall a. foreach (x :: a) -> isJust (Just x) :~: True
listToMaybeSingleton   :: forall a. foreach (x :: a) -> listToMaybe '[x] :~: Just x
listToMaybeMaybeToList :: forall a. foreach (mx :: Maybe a) -> listToMaybe (maybeToList mx) :~: mx
```

### `Data.Either.Dependent` {#dataeitherdependent}

Source: [on-site `Data/Either/Dependent.hs`](/source/dependent-base/data/either/dependent/) ·
[`Internal.hs`](/source/dependent-base/data/either/dependent/internal/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/Either/Dependent.hs)

Certified `Either` operations, involution proofs, and sum isomorphisms.

```haskell
data Either a b = Left a | Right b
either          :: forall a b c. (a -> c) -> (b -> c) -> Either a b -> c
isLeft          :: forall a b. Either a b -> Bool
isRight         :: forall a b. Either a b -> Bool
bimapEither     :: forall a b c d. (a -> c) -> (b -> d) -> Either a b -> Either c d
mapLeft         :: forall a b c. (a -> c) -> Either a b -> Either c b
mapRight        :: forall a b d. (b -> d) -> Either a b -> Either a d
swapEither      :: forall a b. Either a b -> Either b a
assocEitherTo   :: forall a b c. Either (Either a b) c -> Either a (Either b c)
assocEitherFrom :: forall a b c. Either a (Either b c) -> Either (Either a b) c

swapEitherInvolutive :: forall a b. foreach (e :: Either a b) -> swapEither (swapEither e) :~: e
isLeftLeft           :: forall a b. foreach (x :: a) -> isLeft (Left @a @b x) :~: True
isRightRight         :: forall a b. foreach (y :: b) -> isRight (Right @a @b y) :~: True
mapLeftId            :: forall a b. foreach (e :: Either a b) -> mapLeft id e :~: e
mapRightId           :: forall a b. foreach (e :: Either a b) -> mapRight id e :~: e
sumCommIso           :: forall a b. Iso (Either a b) (Either b a)
sumAssocIso          :: forall a b c. Iso (Either (Either a b) c) (Either a (Either b c))
```

### `Data.Tuple.Dependent` {#datatupledependent}

Source: [on-site `Data/Tuple/Dependent.hs`](/source/dependent-base/data/tuple/dependent/) ·
[`Internal.hs`](/source/dependent-base/data/tuple/dependent/internal/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/Tuple/Dependent.hs)

Certified pair projections, type isomorphism (`Iso`) combinators, and semiring
product bijections.

```haskell
fst        :: (a, b) -> a
snd        :: (a, b) -> b
swap       :: (a, b) -> (b, a)
curry      :: ((a, b) -> c) -> a -> b -> c
uncurry    :: (a -> b -> c) -> (a, b) -> c
bimapPair  :: forall a b c d. (a -> c) -> (b -> d) -> (a, b) -> (c, d)
firstPair  :: forall a b c. (a -> c) -> (a, b) -> (c, b)
secondPair :: forall a b d. (b -> d) -> (a, b) -> (a, d)

swapInvolutive :: forall a b. foreach (p :: (a, b)) -> swap (swap p) :~: p
pairEta        :: forall a b. foreach (p :: (a, b)) -> '(fst p, snd p) :~: p

data Iso a b where
  MkIso :: foreach (to :: a -> b)
        -> foreach (from :: b -> a)
        -> (foreach (x :: a) -> from (to x) :~: x)
        -> (foreach (y :: b) -> to (from y) :~: y)
        -> Iso a b

isoRefl     :: forall a. Iso a a
isoSym      :: forall a b. Iso a b -> Iso b a
isoTrans    :: forall a b c. Iso a b -> Iso b c -> Iso a c
composeLeft :: forall {a} {b} {c}.
               foreach (f :: a -> b) -> foreach (g :: b -> a)
            -> foreach (h :: b -> c) -> foreach (k :: c -> b)
            -> (foreach (x :: a) -> g (f x) :~: x)
            -> (foreach (y :: b) -> k (h y) :~: y)
            -> foreach (x :: a) -> g (k (h (f x))) :~: x

prodCommIso           :: forall a b. Iso (a, b) (b, a)
prodAssocIso          :: forall a b c. Iso ((a, b), c) (a, (b, c))
prodUnitLIso          :: forall a. Iso ((), a) a
prodUnitRIso          :: forall a. Iso (a, ()) a
elimProdZeroL         :: forall a b. (Void, a) -> b
elimProdZeroR         :: forall a b. (a, Void) -> b
prodDistribEitherIso  :: forall a b c. Iso (a, Either b c) (Either (a, b) (a, c))
prodDistribEitherLIso :: forall a b c. Iso (Either a b, c) (Either (a, c) (b, c))
```
