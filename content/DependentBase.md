---
title: "dependent-base Reference"
description: "API reference for TharkunAB/dependent-base: Prelude.Dependent, Data.Function.Dependent, Data.Nat.Dependent, Data.Vec.Dependent, Data.Fin.Dependent, Sigma, and Exists."
prev: /Setup/
next: /Source/
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
bundle and available in PLFH's interactive GHCi sessions. Compiler plugins live
in [`TharkunAB/dependent-proof-search`](https://github.com/TharkunAB/dependent-proof-search)
and [`TharkunAB/dependent-obs-eq`](https://github.com/TharkunAB/dependent-obs-eq).

## How `dependent-base` reuse relates to PLFA

In [*Programming Language Foundations in Agda*](https://plfa.inf.ed.ac.uk/)
(PLFA), `Naturals` defines `ℕ` and `_+_` from scratch, binds Agda's
`{-# BUILTIN NATURAL ℕ #-}` pragma for decimal numerals, and later chapters
switch to Agda's standard library (`Data.Nat`, `Data.List`,
`Relation.Binary.PropositionalEquality`).

In PLFH, Haskell datatypes are nominal and `Num Nat` / `FromNatural Nat`
instances are global. Reusing `Data.Nat.Dependent.Nat` and stock `Prelude`
`List a` keeps one shared `Nat` and one shared list type across all 25
chapters, while chapters such as [Induction](/Induction/) and [Lists](/Lists/)
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

### `Prelude.Dependent` {#preludedependent}

Source: [on-site `Prelude/Dependent.hs`](/Source/dependent-base/Prelude/Dependent/) ·
[GitHub (`TharkunAB/dependent-base`)](https://github.com/TharkunAB/dependent-base/blob/main/src/Prelude/Dependent.hs)

Umbrella prelude re-exporting `Data.Function.Dependent`,
`Data.Type.Equality.Dependent`, `Data.Decision`, `Data.Nat.Dependent`,
`Data.Fin.Dependent`, `Data.Vec.Dependent`, `Data.List.Dependent`,
`Data.List.Dependent.All`, `Data.Sigma.Dependent`, `Data.Exists.Dependent`,
`Data.Bool.Dependent`, `Data.Maybe.Dependent`, `Data.Either.Dependent`, and
`Data.Tuple.Dependent`.

### `Data.Function.Dependent` {#datafunctiondependent}

Source: [on-site `Data/Function/Dependent.hs`](/Source/dependent-base/Data/Function/Dependent/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/Function/Dependent.hs)

Dependent function combinators that generalize ordinary `Prelude` operations
without breaking non-dependent call sites:

| Symbol | Type / Role |
| --- | --- |
| `(.)` | `(foreach (y :: b) -> c y) -> foreach (f :: a -> b) -> foreach (x :: a) -> c (f x)` |
| `($)`, `applyDep` | `(foreach (x :: a) -> b x) -> foreach (x :: a) -> b x` |
| `composeDep`, `composeSigma` | Dependent composition over a shared runtime input or `Sigma` package |
| `id`, `idDep`, `const`, `constDep`, `flip`, `flipDep`, `on` | Ordinary and retained combinators |

### `Data.Type.Equality.Dependent` {#datatypeequalitydependent}

Source: [on-site `Data/Type/Equality/Dependent.hs`](/Source/dependent-base/Data/Type/Equality/Dependent/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/Type/Equality/Dependent.hs)

| Symbol | Type / Role |
| --- | --- |
| `(:~:) (Refl)`, `(:~~:) (HRefl)`, `type (~)` | Homogeneous, heterogeneous, and constraint equality |
| `sym`, `trans`, `castWith`, `gcastWith` | Equality symmetry, transitivity, and transport |
| `cong`, `cong2`, `congApp` | Matchability-polymorphic congruence (`forall (f :: a %m -> b) -> ...`) |
| `subst`, `substImplicit`, `rewrite`, `withEquality` | Substitution and local equality rewriting |
| `begin`, `stepEq`, `stepRefl`, `(===)`, `qed` | ASCII equational reasoning chains |
| `Inspect (..)`, `inspect` | Retained value-plus-equality view idiom |
| `Matchability (..)`, `M`, `U` | Re-exported from `GHC.Matchability` |

### `Data.Nat.Dependent` & `Data.Nat.Dependent.Properties` {#datanatdependent}

Source: [on-site `Data/Nat/Dependent.hs`](/Source/dependent-base/Data/Nat/Dependent/) ·
[`Properties.hs`](/Source/dependent-base/Data/Nat/Dependent/Properties/) ·
[`Internal.hs`](/Source/dependent-base/Data/Nat/Dependent/Internal/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/Nat/Dependent.hs)

| Symbol | Type / Role |
| --- | --- |
| `Nat (Zero, Succ)`, `Size` | Peano naturals with `Eq`, `Ord`, `Show`, `Num`, and `FromNatural` (`0`, `1`, `2`, ...) |
| `plus`, `type (+)`, `mul`, `minus`, `minNat`, `maxNat` | Total structural arithmetic with checked open source equations |
| `eqNat`, `eqSize`, `compareNat`, `natToInt`, `natToInteger` | Boolean equality, comparison, and `Int`/`Integer` conversion |
| `LE (..)`, `LTNat` | Inductive ordering relations |

#### `Data.Nat.Dependent.Properties` {#datanatdependentproperties}

Proves `congSucc`, `congFirst`, `succInjective`, `eqNatRefl`, `eqSizeRefl`,
`plusZero`, `plusSucc`, `plusAssoc`, `plusComm`, `mulZero`, `mulSucc`,
`mulOneL`, `mulOneR`, `mulDistribR`, `mulDistribL`, `mulAssoc`, `mulComm`,
`minusZeroR`, `minusDiag`, `leRefl`, `leTrans`, `leAntisym`, `leSuccR`,
`invLESucc`, and `decLE`.

### `Data.List.Dependent`, `Properties`, & `All` {#datalistdependent}

Source: [on-site `Data/List/Dependent.hs`](/Source/dependent-base/Data/List/Dependent/) ·
[`Properties.hs`](/Source/dependent-base/Data/List/Dependent/Properties/) ·
[`All.hs`](/Source/dependent-base/Data/List/Dependent/All/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/List/Dependent.hs)

| Symbol | Type / Role |
| --- | --- |
| `size`, `lengthNat` | `[a] -> Nat` (structural list length) |
| `(++)`, `append`, `map`, `foldr`, `zip`, `zipWith`, `reverse`, `shunt`, `reverseShunt`, `takeSize` | Certified operations directly over stock `Prelude` lists `[a]` |
| `All (..)`, `Any (..)`, `Elem`, `lookupAll`, `mapAll`, `decAll`, `decAny`, `decElem` | Indexed list predicates and decision procedures (`Data.List.Dependent.All`) |

#### `Data.List.Dependent.Properties` {#datalistdependentproperties}

Proves `consCong`, `appendNilR`, `appendAssoc`, `mapId`, `mapCompose`,
`mapAppend`, `lengthAppend`, `lengthAppendList`, `lengthMap`, `lengthZip`,
`lengthZipWith`, `lengthZipMap`, `lengthMapZip`, `lengthReverse`,
`lengthShunt`, `lengthReverseShunt`, `shuntAppend`, `reverseShuntInvolutive`,
and `lengthTakeSize`.

### `Data.Vec.Dependent` & `Data.Vec.Dependent.Properties` {#datavecdependent}

Source: [on-site `Data/Vec/Dependent.hs`](/Source/dependent-base/Data/Vec/Dependent/) ·
[`Properties.hs`](/Source/dependent-base/Data/Vec/Dependent/Properties/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/Vec/Dependent.hs)

| Symbol | Type / Role |
| --- | --- |
| `Vec (VNil, VCons)`, `SomeVec` | Length-indexed vectors `Vec a (n :: Nat)` and `some (n :: Nat) \| Vec a n` |
| `headVec`, `tailVec`, `snocVec`, `initVec`, `lastVec`, `appendVec`, `mapVec`, `zipVec`, `zipWithVec`, `replicateVec`, `lookupVec`, `mkFinVec`, `tabulateVec`, `updateAtVec`, `reverseVec`, `foldrVec` | Total length-indexed operations |
| `toListVec`, `fromListVec`, `fromListExact`, `packListVec` | Verified conversions between `Vec a n` and stock `[a]` |
| `vconsCong`, `appendVecNilL`, `appendVecCons`, `appendVecNilR`, `appendVecAssoc`, `splitAtAppendVec` | Algebraic laws in `Data.Vec.Dependent.Properties` |

### `Data.Fin.Dependent` {#datafindependent}

Source: [on-site `Data/Fin/Dependent.hs`](/Source/dependent-base/Data/Fin/Dependent/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/Fin/Dependent.hs)

| Symbol | Type / Role |
| --- | --- |
| `Fin (FZ, FS)` | Bounded natural positions strictly below `n :: Nat` |
| `finToNat`, `finToInt`, `mkFin`, `weakenFin`, `shiftFin`, `absurdFinZero`, `lastFin`, `oppositeFin` | Total indexing and position combinators |

### `Data.Sigma.Dependent` & `Data.Exists.Dependent` {#datasigmadependent}

Source: [`Data/Sigma/Dependent.hs`](/Source/dependent-base/Data/Sigma/Dependent/) ·
[`Data/Exists/Dependent.hs`](/Source/dependent-base/Data/Exists/Dependent/) ·
[GitHub](https://github.com/TharkunAB/dependent-base/blob/main/src/Data/Sigma/Dependent.hs)

| Symbol | Type / Role |
| --- | --- |
| `Sigma (Pair)`, `first`, `second`, `withSigma`, `mapSigma`, `mapSigmaSecond`, `currySigma`, `uncurrySigma` | Retained dependent pairs (`some (x :: a) \| p x`) |
| `pattern Pack`, `type (/\) (MkCPair)`, `Witness (..)`, `withExists`, `mapExists`, `uncurryExists`, `withEvidence`, `discardEvidence` | Proposal `#473` erased existential packages (`GHC.Exists.Exists`) |

### `Data.Decision`, `Bool`, `Maybe`, `Either`, & `Tuple` {#datadecision}

| Module | On-site Source | Highlights |
| --- | --- | --- |
| `Data.Decision` | [`Data/Decision.hs`](/Source/dependent-base/Data/Decision/) | `Void`, `absurd`, `Not`, `Dec (..)`, `Reflects`, `ReflectsBool`, `decNot`/`And`/`Or`/`Imp`, `DecEq` |
| `Data.Bool.Dependent` | [`Data/Bool/Dependent.hs`](/Source/dependent-base/Data/Bool/Dependent/) | Certified `not`, `(&&)`, `(||)`, `bool`, involution and De Morgan laws |
| `Data.Maybe.Dependent` | [`Data/Maybe/Dependent.hs`](/Source/dependent-base/Data/Maybe/Dependent/) | Certified `maybe`, `fromMaybe`, functor and round-trip laws |
| `Data.Either.Dependent` | [`Data/Either/Dependent.hs`](/Source/dependent-base/Data/Either/Dependent/) | Certified `either`, sum involution and associativity |
| `Data.Tuple.Dependent` | [`Data/Tuple/Dependent.hs`](/Source/dependent-base/Data/Tuple/Dependent/) | Certified `fst`, `snd`, `swap`, `curry`, `uncurry`, `Iso (..)`, `isoRefl`/`Sym`/`Trans` |
