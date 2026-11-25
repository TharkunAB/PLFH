---
title: "HaskLib Reference"
prev: /Setup/
next: /Source/
src: content/HaskLib.md
---

`HaskLib` is the prototype Dependent Haskell standard library shipped alongside
[`Tritlo/ghc` (`dependent-haskell`)](https://github.com/Tritlo/ghc/tree/dependent-haskell).
Every module in `HaskLib` is precompiled into the browser WebAssembly bundle and
available automatically in PLFH's interactive GHCi sessions.

## How `HaskLib` reuse relates to PLFA

In [*Programming Language Foundations in Agda*](https://plfa.inf.ed.ac.uk/)
(PLFA), `Naturals` defines `ℕ` and `_+_` from scratch, binds Agda's
`{-# BUILTIN NATURAL ℕ #-}` pragma for decimal numerals, and later chapters
switch to Agda's standard library (`Data.Nat`, `Data.List`,
`Relation.Binary.PropositionalEquality`).

In PLFH, Haskell datatypes are nominal and `Num Nat` / `FromNatural Nat`
instances are global. Reusing `HaskLib.Nat.Nat` and stock `Prelude` `List a`
keeps one shared `Nat` and one shared list type across all 25 chapters,
`HaskLib.List.size`, and decimal-numeral literals (`2 + 3 :~: 5`), while
chapters like [Induction](/Induction/) and [Lists](/Lists/) still prove the
core inductive theorems (`plusIdentityR`, `plusSuc`, `plusAssoc`, `plusComm`,
`appendAssoc`, `lengthAppendLaw`, `lengthMapLaw`) directly inline for pedagogy.

## Interactive GHCi tips

- **Inspect any module in the browser drawer:** run `:browse HaskLib.Nat`,
  `:browse HaskLib.List`, or `:browse PLFH.Part1.Naturals` in **Open Chapter GHCi**.
- **Printing `Nat` as a decimal:** `PreludeMapLengthSize.Nat` derives `Show`
  (printing `Succ (Succ Zero)`) and provides `Num Nat` / `FromNatural Nat` for
  constructing Peano numbers from decimal literals (`2 :: Nat`). Until
  `HaskLib.Nat` adds a decimal inverse (`ToNatural`), you can print decimal
  values in GHCi with a one-liner:

  ```text
  ghci> let natToInt Zero = 0; natToInt (Succ n) = 1 + natToInt n
  ghci> natToInt (plus 2 3)
  5
  ```

## Module Index & Exported API

### `HaskLib` {#hasklib}

Source: [on-site `HaskLib.hs`](/Source/hasklib/HaskLib/) ·
[GitHub (`Tritlo/ghc`)](https://github.com/Tritlo/ghc/blob/dependent-haskell/docs/dependent-haskell/hasklib/HaskLib.hs)

Re-exports `module HaskLib.List`, `Matchability (..)` (from `GHC.Matchability`),
`(:~:) (Refl)` and `trans` (from `Data.Type.Equality`), plus core equality
combinators:

| Symbol | Type / Role |
| --- | --- |
| `cong` | `forall {a} {b} {m :: Matchability} (f :: a %m -> b) x y. x :~: y -> f x :~: f y` |
| `rewrite` | `(a :~: b) -> ((a ~ b) => r) -> r` (alias for `gcastWith`) |
| `withEquality` | Compatibility alias for `rewrite` |
| `eqSize`, `eqSizeRefl`, `plusZero`, `plusSucc`, `congSucc`, `congFirst` | Re-exported from `HaskLib.Nat` |

### `HaskLib.Nat` {#hasklibnat}

Source: [on-site `HaskLib/Nat.hs`](/Source/hasklib/HaskLib/Nat/) ·
[GitHub (`Tritlo/ghc`)](https://github.com/Tritlo/ghc/blob/dependent-haskell/docs/dependent-haskell/hasklib/HaskLib/Nat.hs)

| Symbol | Type / Role |
| --- | --- |
| `Nat (Zero, Succ)` | Peano natural numbers (defined in [`PreludeMapLengthSize.hs`](/Source/hasklib/PreludeMapLengthSize/), with `Show`, `Num Nat`, and `FromNatural Nat`) |
| `plus` | `Nat -> Nat -> Nat` (structural recursion on first argument) |
| `type (+)` | `type (m :: Nat) + (n :: Nat) = plus m n` (`infixl 6`) |
| `eqSize` | `Nat -> Nat -> Bool` |
| `eqSizeRefl` | `foreach (n :: Nat) -> eqSize n n :~: True` |
| `plusZero` | `foreach (m :: Nat) -> plus m Zero :~: m` |
| `plusSucc` | `foreach (m :: Nat) -> foreach (n :: Nat) -> plus m (Succ n) :~: Succ (plus m n)` |
| `plusComm` | `foreach (m :: Nat) -> foreach (n :: Nat) -> plus m n :~: plus n m` |
| `congSucc` | `m :~: n -> Succ m :~: Succ n` |
| `congFirst` | `forall (f :: Nat %U -> Nat %U -> Nat) r m n. m :~: n -> f m r :~: f n r` |

### `HaskLib.List` {#haskliblist}

Source: [on-site `HaskLib/List.hs`](/Source/hasklib/HaskLib/List/) ·
[GitHub (`Tritlo/ghc`)](https://github.com/Tritlo/ghc/blob/dependent-haskell/docs/dependent-haskell/hasklib/HaskLib/List.hs)

Laws over stock `Prelude` lists (`[a]`, `(++)`, `map`, `reverse`, `zip`, `zipWith`, `foldr`):

| Symbol | Type / Role |
| --- | --- |
| `Size` | Compatibility alias for `Nat` |
| `size` | `[a] -> Nat` (structural list length) |
| `minSize` | `Nat -> Nat -> Nat` |
| `takeSize` | `Nat -> [a] -> [a]` (from [`HaskLib/List/Prefix.hs`](/Source/hasklib/HaskLib/List/Prefix/)) |
| `foldr` | `(a -> b -> b) -> b -> [a] -> b` (re-exported from `GHC.Internal.List` with checked equations) |
| `appendAssoc` | `foreach (xs ys zs :: [a]) -> ((xs ++ ys) ++ zs) :~: (xs ++ (ys ++ zs))` |
| `lengthMap` | `foreach (f :: a -> b) -> foreach (xs :: [a]) -> size (map f xs) :~: size xs` |
| `lengthAppend` | `foreach (xs ys :: [a]) -> size (xs ++ ys) :~: plus (size xs) (size ys)` |
| `lengthReverse` | `foreach (xs :: [a]) -> size (reverse xs) :~: size xs` |
| `lengthTakeSize` | `foreach (n :: Nat) -> foreach (xs :: [a]) -> size (takeSize n xs) :~: minSize n (size xs)` |
| `lengthZip`, `lengthZipWith`, `lengthZipMap`, `lengthMapZip` | Length preservation for `zip`, `zipWith`, and fused `map`/`zip` compositions |

### Underlying Runtime & Compatibility Modules

| Module | On-site Source | Upstream (`Tritlo/ghc`) | Role |
| --- | --- | --- | --- |
| `PreludeMapLengthSize` | [`PreludeMapLengthSize.hs`](/Source/hasklib/PreludeMapLengthSize/) | [GitHub](https://github.com/Tritlo/ghc/blob/dependent-haskell/docs/dependent-haskell/examples/open-evaluation/PreludeMapLengthSize.hs) | Defines `Nat`, `ToPeano`, `FromNatural Nat`, `Num Nat`, `plus`, `size`, `minSize`, `eqSize` |
| `HaskLib.Size` | [`HaskLib/Size.hs`](/Source/hasklib/HaskLib/Size/) | [GitHub](https://github.com/Tritlo/ghc/blob/dependent-haskell/docs/dependent-haskell/hasklib/HaskLib/Size.hs) | Legacy compatibility re-exports for `Size` and `Nat` |
| `HaskLib.List.Prefix` | [`HaskLib/List/Prefix.hs`](/Source/hasklib/HaskLib/List/Prefix/) | [GitHub](https://github.com/Tritlo/ghc/blob/dependent-haskell/docs/dependent-haskell/hasklib/HaskLib/List/Prefix.hs) | Defines structural `takeSize` |
| `PreludeZipRuntime` | [`PreludeZipRuntime.hs`](/Source/hasklib/PreludeZipRuntime/) | [GitHub](https://github.com/Tritlo/ghc/blob/dependent-haskell/docs/dependent-haskell/examples/open-evaluation/PreludeZipRuntime.hs) | Defines `lengthZip` and `lengthZipWith` |
| `PreludeZipMapRuntime` | [`PreludeZipMapRuntime.hs`](/Source/hasklib/PreludeZipMapRuntime/) | [GitHub](https://github.com/Tritlo/ghc/blob/dependent-haskell/docs/dependent-haskell/examples/open-evaluation/PreludeZipMapRuntime.hs) | Defines `lengthZipMap` |
