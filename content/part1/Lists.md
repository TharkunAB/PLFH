---
title: "Lists: Lists and higher-order functions"
prev: /Decidable/
next: /Lambda/
src: content/part1/Lists.md
module: PLFH.Part1.Lists
plfaChapter: https://plfa.inf.ed.ac.uk/19.08/Lists/
---

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, TypeOperators #-}
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
  , All (..)
  , Any (..)
  , In
  , allAppend
  , allMap
  , zeroInList
  , threeNotInList
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl), gcastWith)
import Data.Void (Void)
import HaskLib (lengthAppend, lengthMap, lengthReverse, size, withEquality)
import HaskLib.Size (Size (..), plus)
import PLFH.Part1.Decidable (Not)
```

In PLFA, the **Lists** chapter introduces polymorphic lists, append (`++`),
length, reverse, `shunt`, `map`, `foldr`, monoids, and the indexed list
predicates `All`, `Any`, and membership (`∈`).

On this Dependent Haskell fork, **ordinary Prelude lists `[a]`**,
**Prelude `(++)`**, and **Prelude `map`** already have checked open source
equations—so we can state and prove classic list laws directly over standard
Haskell lists with no custom shadow `List` datatype!

## Append (`++`): associativity and right identity

Using Prelude `(++)` directly in both types and terms:

```haskell
-- | Associativity of Prelude list append: (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
appendAssoc :: forall a. foreach (xs :: [a]) -> foreach (ys :: [a]) -> foreach (zs :: [a])
            -> ((xs ++ ys) ++ zs) :~: (xs ++ (ys ++ zs))
appendAssoc []       _  _  = Refl
appendAssoc (_ : xs) ys zs = withEquality (appendAssoc xs ys zs) Refl

-- | Right identity of Prelude list append: xs ++ [] = xs.
appendNilR :: forall a. foreach (xs :: [a]) -> (xs ++ '[]) :~: xs
appendNilR []       = Refl
appendNilR (_ : xs) = withEquality (appendNilR xs) Refl
```

## Length laws (reused from `HaskLib`)

PLFA proves `length (xs ++ ys) ≡ length xs + length ys` and asks for length
preservation of `map` and `reverse`. All three are already proved for
ordinary Prelude `(++)`, `map`, and `reverse` in `HaskLib`:

```haskell
-- | Length of append (reused from HaskLib.lengthAppend).
lengthAppendLaw :: forall a. foreach (xs :: [a]) -> foreach (ys :: [a])
                -> size (xs ++ ys) :~: plus (size xs) (size ys)
lengthAppendLaw xs ys = lengthAppend xs ys

-- | Length of map (reused from HaskLib.lengthMap).
lengthMapLaw :: forall a b. foreach (f :: a -> b) -> foreach (xs :: [a])
             -> size (map f xs) :~: size xs
lengthMapLaw f xs = lengthMap f xs

-- | Length of reverse (reused from HaskLib.lengthReverse).
lengthReverseLaw :: forall a. foreach (xs :: [a])
                 -> size (reverse xs) :~: size xs
lengthReverseLaw xs = lengthReverse xs
```

<div class="wip-notice">
<strong>[WIP NOTICE — GHC compiler panic on eta-reduced polymorphic <code>foreach</code> alias (R05)]</strong>
Writing an eta-reduced alias such as <code>lengthReverseLaw = lengthReverse</code>
for an imported polymorphic <code>foreach (xs :: [a])</code> function triggers
an internal compiler panic on GHC <code>db2586fdc2</code>:
<pre class="wip"><code>panic! (the 'impossible' happened)
  substTy: unsupported runtime index or changed domain
  pprPanic, called at compiler/GHC/Core/TyCo/Subst.hs:900:14</code></pre>
Eta-expanding the retained arguments (<code>lengthReverseLaw xs = lengthReverse xs</code>)
compiles cleanly. Reported with 7-line minimal reproducer
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R05_SubstTyEtaAliasPanic.hs"><code>reproducers/R05_SubstTyEtaAliasPanic.hs</code></a>.
</div>

<div class="note-box">
<strong>Rewrite rules note:</strong>
As documented in the GHC fork's README, modules using <code>lengthMap</code>
disable rewrite rules (<code>-fno-enable-rewrite-rules</code>) because stock
list-fusion rewrite rules can change demand on partial inputs.
</div>

## Higher-order list laws: `map`

Because `foreach (f :: a -> b)` retains an arbitrary unknown Haskell function,
we can prove the functor and append-homomorphism laws for **ordinary
Prelude `map`** and **`(.)`**:

```haskell
-- | Map distributes over append: map f (xs ++ ys) = map f xs ++ map f ys.
mapAppend :: forall a b. foreach (f :: a -> b) -> foreach (xs :: [a]) -> foreach (ys :: [a])
          -> map f (xs ++ ys) :~: (map f xs ++ map f ys)
mapAppend f xs ys = case xs of
  []        -> Refl
  (_ : xs') -> gcastWith (mapAppend f xs' ys) Refl

-- | Functor composition law: map (g . f) xs = map g (map f xs).
mapCompose :: forall a b c. foreach (g :: b -> c) -> foreach (f :: a -> b) -> foreach (xs :: [a])
           -> map (g . f) xs :~: map g (map f xs)
mapCompose g f xs = case xs of
  []        -> Refl
  (_ : xs') -> gcastWith (mapCompose g f xs') Refl

-- | Functor identity law: map id xs = xs.
mapId :: forall a. foreach (xs :: [a]) -> map id xs :~: xs
mapId []       = Refl
mapId (_ : xs) = gcastWith (mapId xs) Refl
```

<div class="wip-notice">
<strong>[WIP NOTICE — Equations with a leading retained function binder (R03)]</strong>
Notice that <code>mapAppend</code> and <code>mapCompose</code> match on
<code>xs</code> using <code>case xs of</code> rather than constructor
equations <code>mapAppend _ [] _ = Refl</code>. On GHC <code>db2586fdc2</code>,
multi-equation constructor splitting after a leading function-valued retained
binder reports <code>GHC-83605</code> (<em>Function-valued retained binders
require bare variable patterns or wildcards</em>). See
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R03_FunctionColumnSplit.hs"><code>reproducers/R03_FunctionColumnSplit.hs</code></a>.
</div>

## Reverse, `shunt`, and `foldr` monoid laws

<div class="wip-notice">
<strong>[WIP NOTICE — Quadratic <code>reverse</code> (R13/R16) and higher-order <code>foldr</code> as a retained index (R03)]</strong>
Two classic PLFA Lists sections hit crisp compiler boundaries on GHC <code>db2586fdc2</code>:
<ol>
  <li><strong>Quadratic <code>rev</code> (R13/R16):</strong>
      While tail-recursive <code>shunt</code> (<code>shunt [] ys = ys; shunt (x:xs) ys = shunt xs (x:ys)</code>)
      <em>does</em> get open source equations (and proves <code>shunt (xs ++ ys) zs :~: shunt ys (shunt xs zs)</code>),
      PLFA's naive quadratic <code>rev [] = []; rev (x:xs) = app (rev xs) [x]</code>
      fails open evaluation with <code>GHC-70565</code>—blocking
      <code>shunt-reverse</code> and <code>reverses</code>. See
      <a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_RevOpenEq.hs"><code>reproducers/R13_RevOpenEq.hs</code></a>.</li>
  <li><strong>Higher-order <code>foldr</code> in retained arguments (R03):</strong>
      GHC accepts <code>foldrL plus 'Zero (app xs ys)</code> inside a type
      signature, but rejects passing <code>foldrL plus Zero xs</code> as a
      retained runtime argument to an associative lemma like <code>plusAssoc</code>
      with <code>GHC-83605</code> (<em>GHC cannot use this expression as a retained
      index</em>). This blocks PLFA's <code>foldr-monoid-++</code> proof. See
      <a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R03_FoldrRetainedIndex.hs"><code>reproducers/R03_FoldrRetainedIndex.hs</code></a>.</li>
</ol>
</div>

## Predicates on lists: `All`, `Any`, and membership (`∈`)

Indexed list predicates port cleanly as GADTs over promoted Prelude lists:

```haskell
-- | Evidence that predicate `p` holds for every element of `xs`.
data All (p :: a -> Type) (xs :: [a]) where
  AllNil  :: All p '[]
  AllCons :: p x -> All p xs -> All p (x ': xs)

-- | Evidence that predicate `p` holds for at least one element of `xs`.
data Any (p :: a -> Type) (xs :: [a]) where
  Here  :: p x -> Any p (x ': xs)
  There :: Any p xs -> Any p (x ': xs)

-- | List membership: `x` appears in `xs`.
type In (x :: a) (xs :: [a]) = Any ((:~:) x) xs

-- | If `p` holds for all of `xs` and all of `ys`, it holds for `xs ++ ys`.
allAppend :: All p xs -> All p ys -> All p (xs ++ ys)
allAppend AllNil           pys = pys
allAppend (AllCons px pxs) pys = AllCons px (allAppend pxs pys)

-- | Transforming element proofs under `All`.
allMap :: (forall x. p x -> q x) -> All p xs -> All q xs
allMap _ AllNil           = AllNil
allMap f (AllCons px pxs) = AllCons (f px) (allMap f pxs)

-- | Concrete membership proof: 0 ∈ [0, 1, 0].
zeroInList :: In 'Zero '[ 'Zero, 'Succ 'Zero, 'Zero ]
zeroInList = Here Refl

-- | Concrete non-membership proof: 2 ∉ [0, 1].
threeNotInList :: Not (In ('Succ ('Succ 'Zero)) '[ 'Zero, 'Succ 'Zero ])
threeNotInList (Here eq)          = case eq of {}
threeNotInList (There (Here eq))  = case eq of {}
threeNotInList (There (There p))  = case p of {}
```

## Changes from PLFA `v19.08`

- Adapted from [Lists (v19.08)](https://plfa.inf.ed.ac.uk/19.08/Lists/)
  ([source](https://github.com/plfa/plfa.github.io/blob/63fcbbe25ec3686ff4c6df2c5b58a96b3a2054f3/src/plfa/part1/Lists.lagda.md)).
- Used standard Prelude `[a]`, `(++)`, and `map` directly instead of a custom
  `List` datatype.
- Reused `HaskLib`'s `lengthAppend`, `lengthMap`, and `lengthReverse`.
- Checked direct ports of `appendAssoc`, `appendNilR`, `mapAppend`,
  `mapCompose`, `mapId`, `All`, `Any`, `In`, `allAppend`, `allMap`,
  `zeroInList`, and `threeNotInList`.
- Marked naive quadratic `rev`, `foldr` as a retained index, and multi-equation
  splitting after a retained function with `[WIP NOTICE]` and minimal reproducers.
