---
title: "Lists: Lists and higher-order functions"
prev: /Decidable/
next: /Lambda/
src: content/part1/Lists.md
module: PLFH.Part1.Lists
plfaChapter: https://plfa.inf.ed.ac.uk/Lists/
---

```haskell
{-# LANGUAGE AllowAmbiguousTypes, DataKinds, EmptyCase, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, PolyKinds, ScopedTypeVariables, TypeApplications, TypeOperators #-}
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
  , downFrom
  , zeros
  , lengthDownFrom
  , lengthZeros
  , All (..)
  , Any (..)
  , In
  , allAppend
  , allAppendInv
  , allMap
  , anyAppendL
  , anyAppendR
  , anyAppendInv
  , decAll
  , decAny
  , zeroInList
  , threeNotInList
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl), gcastWith)
import Data.Void (Void)
import HaskLib (lengthAppend, lengthMap, lengthReverse, rewrite, size)
import HaskLib.Nat (Nat (..), plus)
import PLFH.Part1.Decidable (Dec (..), Not)
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
appendAssoc (_ : xs) ys zs = rewrite (appendAssoc xs ys zs) Refl

-- | Right identity of Prelude list append: xs ++ [] = xs.
appendNilR :: forall a. foreach (xs :: [a]) -> (xs ++ '[]) :~: xs
appendNilR []       = Refl
appendNilR (_ : xs) = rewrite (appendNilR xs) Refl
```

## Length laws (reused from `HaskLib`)

PLFA proves `length (xs ++ ys) ≡ length xs + length ys` and asks for length
preservation of `map` and `reverse`. All three are already proved for
ordinary Prelude `(++)`, `map`, and `reverse` in `HaskLib`:

```haskell
-- | Length of append (reused directly from HaskLib.lengthAppend).
lengthAppendLaw :: forall a. foreach (xs :: [a]) -> foreach (ys :: [a])
                -> size (xs ++ ys) :~: plus (size xs) (size ys)
lengthAppendLaw = lengthAppend

-- | Length of map (reused from HaskLib.lengthMap; eta-expanded due to R04/R05 bug below).
lengthMapLaw :: forall a b. foreach (f :: a -> b) -> foreach (xs :: [a])
             -> size (map f xs) :~: size xs
lengthMapLaw f xs = lengthMap f xs

-- | Length of reverse (reused directly from HaskLib.lengthReverse).
lengthReverseLaw :: forall a. foreach (xs :: [a])
                 -> size (reverse xs) :~: size xs
lengthReverseLaw = lengthReverse
```

<div class="note-box">
<strong>Fixed compiler panic (<code>692eae0778</code> / <code>9cc4065fab</code>):</strong>
On earlier baselines (<code>db2586fdc2</code>–<code>1a02a866e7</code>),
eta-reduced aliases like <code>lengthReverseLaw = lengthReverse</code> panicked
at <code>compiler/GHC/Core/TyCo/Subst.hs:900</code>. Fixed for value-typed
<code>foreach</code> aliases (<code>lengthAppendLaw</code>,
<code>lengthReverseLaw</code>) and tracked as regression check
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/fixed/R05_SubstTyEtaAliasPanic.hs"><code>reproducers/fixed/R05_SubstTyEtaAliasPanic.hs</code></a>.
</div>

<div class="wip-notice">
<strong>[WIP NOTICE — Eta-reduced alias with function-valued <code>foreach (f :: a -&gt; b)</code> (R04/R05)]</strong>
Even on published <code>9cc4065fab</code>, writing the eta-reduced alias
<code>lengthMapLaw = lengthMap</code> fails with <code>GHC-83865</code>
printing <em>identical</em> expected and actual types
(<code>foreach (f :: a -&gt; b) -&gt; foreach (xs :: [a]) -&gt; size (map f xs) :~: size xs</code>),
whereas eta-expanding <code>lengthMapLaw f xs = lengthMap f xs</code> checks
cleanly. Isolated in
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R04_EtaAliasForEachFunctionBinder.hs"><code>reproducers/R04_EtaAliasForEachFunctionBinder.hs</code></a>.
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

## Accumulating `shunt`, countdown lists (`downFrom`, `zeros`), and `foldr`

On published `dependent-haskell` (`692eae0778`/`9cc4065fab`), both PLFA's
accumulating tail-recursive `shunt` (since this module disables rewrite rules
for `HaskLib.lengthMap`) and `Nat -> [Nat]` countdown recursion (`downFrom`,
`zeros`) now check directly!

```haskell
-- | Accumulating list reversal helper `shunt`.
shunt :: [a] -> [a] -> [a]
shunt []     ys = ys
shunt (x:xs) ys = shunt xs (x : ys)

-- | Distributivity of `shunt` over append (`shunt-++`).
shuntAppend :: forall a. foreach (xs :: [a]) -> foreach (ys :: [a]) -> foreach (zs :: [a])
            -> shunt (xs ++ ys) zs :~: shunt ys (shunt xs zs)
shuntAppend []     _  _  = Refl
shuntAppend (x:xs) ys zs = shuntAppend xs ys (x : zs)

-- | Countdown list from `n - 1` down to `0` (`downFrom`).
downFrom :: Nat -> [Nat]
downFrom Zero     = []
downFrom (Succ n) = n : downFrom n

-- | A list of `n` copies of `Zero`.
zeros :: Nat -> [Nat]
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

<div class="note-box">
<strong>Fixed compiler gaps (<code>692eae0778</code> / <code>9cc4065fab</code>):</strong>
<code>downFrom</code> / <code>zeros</code> (<code>Nat -&gt; [Nat]</code> open
equations) now check at both <code>-O0</code> and <code>-O2</code>
(<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/fixed/R13_DownFromOpenEq.hs"><code>reproducers/fixed/R13_DownFromOpenEq.hs</code></a>).
Accumulating <code>shuntAppend</code> checks at <code>-O0</code> and at
<code>-O2 -fno-enable-rewrite-rules</code> (as in this module), while default
<code>-O2</code> with Prelude <code>(++)</code> fusion rules remains tracked in
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_ShuntAccumOpenEq.hs"><code>reproducers/R13_ShuntAccumOpenEq.hs</code></a>.
</div>

<div class="wip-notice">
<strong>[WIP NOTICE — Quadratic <code>rev</code> (R13/R16), higher-order <code>foldr</code> (R03), &amp; default <code>-O2</code> <code>shunt</code>]</strong>
Three classic PLFA Lists items remain open on published <code>9cc4065fab</code>:
<ol>
  <li><strong>Quadratic <code>rev</code> (R13/R16):</strong>
      PLFA's naive quadratic <code>rev [] = []; rev (x:xs) = app (rev xs) [x]</code>
      still fails open evaluation with <code>GHC-70565</code>—blocking
      <code>shunt-reverse</code> and <code>reverses</code>. See
      <a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_RevOpenEq.hs"><code>reproducers/R13_RevOpenEq.hs</code></a>.</li>
  <li><strong>Higher-order <code>foldr</code> in retained arguments (R03):</strong>
      Passing <code>foldrL plus Zero xs</code> as a retained runtime argument
      to an associative lemma like <code>plusAssoc</code> still fails with
      <code>GHC-83605</code> (<em>GHC cannot use this expression as a retained
      index</em>), blocking <code>foldr-monoid-++</code>. See
      <a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R03_FoldrRetainedIndex.hs"><code>reproducers/R03_FoldrRetainedIndex.hs</code></a>.</li>
  <li><strong>Default <code>-O2</code> rewrite-rule check on <code>shuntAppend</code>:</strong>
      Without <code>-fno-enable-rewrite-rules</code>, default <code>-O2</code>
      still rejects <code>shuntAppend</code> with <code>GHC-83605</code> at the
      Prelude <code>(++)</code> rewrite-rule guard
      (<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_ShuntAccumOpenEq.hs"><code>reproducers/R13_ShuntAccumOpenEq.hs</code></a>).</li>
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

-- | Inversion of `All` over append: `All p (xs ++ ys)` splits into `All p xs` and `All p ys`.
allAppendInv :: foreach (xs :: [a]) -> All p (xs ++ ys) -> (All p xs, All p ys)
allAppendInv []     ays            = (AllNil, ays)
allAppendInv (_:xs) (AllCons px r) =
  case allAppendInv xs r of
    (axs, ays) -> (AllCons px axs, ays)

-- | Left introduction for `Any` over append.
anyAppendL :: forall a (p :: a -> Type) (xs :: [a]) (ys :: [a]). Any p xs -> Any p (xs ++ ys)
anyAppendL (Here px) = Here px
anyAppendL (There r) = There (anyAppendL @a @p @_ @ys r)

-- | Right introduction for `Any` over append.
anyAppendR :: forall a (p :: a -> Type) (ys :: [a]).
              foreach (xs :: [a]) -> Any p ys -> Any p (xs ++ ys)
anyAppendR []     ays = ays
anyAppendR (x:xs) ays = There @p @(xs ++ ys) @x (anyAppendR @a @p @ys xs ays)

-- | Inversion of `Any` over append: `Any p (xs ++ ys)` comes from `xs` or `ys`.
anyAppendInv :: foreach (xs :: [a]) -> Any p (xs ++ ys) -> Either (Any p xs) (Any p ys)
anyAppendInv []     ays       = Right ays
anyAppendInv (_:_)  (Here px) = Left (Here px)
anyAppendInv (_:xs) (There r) =
  case anyAppendInv xs r of
    Left  axs -> Left (There axs)
    Right ays -> Right ays

-- | Decidability of universal list quantification `All p xs`.
decAll :: (foreach (x :: a) -> Dec (p x)) -> foreach (xs :: [a]) -> Dec (All p xs)
decAll d xs = case xs of
  []    -> Yes AllNil
  x:xs' -> case d x of
    No npx -> No (\case AllCons px _ -> npx px)
    Yes px -> case decAll d xs' of
      Yes axs -> Yes (AllCons px axs)
      No naxs -> No (\case AllCons _ axs -> naxs axs)

-- | Decidability of existential list quantification `Any p xs`.
decAny :: (foreach (x :: a) -> Dec (p x)) -> foreach (xs :: [a]) -> Dec (Any p xs)
decAny d xs = case xs of
  []    -> No (\case {})
  x:xs' -> case d x of
    Yes px  -> Yes (Here px)
    No  npx -> case decAny d xs' of
      Yes axs -> Yes (There axs)
      No naxs -> No (\case Here px -> npx px; There axs -> naxs axs)

-- | Concrete membership proof: 0 ∈ [0, 1, 0].
zeroInList :: In (0 :: Nat) '[ (0 :: Nat), (1 :: Nat), (0 :: Nat) ]
zeroInList = Here Refl

-- | Concrete non-membership proof: 2 ∉ [0, 1].
threeNotInList :: Not (In (2 :: Nat) '[ (0 :: Nat), (1 :: Nat) ])
threeNotInList (Here eq)          = case eq of {}
threeNotInList (There (Here eq))  = case eq of {}
threeNotInList (There (There p))  = case p of {}
```

<div class="wip-notice">
<strong>[WIP NOTICE — De Morgan between <code>All</code> and <code>Any</code> with an inline type lambda (R23)]</strong>
Writing <code>Not (Any p xs) -&gt; All (\x -&gt; Not (p x)) xs</code>
hits the same Matchable-vs-Unmatchable arrow kind clash as Leibniz
equality, because <code>All</code> expects a matchable predicate
<code>a -&gt; Type</code> while the inline type lambda has unmatchable
kind <code>a %U -&gt; Type</code> (see
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R23_MatchabilityInLeibniz.hs"><code>reproducers/R23_MatchabilityInLeibniz.hs</code></a>).
</div>

## Changes from PLFA

- Adapted from [Lists](https://plfa.inf.ed.ac.uk/Lists/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part1/Lists.lagda.md)).
- Used standard Prelude `[a]`, `(++)`, and `map` directly instead of a custom
  `List` datatype.
- Reused `HaskLib`'s `lengthAppend`, `lengthMap`, and `lengthReverse` via
  direct eta-reduced aliases (fixed on `692eae0778`/`9cc4065fab`).
- Checked direct ports of `appendAssoc`, `appendNilR`, `mapAppend`,
  `mapCompose`, `mapId`, `shunt`/`shuntAppend`, `downFrom`/`zeros`/`lengthDownFrom`/`lengthZeros`,
  `All`, `Any`, `In`, `allAppend`/`Inv`, `anyAppend*`/`Inv`, `allMap`,
  `decAll`, `decAny`, `zeroInList`, and `threeNotInList`.
- Marked naive quadratic `rev`, `foldr` as a retained index, default `-O2`
  `shunt` fusion rules, multi-equation splitting after a retained function,
  and inline type-lambda `All` with `[WIP NOTICE]` and minimal reproducers.
