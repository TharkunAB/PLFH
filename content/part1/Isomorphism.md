---
title: "Isomorphism: Isomorphism and embedding"
prev: /Equality/
next: /Connectives/
src: content/part1/Isomorphism.md
module: PLFH.Part1.Isomorphism
plfaChapter: https://plfa.inf.ed.ac.uk/Isomorphism/
---

```haskell
{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
module PLFH.Part1.Isomorphism
  ( Iff (..)
  , iffRefl
  , iffSym
  , iffTrans
  , IsoSize (..)
  , idSize
  , idSizeId
  , isoSizeRefl
  , isoSizeSym
  ) where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..))
```

In PLFA, **Isomorphism** introduces three ways of relating two types `a`
and `b`:

- **Logical equivalence** (`a ⇔ b`): functions `to :: a -> b` and
  `from :: b -> a` with no round-trip equations.
- **Embedding** (`a ≲ b`): `to` and `from` together with a proof
  `from (to x) ≡ x`.
- **Isomorphism** (`a ≃ b`): `to` and `from` together with *both*
  round-trip proofs `from (to x) ≡ x` and `to (from y) ≡ y`.

## Logical equivalence (`_⇔_`)

Logical equivalence requires no retained function fields and ports directly
as an equivalence relation on types:

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

## Dependent isomorphism records (`_≃_`)

Can we state PLFA's polymorphic isomorphism record in Dependent Haskell?

```{.haskell .wip}
data Iso a b where
  MkIso :: foreach (to :: a -> b) -> foreach (from :: b -> a)
        -> (foreach (x :: a) -> from (to x) :~: x)
        -> (foreach (y :: b) -> to (from y) :~: y)
        -> Iso a b
```

On published GHC `692eae0778`/`9cc4065fab`, **monomorphic** `IsoSize`
(fixing `a = b = Nat`) both declares *and* constructs/eliminates cleanly
with higher-rank `foreach` proof fields (`isoSizeRefl` and `isoSizeSym`):

```haskell
-- | Identity function on Nat with explicit structural equations.
idSize :: Nat -> Nat
idSize Zero     = Zero
idSize (Succ n) = Succ n

-- | Round-trip identity proof for `idSize`.
idSizeId :: foreach (x :: Nat) -> idSize (idSize x) :~: x
idSizeId Zero     = Refl
idSizeId (Succ _) = Refl

-- | Monomorphic isomorphism witness on Nat.
data IsoSize where
  MkIsoSize :: foreach (to :: Nat -> Nat) -> foreach (from :: Nat -> Nat)
            -> (foreach (x :: Nat) -> from (to x) :~: x)
            -> (foreach (y :: Nat) -> to (from y) :~: y)
            -> IsoSize

-- | Reflexivity of `IsoSize` (constructing higher-rank `foreach` proof fields!).
isoSizeRefl :: IsoSize
isoSizeRefl = MkIsoSize idSize idSize idSizeId idSizeId

-- | Symmetry of `IsoSize`: swap `to`/`from` and their round-trip proofs.
isoSizeSym :: IsoSize -> IsoSize
isoSizeSym (MkIsoSize to from fromTo toFrom) = MkIsoSize from to toFrom fromTo
```

<div class="note-box">
<strong>Fixed compiler gap (<code>692eae0778</code> / <code>9cc4065fab</code>):</strong>
On earlier baselines (<code>d15cbd41fe</code>–<code>1a02a866e7</code>),
constructing <code>MkIsoSize idSize idSize idSizeId idSizeId</code> failed with
<code>GHC-83865</code> printing identical expected and actual higher-rank
<code>foreach</code> types. Fixed and tracked as regression check
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/fixed/R04_HigherRankForEachField.hs"><code>reproducers/fixed/R04_HigherRankForEachField.hs</code></a>.
</div>

<div class="wip-notice">
<strong>[WIP NOTICE — Polymorphic <code>Iso a b</code> &amp; <code>Embed a b</code> (R03/R04)]</strong>
Generalizing <code>IsoSize</code> to polymorphic <code>Iso a b</code>
(<code>MkIso :: foreach (to :: a -&gt; b) -&gt; ...</code>) still fails with
<code>GHC-83605</code> (<em>This retained argument has an unsupported function
domain. Its declared domain is: <code>a -&gt; b</code></em>).
See <a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R04_PolyFunctionFieldInIso.hs"><code>reproducers/R04_PolyFunctionFieldInIso.hs</code></a>.
Because we avoid workarounds, full polymorphic <code>_≃_</code> /
<code>_≲_</code> isomorphisms await R03/R04 polymorphic retained function
domains; in <a href="/Connectives/">Connectives</a> we state the logical
equivalences using <code>Iff</code>.
</div>

## Changes from PLFA

- Adapted from [Isomorphism](https://plfa.inf.ed.ac.uk/Isomorphism/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part1/Isomorphism.lagda.md)).
- Checked direct ports of `Iff`, `iffRefl`, `iffSym`, `iffTrans`, and
  monomorphic `IsoSize` with `isoSizeRefl` and `isoSizeSym`!
- Marked polymorphic `Iso`/`Embed` with `[WIP NOTICE]` and minimal reproducer
  `R04_PolyFunctionFieldInIso.hs` (while `R04_HigherRankForEachField.hs` is now
  a verified regression check).
- Note on extensionality: like Agda, Haskell does not prove function
  extensionality (`(foreach x -> f x :~: g x) -> f :~: g`) internally.
