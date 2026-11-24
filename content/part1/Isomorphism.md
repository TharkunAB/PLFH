---
title: "Isomorphism: Isomorphism and embedding"
prev: /Equality/
next: /Connectives/
src: content/part1/Isomorphism.md
module: PLFH.Part1.Isomorphism
plfaChapter: https://plfa.inf.ed.ac.uk/19.08/Isomorphism/
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
  ) where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Size (Size (..))
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

On GHC `d15cbd41fe`, **monomorphic** `IsoSize` (fixing `a = b = Size`)
*does* declare cleanly as a GADT with retained function fields and
higher-rank `foreach` proof fields:

```haskell
-- | Identity function on Size with explicit structural equations.
idSize :: Size -> Size
idSize Zero     = Zero
idSize (Succ n) = Succ n

-- | Round-trip identity proof for `idSize`.
idSizeId :: foreach (x :: Size) -> idSize (idSize x) :~: x
idSizeId Zero     = Refl
idSizeId (Succ _) = Refl

-- | Monomorphic isomorphism witness on Size (declaration checks!).
data IsoSize where
  MkIsoSize :: foreach (to :: Size -> Size) -> foreach (from :: Size -> Size)
            -> (foreach (x :: Size) -> from (to x) :~: x)
            -> (foreach (y :: Size) -> to (from y) :~: y)
            -> IsoSize
```

<div class="wip-notice">
<strong>[WIP NOTICE — Polymorphic <code>Iso a b</code> &amp; constructing <code>MkIsoSize</code> (R03/R04)]</strong>
Stating and using PLFA's <code>_≃_</code> (<code>Iso</code>) and
<code>_≲_</code> (<code>Embed</code>) uncovers two crisp R03/R04 boundaries
on GHC <code>d15cbd41fe</code>:
<ol>
  <li><strong>Polymorphic function fields in <code>foreach</code> (R03/R04):</strong>
      <code>MkIso :: foreach (to :: a -&gt; b) -&gt; ...</code> fails with
      <code>GHC-83605</code> (<em>This retained argument has an unsupported
      function domain. Its declared domain is: <code>a -&gt; b</code></em>).
      See <a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R04_PolyFunctionFieldInIso.hs"><code>reproducers/R04_PolyFunctionFieldInIso.hs</code></a>.</li>
  <li><strong>Applying <code>MkIsoSize</code> to a higher-rank <code>foreach</code> proof (R03/R04):</strong>
      Even though <code>data IsoSize</code> itself compiles, constructing
      <code>MkIsoSize idSize idSize idSizeId idSizeId</code> fails with
      <code>GHC-83865</code> printing <em>identical</em> expected and actual types:
      <code>Couldn't match expected type: foreach (x :: Size) -&gt; idSize (idSize x) :~: x
      with actual type: foreach (x :: Size) -&gt; idSize (idSize x) :~: x</code>!
      See <a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R04_HigherRankForEachField.hs"><code>reproducers/R04_HigherRankForEachField.hs</code></a>.</li>
</ol>
Because we avoid workarounds, full <code>_≃_</code> / <code>_≲_</code>
isomorphisms and embeddings await R03/R04 support; in
<a href="/Connectives/">Connectives</a> we state the logical equivalences
using <code>Iff</code>.
</div>

## Changes from PLFA `v19.08`

- Adapted from [Isomorphism (v19.08)](https://plfa.inf.ed.ac.uk/19.08/Isomorphism/)
  ([source](https://github.com/plfa/plfa.github.io/blob/63fcbbe25ec3686ff4c6df2c5b58a96b3a2054f3/src/plfa/part1/Isomorphism.lagda.md)).
- Checked direct ports of `Iff`, `iffRefl`, `iffSym`, `iffTrans`, and the
  declaration of `IsoSize`.
- Marked polymorphic `Iso`/`Embed` and constructing `MkIsoSize` with
  `[WIP NOTICE]` and two minimal R03/R04 reproducers.
- Note on extensionality: like Agda, Haskell does not prove function
  extensionality (`(foreach x -> f x :~: g x) -> f :~: g`) internally.
