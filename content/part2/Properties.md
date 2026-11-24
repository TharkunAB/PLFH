---
title: "Properties: Progress and Preservation"
prev: /Lambda/
next: /DeBruijn/
src: content/part2/Properties.md
module: PLFH.Part2.Properties
plfaChapter: https://plfa.inf.ed.ac.uk/Properties/
---

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, TypeOperators #-}
module PLFH.Part2.Properties
  ( Canonical (..)
  , canonical
  , extCtx
  , renameTyping
  , weakenTyping
  , dropTyping
  , swapTyping
  ) where

import Data.Type.Equality ((:~:) (Refl))
import Data.Void (absurd)
import PLFH.Part1.Decidable (Not)
import PLFH.Part2.Lambda
  ( Ctx (..)
  , HasType (..)
  , Id
  , Lookup (..)
  , Term (..)
  , Ty (..)
  , Value (..)
  )
```

Type safety for the simply-typed lambda calculus rests on two classic
theorems due to Wright and Felleisen:

1. **Progress:** Every closed, well-typed term is either already a value or
   can take a step (`progress`).
2. **Preservation (Subject Reduction):** If a closed, well-typed term takes
   a step, the resulting term has the same type (`preserve`).

In this chapter we prove **Canonical Forms** (`canonical`) and all of the
structural context lemmas needed for **Preservation** (`extCtx`,
`renameTyping`, `weakenTyping`, `dropTyping`, `swapTyping`) directly in
Dependent Haskell—and document the exact R13/R16 open-evaluation boundary for
`Syntax.substTerm` that currently blocks sound `Step`-indexed `progress`,
`substTyping`, and `preserve` on the published 590 compiler.

## Canonical forms

A closed value of function type must be a lambda abstraction, and a closed
value of natural-number type must be `TZero` or `TSuc v`:

```haskell
-- | Canonical form of a closed well-typed value.
data Canonical (m :: Term) (a :: Ty) where
  CLam  :: HasType ('CExt 'CEmpty x a) n b -> Canonical ('Lam x n) ('TArr a b)
  CZero :: Canonical 'TZero 'TNat
  CSuc  :: Value v -> HasType 'CEmpty v 'TNat -> Canonical ('TSuc v) 'TNat

-- | Every closed well-typed value has a canonical form matching its type.
canonical :: HasType 'CEmpty v a -> Value v -> Canonical v a
canonical (TLam tn)  VLam      = CLam tn
canonical TZeroT     VZero     = CZero
canonical (TSucT tv) (VSuc vv) = CSuc vv tv
```

## Structural context lemmas for Preservation (`ext`, `rename`, `weaken`, `drop`, `swap`)

Before proving substitution and preservation, PLFA develops context renaming
and its corollaries. Every single one of these structural lemmas ports
directly to Dependent Haskell:

```haskell
-- | Extend a context inclusion under a newly bound variable `x : a`.
extCtx :: (forall y b. Lookup g y b -> Lookup d y b)
       -> Lookup ('CExt g x a) y b
       -> Lookup ('CExt d x a) y b
extCtx _   LZ         = LZ
extCtx rho (LS neq p) = LS neq (rho p)

-- | Rename (or map) variable lookups throughout a typing derivation.
renameTyping :: (forall y b. Lookup g y b -> Lookup d y b)
             -> HasType g m a
             -> HasType d m a
renameTyping rho (TVar p)          = TVar (rho p)
renameTyping rho (TLam tn)         = TLam (renameTyping (extCtx rho) tn)
renameTyping rho (TApp tl tm)      = TApp (renameTyping rho tl) (renameTyping rho tm)
renameTyping _   TZeroT            = TZeroT
renameTyping rho (TSucT tm)        = TSucT (renameTyping rho tm)
renameTyping rho (TCaseT tl tm tn) =
  TCaseT (renameTyping rho tl) (renameTyping rho tm) (renameTyping (extCtx rho) tn)
renameTyping rho (TMuT tm)         = TMuT (renameTyping (extCtx rho) tm)

-- | A closed term is well-typed in any context `g`.
weakenTyping :: HasType 'CEmpty m a -> HasType g m a
weakenTyping = renameTyping (\case {})

-- | Drop a shadowed duplicate binding for `x` from the context.
dropTyping :: HasType ('CExt ('CExt g x a) x b) m c
           -> HasType ('CExt g x b) m c
dropTyping = renameTyping dropLookup
  where
    dropLookup :: Lookup ('CExt ('CExt g x a) x b) y c -> Lookup ('CExt g x b) y c
    dropLookup LZ                = LZ
    dropLookup (LS neq LZ)       = absurd (neq Refl)
    dropLookup (LS neq (LS _ p)) = LS neq p

-- | Swap two distinct adjacent bindings `x /= y` in the context.
swapTyping :: forall g x y a b m c.
              Not (x :~: y)
           -> HasType ('CExt ('CExt g x a) y b) m c
           -> HasType ('CExt ('CExt g y b) x a) m c
swapTyping xNeqY = renameTyping swapLookup
  where
    swapLookup :: Lookup ('CExt ('CExt g x a) y b) z d
               -> Lookup ('CExt ('CExt g y b) x a) z d
    swapLookup LZ                         = LS (\Refl -> xNeqY Refl) LZ
    swapLookup (LS _ LZ)                  = LZ
    swapLookup (LS zNeqY (LS zNeqX rest)) = LS zNeqX (LS zNeqY rest)
```

## Progress, Substitution Lemma, and Preservation (`progress`, `substTyping`, `preserve`)

<div class="wip-notice">
<strong>[WIP NOTICE — Progress &amp; Preservation wait on published open equations for <code>Syntax.substTerm</code> (R13/R16)]</strong>
Every structural ingredient of Progress and Preservation (<code>canonical</code>,
<code>extCtx</code>, <code>renameTyping</code>, <code>weakenTyping</code>,
<code>dropTyping</code>, and <code>swapTyping</code>) checks directly on
published GHC <code>1a02a866e7</code>!
<br><br>
An earlier revision of this chapter checked <code>progress</code> against a
<code>Step</code> relation whose unqualified <code>substTerm</code> silently
bound a fresh unconstrained type variable (see the soundness note in
<a href="/Lambda/">Lambda</a>). Once the compiler team's split-module
<code>Syntax.substTerm</code> support (verified on private
<code>09bc6546ca</code>, where wrong <code>BetaMu</code> endpoints are rejected
with <code>GHC-83865</code>) publishes to a normal compiler release, both
<strong>Progress</strong> and full <strong>Preservation</strong>:
<pre class="wip"><code>progress    :: HasType 'CEmpty m a -&gt; Progress m
substTyping :: HasType ('CExt g x a) n b
            -&gt; HasType 'CEmpty v a
            -&gt; HasType g (Syntax.substTerm n x v) b
preserve    :: HasType 'CEmpty m a -&gt; Step m n -&gt; HasType 'CEmpty n a</code></pre>
will slot directly into this chapter with zero workarounds and a sound
<code>Step</code> interface. See minimal reproducer
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_SubstTermOpenEq.hs"><code>reproducers/R13_SubstTermOpenEq.hs</code></a>.
</div>

## Changes from PLFA

- Adapted from [Properties](https://plfa.inf.ed.ac.uk/Properties/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/Properties.lagda.md)).
- `Canonical`, `canonical`, `extCtx`, `renameTyping`, `weakenTyping`,
  `dropTyping`, and `swapTyping` are all **checked direct ports** passing
  `-dcore-lint -dstg-lint`.
- `progress`, `substTyping`, and `preserve` are marked `[WIP NOTICE]` on
  published GHC `1a02a866e7` until `Syntax.substTerm` open equations publish
  (`R13_SubstTermOpenEq.hs`), ensuring no checked theorem relies on the
  unconstrained fresh-tyvar `Step` interface.
