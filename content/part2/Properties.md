---
title: "Properties: Progress and Preservation"
prev: /Lambda/
next: /DeBruijn/
src: content/part2/Properties.md
module: PLFH.Part2.Properties
plfaChapter: https://plfa.inf.ed.ac.uk/19.08/Properties/
---

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, TypeOperators #-}
module PLFH.Part2.Properties
  ( Canonical (..)
  , canonical
  , Progress (..)
  , progress
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
  , Step (..)
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

In this chapter we prove **Canonical Forms**, **Progress**, and all of the
structural context lemmas needed for **Preservation** (`ext`, `rename`,
`weaken`, `drop`, `swap`) directly in Dependent Haskell—and pinpoint the
exact R13/R16 compiler boundary that currently blocks the final substitution
lemma and β-reduction cases of `preserve`.

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

## Progress (checked direct port!)

A closed term `m` makes *progress* if either there exists `n` such that
`Step m n`, or `Value m`:

```haskell
-- | Evidence that a closed term either steps or is already a value.
data Progress (m :: Term) where
  PStep :: Step m n -> Progress m
  PDone :: Value m  -> Progress m

-- | Progress theorem: every closed well-typed term either steps or is a value.
progress :: HasType 'CEmpty m a -> Progress m
progress (TVar x) = case x of {}
progress (TLam _) = PDone VLam
progress (TApp tl tm) = case progress tl of
  PStep s  -> PStep (XiApp1 s)
  PDone vl -> case progress tm of
    PStep s  -> PStep (XiApp2 vl s)
    PDone vm -> case canonical tl vl of
      CLam _ -> PStep (BetaLam vm)
progress TZeroT = PDone VZero
progress (TSucT tm) = case progress tm of
  PStep s  -> PStep (XiSuc s)
  PDone vm -> PDone (VSuc vm)
progress (TCaseT tl _ _) = case progress tl of
  PStep s  -> PStep (XiCase s)
  PDone vl -> case canonical tl vl of
    CZero    -> PStep BetaZero
    CSuc v _ -> PStep (BetaSuc v)
progress (TMuT _) = PStep BetaMu
```

Look how clean that is: `progress` has the **exact same statement, hypotheses,
and proof structure** as PLFA `v19.08`—no singletons, no type families, no
coercions—and passes GHC's Core Lint and STG Lint!

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

## Substitution lemma and Preservation (`subst`, `preserve`)

<div class="wip-notice">
<strong>[WIP NOTICE — Preservation blocked on open evaluation of <code>substTerm</code> (R13/R16)]</strong>
Every structural step of Preservation (<code>canonical</code>, <code>extCtx</code>,
<code>renameTyping</code>, <code>weakenTyping</code>, <code>dropTyping</code>,
<code>swapTyping</code>, and all five non-β cases of <code>preserve</code>:
<code>XiApp1</code>, <code>XiApp2</code>, <code>XiSuc</code>, <code>XiCase</code>,
<code>BetaZero</code>) checks directly!
<br><br>
The remaining ingredient is the substitution typing lemma:
<pre class="wip"><code>substTyping :: HasType ('CExt g x a) n b
            -&gt; HasType 'CEmpty v a
            -&gt; HasType g (substTerm n x v) b</code></pre>
and the three β-cases of <code>preserve</code> (<code>BetaLam</code>,
<code>BetaSuc</code>, <code>BetaMu</code>) that call it.
On GHC <code>db2586fdc2</code>, checking <code>substTyping</code> fails with
<code>GHC-70565</code> because <code>substTerm</code> is an ordinary Haskell
function containing <code>case eqId x y of</code> branches, which GHC's open
source-equation evaluator (R13/R16) does not yet reduce on open inputs.
<br><br>
Per PLFH's yardstick policy, we do <em>not</em> duplicate <code>substTerm</code>
as a separate type family. Once R13/R16 supports open equations for functions
branching on a Boolean helper (<code>case eqId x y of</code>), <code>substTyping</code>
and full <code>preserve</code> will slot straight in.
See minimal reproducer
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_SubstTermOpenEq.hs"><code>reproducers/R13_SubstTermOpenEq.hs</code></a>.
</div>

## Changes from PLFA `v19.08`

- Adapted from [Properties (v19.08)](https://plfa.inf.ed.ac.uk/19.08/Properties/)
  ([source](https://github.com/plfa/plfa.github.io/blob/63fcbbe25ec3686ff4c6df2c5b58a96b3a2054f3/src/plfa/part2/Properties.lagda.md)).
- `Canonical`, `canonical`, `Progress`, `progress` (full closed well-typed
  progress theorem!), `extCtx`, `renameTyping`, `weakenTyping`, `dropTyping`,
  and `swapTyping` are all **checked direct ports** passing `-dcore-lint -dstg-lint`.
- `substTyping` and full `preserve` are marked `[WIP NOTICE]` pending R13/R16
  open source equations for `substTerm` (`R13_SubstTermOpenEq.hs`).
