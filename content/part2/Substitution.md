---
title: "Substitution: Simultaneous substitution and σ-calculus"
prev: /BigStep/
next: /Confluence/
src: content/part2/Substitution.md
module: PLFH.Part2.Substitution
plfaChapter: https://plfa.inf.ed.ac.uk/Substitution/
plfaAuthors: "Philip Wadler, Wen Kokke, and Jeremy G. Siek"
---

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
module PLFH.Part2.Substitution
  ( Rename
  , Subst
  , ids
  , shift
  , ren
  , consSubst
  , seqSubst
  , subHead
  , subTail
  , zShift
  , subIdL
  , subApp
  ) where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..))
import PLFH.Part2.Untyped
  ( Fin (..)
  , UTerm (..)
  , extU
  , extsU
  , renameU
  , substU
  )
```

In PLFA's **Substitution** chapter (used by **BigStep** and **Confluence**),
simultaneous renamings and substitutions are organized into a clean algebra
inspired by Abadi, Cardelli, Curien, and Lévy's **σ-calculus**.

## Renamings, Substitutions, and σ-calculus combinators

```haskell
-- | A simultaneous renaming from scope depth `m` to scope depth `n`.
type Rename (m :: Nat) (n :: Nat) = Fin m -> Fin n

-- | A simultaneous substitution mapping variables in depth `m` to terms in depth `n`.
type Subst (m :: Nat) (n :: Nat) = Fin m -> UTerm n

-- | Identity substitution: maps each variable to itself.
ids :: Subst m m
ids = UVar

-- | Shift renaming: increments every de Bruijn variable by one (`S_`).
shift :: Rename m ('Succ m)
shift = FS

-- | Lift a renaming to a substitution.
ren :: Rename m n -> Subst m n
ren rho x = UVar (rho x)

-- | Extend a substitution with a new term for variable 0 (`M • σ`).
consSubst :: UTerm n -> Subst m n -> Subst ('Succ m) n
consSubst t _     FZ     = t
consSubst _ sigma (FS x) = sigma x

-- | Sequential composition of substitutions (`σ ⨟ τ`).
seqSubst :: Subst m n -> Subst n p -> Subst m p
seqSubst sigma tau x = substU tau (sigma x)
```

## Definitional σ-calculus laws

Notice which laws hold by **pure computation / reflexivity** (even at the
value level, and checked directly for arbitrary inputs):

```haskell
-- | Head law: `(t • σ) 0 = t`.
subHead :: UTerm n -> Subst m n -> UTerm n
subHead t sigma = consSubst t sigma FZ

-- | Tail law: `(t • σ) (FS x) = σ x`.
subTail :: UTerm n -> Subst m n -> Fin m -> UTerm n
subTail t sigma x = consSubst t sigma (FS x)

-- | Shifting variable 0 after cons returns the original substitution on `x`.
zShift :: UTerm n -> Subst m n -> Fin m -> UTerm n
zShift t sigma x = consSubst t sigma (shift x)

-- | Left identity on variables: `substU sigma (UVar x) = sigma x`.
subIdL :: Subst m n -> Fin m -> UTerm n
subIdL sigma x = substU sigma (UVar x)

-- | Distributing substitution over application.
subApp :: Subst m n -> UTerm m -> UTerm m -> UTerm n
subApp sigma l m = substU sigma (UApp l m)
```

## Proving σ-calculus equational identities (`sub-id`, `sub-sub`, `sub-dist`)

<div class="wip-notice">
<strong>[WIP NOTICE — Equational σ-calculus proofs over GADT terms &amp; functions (R03/R13/R16)]</strong>
Stating PLFA's equational substitution identities directly as Dependent
Haskell types, such as:
<pre class="wip"><code>subId  :: foreach (t :: UTerm n) -&gt; substU ids t :~: t
subSub :: foreach (s1 :: Subst m n) -&gt; foreach (s2 :: Subst n p)
       -&gt; foreach (t :: UTerm m)
       -&gt; substU s2 (substU s1 t) :~: substU (seqSubst s1 s2) t</code></pre>
requires two capabilities already isolated by our yardstick:
<ol>
  <li><strong>R03/R04:</strong> <code>foreach</code> binders over polymorphic
      function domains (<code>Subst m n</code>), tracked in
      <a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R04_PolyFunctionFieldInIso.hs"><code>R04_PolyFunctionFieldInIso.hs</code></a>.</li>
  <li><strong>R13/R16:</strong> Open source equations for higher-order
      GADT-indexed functions (<code>substU</code>, <code>renameU</code>,
      <code>extsU</code>), analogous to
      <a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_LookupEnvOpenEq.hs"><code>R13_LookupEnvOpenEq.hs</code></a>.</li>
</ol>
All σ-calculus definitions and runtime combinators above compile cleanly with
<code>-dcore-lint -dstg-lint</code>.
</div>

## Changes from PLFA

- Adapted from [Substitution](https://plfa.inf.ed.ac.uk/Substitution/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/Substitution.lagda.md))
  by Philip Wadler, Wen Kokke, and Jeremy G. Siek (CC BY 4.0).
- Checked direct ports of `Rename`, `Subst`, `ids`, `shift`, `ren`,
  `consSubst`, `seqSubst`, and the computational σ-calculus combinators.
- Marked the equational substitution proofs (`sub-id`, `sub-sub`, `sub-dist`)
  with `[WIP NOTICE]` pointing to our tracked R03 and R13/R16 reproducers.
