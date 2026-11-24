---
title: "Substitution: Simultaneous substitution and σ-calculus"
prev: /BigStep/
next: /Confluence/
src: content/part2/Substitution.md
module: PLFH.Part2.Substitution
plfaChapter: https://plfa.inf.ed.ac.uk/Substitution/
plfaAuthors: "Philip Wadler, Wen Kokke, and Jeremy G. Siek"
---

When proving deep metatheorems about lambda calculi—such as **Confluence**
([Confluence](/Confluence/)), **Big-Step/Small-Step Equivalence**, or
**Barendregt's Substitution Lemma** (`M [ x := N ] [ y := L ] = M [ y := L ] [ x := N [ y := L ] ]`)—ad-hoc inductions over single-variable substitution quickly
become tangled in variable-shifting arithmetic.

In PLFA's **Substitution** chapter (following Abadi, Cardelli, Curien, and
Lévy's **σ-calculus** of explicit substitutions, and Steven Schäfer, Tobias
Tebbi, and Gert Smolka's Autosubst framework), simultaneous renamings and
substitutions are packaged into a small **algebraic calculus** governed by a
handful of clean equational laws:

```text
Identity:           M [ ids ]            ≡  M
Composition:        (M [ σ ]) [ τ ]      ≡  M [ σ ⨟ τ ]
Head & Tail:        0 [ M • σ ]          ≡  M
                    (S x) [ M • σ ]      ≡  σ x
Shift & Cons:       ↑ ⨟ (M • σ)          ≡  σ
Eta:                (0 • ↑)              ≡  ids
Distributivity:     (M • σ) ⨟ τ          ≡  (M [ τ ]) • (σ ⨟ τ)
```

Once those algebraic identities are in place, Barendregt's substitution lemma
and commutation of parallel reduction become short equational calculations
rather than tedious index gymnastics!

## Imports

```haskell
{-# LANGUAGE DependentTypes #-}
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
  , subIdL
  , subApp
  ) where

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

## Renamings, Substitutions, and σ-calculus combinators

A **renaming** `Rename m n` maps variables in scope depth `m` to variables in
scope depth `n`, while a **substitution** `Subst m n` maps variables in depth
`m` to arbitrary terms in depth `n`:

- **`ids`**: the identity substitution mapping every variable `x` to `UVar x`.
- **`shift`** (`↑`): the shift renaming `FS` incrementing every de Bruijn index
  by `1` (weakening a term by inserting an unused binder at slot `0`).
- **`ren`**: promotes any renaming `rho` to a substitution `\x -> UVar (rho x)`.
- **`consSubst`** (`M • σ`): prepends a term `t` for variable `FZ` onto an
  existing substitution `sigma` for all outer variables `FS x`.
- **`seqSubst`** (`σ ⨟ τ`): sequential composition—first apply `σ` to variable
  `x`, then apply `τ` to the resulting term via `substU`!

Notice how single-variable substitution `substSingleU b w` from
[Untyped](/Untyped/) is simply `substU (consSubst w ids) b` (`b [ w • ids ]`),
and lifting a substitution under a binder (`extsU sigma`) is simply
`consSubst (UVar FZ) (seqSubst sigma (ren shift))` (`0 • (σ ⨟ ren ↑)`)!

```haskell
-- | A simultaneous renaming from scope depth `m` to scope depth `n`.
type Rename (m :: Nat) (n :: Nat) = Fin m -> Fin n

-- | A simultaneous substitution mapping variables in depth `m` to terms in depth `n`.
type Subst (m :: Nat) (n :: Nat) = Fin m -> UTerm n

-- | Identity substitution: maps each variable to itself.
ids :: Subst m m
ids = UVar

-- | Shift renaming: increments every de Bruijn variable by one (`↑` / `S_`).
shift :: Rename m (Succ m)
shift = FS

-- | Lift a renaming to a substitution.
ren :: Rename m n -> Subst m n
ren rho x = UVar (rho x)

-- | Extend a substitution with a new term for variable 0 (`M • σ`).
consSubst :: UTerm n -> Subst m n -> Subst (Succ m) n
consSubst t _     FZ     = t
consSubst _ sigma (FS x) = sigma x

-- | Sequential composition of substitutions (`σ ⨟ τ`).
seqSubst :: Subst m n -> Subst n p -> Subst m p
seqSubst sigma tau x = substU tau (sigma x)
```

## Runtime σ-calculus combinator examples

Several σ-calculus operations compute directly at runtime on variables and
applications (note that these are value-level computations, not yet
propositional equality theorems `(:~:)`):

```haskell
-- | Head lookup: `(t • σ) 0` computes to `t`.
subHead :: UTerm n -> Subst m n -> UTerm n
subHead t sigma = consSubst t sigma FZ

-- | Tail lookup: `(t • σ) (FS x)` computes to `σ x`.
subTail :: UTerm n -> Subst m n -> Fin m -> UTerm n
subTail t sigma x = consSubst t sigma (FS x)

-- | Left identity on variables: `substU sigma (UVar x)` computes to `sigma x`.
subIdL :: Subst m n -> Fin m -> UTerm n
subIdL sigma x = substU sigma (UVar x)

-- | Distributing substitution over application.
subApp :: Subst m n -> UTerm m -> UTerm m -> UTerm n
subApp sigma l m = substU sigma (UApp l m)
```

## Proving σ-calculus equational identities (`sub-id`, `sub-sub`, `sub-dist`)

<div class="wip-notice">
<strong>[WIP NOTICE — Equational σ-calculus proofs over GADT terms &amp; functions (R04/R16 + Function Extensionality)]</strong>
Stating PLFA's equational substitution identities directly as Dependent
Haskell types, such as:
<pre class="wip"><code>subId  :: foreach (t :: UTerm n) -&gt; substU ids t :~: t
subSub :: foreach (s1 :: Subst m n) -&gt; foreach (s2 :: Subst n p)
       -&gt; foreach (t :: UTerm m)
       -&gt; substU s2 (substU s1 t) :~: substU (seqSubst s1 s2) t</code></pre>
requires both (1) reducing abstract function-valued <code>foreach</code>
binders and higher-order substitutions in types (tracked in
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R16_AbstractRenamingInType.hs"><code>R16_AbstractRenamingInType.hs</code></a>)
and (2) function extensionality (which PLFA postulates via
<code>extensionality</code> for the substitution-algebra equations).
All σ-calculus definitions and runtime combinators above compile cleanly with
<code>-dcore-lint -dstg-lint</code>.
</div>

## Exercises

#### Exercise `substSingle-as-cons` (practice)

Check by hand that `substU (consSubst w ids) t` evaluates to the exact same
result as `substSingleU t w` from [Untyped](/Untyped/) on every term `t`.

#### Exercise `exts-as-sigma` (recommended)

Verify on `FZ` and `FS x` that `extsU sigma` agrees pointwise with
`consSubst (UVar FZ) (seqSubst sigma (ren shift))`, explaining why the
σ-calculus eliminates `extsU` as a primitive combinator!

## Changes from PLFA

- Adapted from [Substitution](https://plfa.inf.ed.ac.uk/Substitution/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/Substitution.lagda.md))
  by Philip Wadler, Wen Kokke, and Jeremy G. Siek (CC BY 4.0).
- Checked direct ports of `Rename`, `Subst`, `ids`, `shift`, `ren`,
  `consSubst`, `seqSubst`, and the computational σ-calculus combinators with
  zero promoted-constructor ticks.
- Marked the equational substitution proofs (`sub-id`, `sub-sub`, `sub-dist`)
  with `[WIP NOTICE]` pointing to `R16_AbstractRenamingInType.hs` and function
  extensionality.
