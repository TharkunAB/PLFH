---
title: "BigStep: Big-step call-by-name operational semantics"
prev: /Bisimulation/
next: /Substitution/
src: content/part2/BigStep.md
module: PLFH.Part2.BigStep
plfaChapter: https://plfa.inf.ed.ac.uk/BigStep/
plfaAuthors: "Philip Wadler, Wen Kokke, and Jeremy G. Siek"
---

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
module PLFH.Part2.BigStep
  ( Env (..)
  , Clos (..)
  , lookupEnv
  , EnvLookup (..)
  , EvalBig (..)
  , IsLamClos (..)
  , evalBigIsLam
  , envLookupDeterm
  , evalDeterm
  , idClos
  , evalIdApp
  , evalConstOmega
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..))
import PLFH.Part2.Untyped (Fin (..), UTerm (..))
```

In PLFA's **BigStep** chapter, we give a **call-by-name**
environment-and-closure big-step semantics (`e ⊢ m ⇓ c`) for the untyped lambda
calculus. Because call-by-name delays evaluating function arguments until their
value is actually needed, it aligns cleanly with the denotational semantics in
Part 3 ([Adequacy](/Adequacy/)).

## Environments, closures, and environment lookup

An environment `Env n` holds `n` closures (one for each free de Bruijn
variable in scope), and a closure `Clos` packages *any* term `UTerm n`
together with its closing environment `Env n`:

```haskell
-- | Closure environment matching de Bruijn scope depth `n`.
data Env (n :: Nat) where
  ENil  :: Env 'Zero
  ECons :: Clos -> Env n -> Env ('Succ n)

-- | A call-by-name closure pairing a term of depth `n` with its environment.
data Clos where
  MkClos :: UTerm n -> Env n -> Clos

-- | Runtime lookup of a well-scoped de Bruijn variable in a matching environment.
lookupEnv :: Env n -> Fin n -> Clos
lookupEnv (ECons c _) FZ     = c
lookupEnv (ECons _ e) (FS x) = lookupEnv e x

-- | Closure for the closed identity function λx. x.
idClos :: Clos
idClos = MkClos (ULam (UVar FZ)) ENil
```

## Call-by-name big-step evaluation (`e ⊢ m ⇓ v`)

Because calling the GADT-indexed function `lookupEnv` directly inside a type
currently hits `GHC-68947` (`R13_LookupEnvOpenEq.hs`), we state `EvalBig` using
a relational lookup `EnvLookup`:

- **`EVar`**: Look up variable `x` in `e` to obtain closure `'MkClos m d`, and
  evaluate `m` in `d`.
- **`ELam`**: A lambda abstraction evaluates immediately to its closure
  `'MkClos ('ULam b) e`.
- **`EApp`**: Evaluate operator `l` to a lambda closure `'MkClos ('ULam b) d`,
  then evaluate body `b` in `d` extended with the **unevaluated** argument
  closure `'MkClos m e`.

```haskell
-- | Relational environment lookup: variable `x` maps to closure `c` in `e`.
type EnvLookup :: forall (n :: Nat). Env n -> Fin n -> Clos -> Type
data EnvLookup e x c where
  ELZ :: EnvLookup ('ECons c e) 'FZ c
  ELS :: EnvLookup e x c -> EnvLookup ('ECons c' e) ('FS x) c

-- | Call-by-name big-step evaluation: in environment `e`, term `t` evaluates to closure `v`.
type EvalBig :: forall (n :: Nat). Env n -> UTerm n -> Clos -> Type
data EvalBig e t v where
  EVar :: EnvLookup e x ('MkClos m d) -> EvalBig d m v -> EvalBig e ('UVar x) v
  ELam :: EvalBig e ('ULam b) ('MkClos ('ULam b) e)
  EApp :: EvalBig e l ('MkClos ('ULam b) d)
       -> EvalBig ('ECons ('MkClos m e) d) b w
       -> EvalBig e ('UApp l m) w

-- | Concrete call-by-name derivation: (λx. x) (λy. y) ⇓ <λy. y, []>.
evalIdApp :: EvalBig 'ENil
                     ('UApp ('ULam ('UVar 'FZ)) ('ULam ('UVar 'FZ)))
                     ('MkClos ('ULam ('UVar 'FZ)) 'ENil)
evalIdApp = EApp ELam (EVar ELZ ELam)

-- | PLFA BigStep exercise: (λx y. x) Ω terminates under call-by-name
-- because Ω is captured unevaluated in the closure environment!
evalConstOmega :: EvalBig 'ENil
  ('UApp ('ULam ('ULam ('UVar ('FS 'FZ))))
         ('UApp ('ULam ('UApp ('UVar 'FZ) ('UVar 'FZ)))
                ('ULam ('UApp ('UVar 'FZ) ('UVar 'FZ)))))
  ('MkClos ('ULam ('UVar ('FS 'FZ)))
           ('ECons ('MkClos ('UApp ('ULam ('UApp ('UVar 'FZ) ('UVar 'FZ)))
                                   ('ULam ('UApp ('UVar 'FZ) ('UVar 'FZ)))) 'ENil) 'ENil))
evalConstOmega = EApp ELam ELam

-- | Witness that a closure's term is a lambda abstraction (weak-head normal form).
data IsLamClos (c :: Clos) where
  MkIsLamClos :: IsLamClos ('MkClos ('ULam b) e)

-- | Every call-by-name big-step evaluation produces a lambda closure!
evalBigIsLam :: EvalBig e m c -> IsLamClos c
evalBigIsLam (EVar _ ev)  = evalBigIsLam ev
evalBigIsLam ELam         = MkIsLamClos
evalBigIsLam (EApp _ ev2) = evalBigIsLam ev2
```

## Determinism (`⇓-determ`)

With the R11 Desugar Core Lint fix published on `dependent-haskell`
(`692eae0778`/`9cc4065fab`), both `envLookupDeterm` and full call-by-name
big-step determinism `evalDeterm` prove directly by structural induction—and
directly discharge the determinism premise of Part 3 [Adequacy](/Adequacy/)!

```haskell
-- | Determinism of relational environment lookup.
envLookupDeterm :: EnvLookup e x c1 -> EnvLookup e x c2 -> c1 :~: c2
envLookupDeterm ELZ      ELZ      = Refl
envLookupDeterm (ELS p1) (ELS p2) = envLookupDeterm p1 p2

-- | Determinism of call-by-name big-step evaluation (`⇓-determ`).
evalDeterm :: EvalBig e m c1 -> EvalBig e m c2 -> c1 :~: c2
evalDeterm (EVar lk1 ev1) (EVar lk2 ev2) = case envLookupDeterm lk1 lk2 of
  Refl -> evalDeterm ev1 ev2
evalDeterm ELam ELam = Refl
evalDeterm (EApp evL1 evB1) (EApp evL2 evB2) = case evalDeterm evL1 evL2 of
  Refl -> evalDeterm evB1 evB2
```

<div class="note-box">
<strong>Fixed Core Lint bug (<code>692eae0778</code> / <code>9cc4065fab</code>):</strong>
On earlier GHC baselines (<code>d15cbd41fe</code>–<code>1a02a866e7</code>),
<code>envLookupDeterm</code> and <code>evalDeterm</code> failed Desugar Core Lint
with <code>R11 mixed-kind coercion binder</code>. Fixed on
<code>dependent-haskell</code> and tracked as regression check
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/fixed/R11_MixedKindCoercionCoreLint.hs"><code>reproducers/fixed/R11_MixedKindCoercionCoreLint.hs</code></a>!
</div>

<div class="wip-notice">
<strong>[WIP NOTICE — Functional <code>lookupEnv</code> in types (R13/R16)]</strong>
Using GADT-indexed <code>lookupEnv e x</code> directly inside the type of
<code>EVar</code> (instead of relational <code>EnvLookup</code>) still fails
with <code>GHC-68947</code>. See
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_LookupEnvOpenEq.hs"><code>reproducers/R13_LookupEnvOpenEq.hs</code></a>.
</div>

## Changes from PLFA

- Adapted from [BigStep](https://plfa.inf.ed.ac.uk/BigStep/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/BigStep.lagda.md))
  by Philip Wadler, Wen Kokke, and Jeremy G. Siek (CC BY 4.0).
- Checked direct ports of call-by-name `Env`, `Clos`, `lookupEnv`, `EnvLookup`,
  `EvalBig`, `evalBigIsLam`, **`envLookupDeterm`**, **`evalDeterm`**,
  `evalIdApp`, and PLFA's `(λx y. x) Ω` exercise (`evalConstOmega`).
- Marked direct functional `lookupEnv e x` in `EVar` with `[WIP NOTICE]`
  (`R13_LookupEnvOpenEq.hs`).
