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
  , idClos
  , evalIdApp
  , evalConstOmega
  ) where

import Data.Kind (Type)
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

## Determinism (`⇓-determ`) and compiler blockers

<div class="wip-notice">
<strong>[WIP NOTICE — Functional <code>lookupEnv</code> (R13) &amp; Determinism Core Lint (R11)]</strong>
Two proofs in <strong>BigStep</strong> hit tracked compiler boundaries on GHC
<code>d15cbd41fe</code>:
<ol>
  <li><strong>GADT-indexed <code>lookupEnv</code> in types (R13/R16):</strong>
      Using <code>lookupEnv e x</code> directly in <code>EVar</code> fails
      <code>GHC-68947</code>. See
      <a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_LookupEnvOpenEq.hs"><code>reproducers/R13_LookupEnvOpenEq.hs</code></a>.</li>
  <li><strong>Determinism of <code>EnvLookup</code> and <code>EvalBig</code> (R11 Core Lint):</strong>
      Even the 2-line proof
      <code>envLookupDeterm :: EnvLookup e x c1 -&gt; EnvLookup e x c2 -&gt; c1 :~: c2</code>
      (needed for <code>evalDeterm</code> and Part 3 <a href="/Adequacy/">Adequacy</a>)
      typechecks on <code>d15cbd41fe</code> and then fails Core Lint after
      Desugar with <code>R11 mixed-kind coercion binder</code> — the exact
      same Desugar Core Lint bug isolated in
      <a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R11_MixedKindCoercionCoreLint.hs"><code>reproducers/R11_MixedKindCoercionCoreLint.hs</code></a>
      (already fixed on the compiler team's private candidate <code>f21ab22285</code> / <code>d033d0132d</code>!).</li>
</ol>
</div>

## Changes from PLFA

- Adapted from [BigStep](https://plfa.inf.ed.ac.uk/BigStep/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/BigStep.lagda.md))
  by Philip Wadler, Wen Kokke, and Jeremy G. Siek (CC BY 4.0).
- Checked direct ports of call-by-name `Env`, `Clos`, `lookupEnv`, `EnvLookup`,
  `EvalBig`, `evalIdApp`, and PLFA's `(λx y. x) Ω` exercise (`evalConstOmega`).
- Marked direct functional `lookupEnv e x` (`R13_LookupEnvOpenEq.hs`) and
  `envLookupDeterm` / `evalDeterm` (`R11_MixedKindCoercionCoreLint.hs`) with
  `[WIP NOTICE]`.
