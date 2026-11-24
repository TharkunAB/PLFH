---
title: "BigStep: Big-step call-by-name operational semantics"
prev: /Bisimulation/
next: /Substitution/
src: content/part2/BigStep.md
module: PLFH.Part2.BigStep
plfaChapter: https://plfa.inf.ed.ac.uk/BigStep/
plfaAuthors: "Philip Wadler, Wen Kokke, and Jeremy G. Siek"
---

Up to now we have defined operational semantics in **small-step** (structural
operational semantics) style, describing a single elementary reduction step
`M —→ N` at a time. In this chapter (following PLFA's **BigStep** chapter by
Philip Wadler, Wen Kokke, and Jeremy G. Siek), we define an alternative style
due to Gilles Kahn: **big-step** (or *natural*) operational semantics, written
`e ⊢ M ⇓ c`, which relates an expression directly to its final evaluated result!

Even more importantly, we make two design choices that prepare directly for
Part 3 ([Denotational Semantics](/Denotational/) and [Adequacy](/Adequacy/)):

1. **Environments and closures instead of substitution:** Rather than
   rewriting syntax every time a function is called, we evaluate a term `UTerm n`
   in an **environment** `Env n` mapping its `n` free de Bruijn variables to
   **closures** `Clos`—pairs `<M, e>` bundling a term with the environment in
   which its free variables live (just like a real interpreter!).
2. **Call-by-name evaluation:** When evaluating an application `UApp l m`, we do
   *not* evaluate the argument `m` first; we simply wrap `m` together with the
   current environment `e` into an unevaluated thunk `MkClos m e` and push it
   onto the callee's environment! Thus `(λ x y. x) Ω` terminates immediately
   without ever touching the diverging term `Ω` (verified in `evalConstOmega`
   below!).

## Imports

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
{-# OPTIONS_GHC -fwrite-source-equations #-}
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
  , evalKIdOmega
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..))
import PLFH.Part2.Untyped (Fin (..), IdTerm, OmegaTerm, UTerm (..))
```

## Environments, closures, and lookup

Notice the mutual recursion between `Env n` and `Clos`:
- `Env n` is a length-indexed list of `n` closures (`ENil` has length `Zero`;
  `ECons c e` adds closure `c` at de Bruijn index `FZ`).
- `Clos` existentially hides the scope depth `n` of a term `UTerm n` together
  with a matching environment `Env n` that closes all `n` of its free variables!

Because `Env n` and `Fin n` share the same scope depth `n`, runtime lookup
`lookupEnv :: Env n -> Fin n -> Clos` is **total**—no `Maybe` or out-of-bounds
error is possible!

```haskell
-- | Closure environment matching de Bruijn scope depth `n`.
data Env (n :: Nat) where
  ENil  :: Env Zero
  ECons :: Clos -> Env n -> Env (Succ n)

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

Our big-step judgment `EvalBig e t v` (`e ⊢ t ⇓ v`) has just **three rules**—one
for each constructor of `UTerm`:

- **`EVar`**: Look up variable `x` in `e` via relational `EnvLookup` to obtain
  its suspended closure `MkClos m d`, and force it by evaluating `d ⊢ m ⇓ v`.
- **`ELam`**: A lambda abstraction `ULam b` is already in weak-head normal form,
  so it evaluates immediately to the closure `MkClos (ULam b) e` capturing the
  current environment `e`.
- **`EApp`**: Evaluate the operator `l` in `e` until it produces a lambda
  closure `MkClos (ULam b) d`, then evaluate the body `b` in `d` extended with
  the **unevaluated** argument closure `MkClos m e`!

Notice that GHC promotes the mutually recursive GADTs `Env n`, `Clos`, and
`UTerm n` simultaneously so `EvalBig` is directly indexed over all three!

```haskell
-- | Relational environment lookup: variable `x` maps to closure `c` in `e`.
type EnvLookup :: forall (n :: Nat). Env n -> Fin n -> Clos -> Type
data EnvLookup e x c where
  ELZ :: EnvLookup (ECons c e) FZ c
  ELS :: EnvLookup e x c -> EnvLookup (ECons c' e) (FS x) c

-- | Call-by-name big-step evaluation: in environment `e`, term `t` evaluates to closure `v`.
type EvalBig :: forall (n :: Nat). Env n -> UTerm n -> Clos -> Type
data EvalBig e t v where
  EVar :: EnvLookup e x (MkClos m d) -> EvalBig d m v -> EvalBig e (UVar x) v
  ELam :: EvalBig e (ULam b) (MkClos (ULam b) e)
  EApp :: EvalBig e l (MkClos (ULam b) d)
       -> EvalBig (ECons (MkClos m e) d) b w
       -> EvalBig e (UApp l m) w
```

### Concrete derivations: `(λx. x) (λy. y)` and `(λx y. x) Ω`

In `evalConstOmega`, we verify PLFA's classic demonstration of call-by-name
laziness: applying the constant function `λ x y. x` to the diverging term `Ω`
terminates in just *two* big-step rules (`EApp ELam ELam`), capturing `Ω`
unevaluated inside the resulting closure environment!

And `evalBigIsLam` confirms that *every* converging big-step evaluation
produces a lambda closure (weak-head normal form):

```haskell
-- | Concrete call-by-name derivation: (λx. x) (λy. y) ⇓ <λy. y, []>.
evalIdApp :: EvalBig ENil
                     (UApp (ULam (UVar FZ)) (ULam (UVar FZ)))
                     (MkClos (ULam (UVar FZ)) ENil)
evalIdApp = EApp ELam (EVar ELZ ELam)

-- | PLFA BigStep exercise: (λx y. x) Ω terminates under call-by-name
-- because Ω is captured unevaluated in the closure environment!
evalConstOmega :: EvalBig ENil
  (UApp (ULam (ULam (UVar (FS FZ))))
        (UApp (ULam (UApp (UVar FZ) (UVar FZ)))
              (ULam (UApp (UVar FZ) (UVar FZ)))))
  (MkClos (ULam (UVar (FS FZ)))
          (ECons (MkClos (UApp (ULam (UApp (UVar FZ) (UVar FZ)))
                               (ULam (UApp (UVar FZ) (UVar FZ)))) ENil) ENil))
evalConstOmega = EApp ELam ELam

-- | PLFA BigStep exercise `eval-K-id-omega`: `((λx y. x) (λz. z)) Ω ⇓ <λz. z, []>`,
-- forcing only the first argument and leaving Ω completely untouched!
evalKIdOmega
  :: EvalBig ENil
       (UApp (UApp (ULam (ULam (UVar (FS FZ)))) IdTerm) OmegaTerm)
       (MkClos IdTerm ENil)
evalKIdOmega = EApp (EApp ELam ELam) (EVar (ELS ELZ) ELam)

-- | Witness that a closure's term is a lambda abstraction (weak-head normal form).
data IsLamClos (c :: Clos) where
  MkIsLamClos :: IsLamClos (MkClos (ULam b) e)

-- | Every call-by-name big-step evaluation produces a lambda closure!
evalBigIsLam :: EvalBig e m c -> IsLamClos c
evalBigIsLam (EVar _ ev)  = evalBigIsLam ev
evalBigIsLam ELam         = MkIsLamClos
evalBigIsLam (EApp _ ev2) = evalBigIsLam ev2
```

## Determinism (`⇓-determ`)

Unlike full β-reduction in [Untyped](/Untyped/), call-by-name big-step
evaluation is **deterministic**: if `e ⊢ m ⇓ c₁` and `e ⊢ m ⇓ c₂`, then
`c₁ :~: c₂`! Both `envLookupDeterm` and `evalDeterm` prove in three lines by
structural induction—and `evalDeterm` directly powers the join case of our
unconditional **Big-Step Adequacy** proof in [Adequacy](/Adequacy/)!

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

## Functional lookup across a module boundary

The variable rule above carries an `EnvLookup` derivation (`ELZ` selects the
first closure, `ELS` continues in the tail). Because `PLFH.Part2.BigStep`
compiles with `-fwrite-source-equations`, GHC publishes checked equations for
the ordinary `lookupEnv` function into `BigStep.hi`!

In the companion client module `PLFH.Part2.BigStepFunctional`
(`clients/PLFH/Part2/BigStepFunctional.hs`), the variable rule constrains
`B.lookupEnv e x` directly—matching PLFA's functional variable rule with zero
promoted-constructor ticks:

```{.haskell .spec}
Var :: (B.lookupEnv e x ~ B.MkClos m d) => Eval d m v -> Eval e (UVar x) v
```

`PLFH.Part2.BigStepFunctional` proves `lookupEvidence :: EnvLookup e x c -> lookupEnv e x :~: c`,
converts every relational derivation via `fromBigStep :: EvalBig e t v -> Eval e t v`,
proves direct `evalDeterm`, and checks both `evalIdApp` (at `FZ`) and
`evalKIdOmega` (at `FS FZ`).

### Negative control: wrong functional lookup target is rejected

Attempting to claim that `((λx y. x) id) Ω` evaluates to a different closure
(such as `MkClos OmegaTerm ENil` instead of `MkClos IdTerm ENil`) via
`BigStepFunctional.Eval` is rejected by GHC with `GHC-83865`:

```{.haskell .fail name="NegBigStepBadLookup" expect="GHC-83865"}
{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs #-}
module NegBigStepBadLookup (badLookup) where

import qualified PLFH.Part2.BigStep as B
import PLFH.Part2.BigStepFunctional (Eval (..))
import PLFH.Part2.Untyped (Fin (..), IdTerm, OmegaTerm, UTerm (..))

-- MUST FAIL: `FS FZ` looks up `IdTerm`, NOT `OmegaTerm`!
badLookup
  :: Eval B.ENil
          (UApp (UApp (ULam (ULam (UVar (FS FZ)))) IdTerm) OmegaTerm)
          (B.MkClos OmegaTerm B.ENil)
badLookup = App (App Lam Lam) (Var Lam)
```

<div class="wip-notice">
<strong>[WIP NOTICE — Same-module functional <code>lookupEnv</code> (R13/R21)]</strong>
<code>-fwrite-source-equations</code> publishes checked equations for
<code>lookupEnv</code> into the compiled interface for downstream modules such
as <code>PLFH.Part2.BigStepFunctional</code>; using <code>lookupEnv</code>
inside a datatype declared in the <em>same</em> module still reports
<code>GHC-68947</code>. See
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_LookupEnvOpenEq.hs"><code>reproducers/R13_LookupEnvOpenEq.hs</code></a>.
</div>

## Exercises

#### Exercise `eval-K-id-omega` (practice)

Construct an `EvalBig ENil` derivation showing that `((λ x y. x) (λ z. z)) Ω`
evaluates to `MkClos (ULam (UVar FZ)) ENil`, and check that `Ω` is never forced!

#### Exercise `omega-diverges` (recommended)

Explain why there is no finite `EvalBig ENil OmegaTerm c` derivation for any
closure `c`: applying `EApp` to `OmegaTerm` requires evaluating the body
`UApp (UVar FZ) (UVar FZ)` in an environment mapping `FZ` back to `SelfApp`,
which requires another strictly smaller sub-derivation of the exact same
problem—contradicting well-founded induction on `EvalBig`!

## Changes from PLFA

- Adapted from [BigStep](https://plfa.inf.ed.ac.uk/BigStep/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/BigStep.lagda.md))
  by Philip Wadler, Wen Kokke, and Jeremy G. Siek (CC BY 4.0).
- Checked direct ports of call-by-name `Env`, `Clos`, `lookupEnv`, `EnvLookup`,
  `EvalBig`, `evalBigIsLam`, `envLookupDeterm`, `evalDeterm`, `evalIdApp`,
  `evalConstOmega`, and `evalKIdOmega`, plus functional `B.lookupEnv` across
  the module boundary in `PLFH.Part2.BigStepFunctional` (verified by negative
  control `NegBigStepBadLookup`), with zero promoted-constructor ticks.
- Same-module functional `lookupEnv e x` in `EVar` remains tracked in
  `R13_LookupEnvOpenEq.hs`.
