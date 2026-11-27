---
title: "BigStep: Big-step call-by-name operational semantics"
prev: /substitution/
next: /confluence/
src: content/part2/BigStep.md
module: PLFH.Part2.BigStep
plfaChapter: https://plfa.inf.ed.ac.uk/BigStep/
---

Up to now we have defined operational semantics in **small-step** (structural
operational semantics) style, describing a single elementary reduction step
`M —→ N` at a time. In this chapter (following PLFA's **BigStep** chapter by
Philip Wadler, Wen Kokke, and Jeremy G. Siek), we define an alternative style
due to Gilles Kahn: **big-step** (or *natural*) operational semantics, written
`e ⊢ M ⇓ c`, which relates an expression directly to its final evaluated result.

Even more importantly, we make two design choices that prepare directly for
Part 3 ([Denotational Semantics](/denotational/) and [Adequacy](/adequacy/)):

1. **Environments and closures instead of substitution:** Rather than
   rewriting syntax every time a function is called, we evaluate a term `UTerm n`
   in an **environment** `Env n` mapping its `n` free de Bruijn variables to
   **closures** `Clos`, pairs `<M, e>` bundling a term with the environment in
   which its free variables live (just like a real interpreter).
2. **Call-by-name evaluation:** When evaluating an application `UApp l m`, we do
   *not* evaluate the argument `m` first; we simply wrap `m` together with the
   current environment `e` into an unevaluated thunk `MkClos m e` and push it
   onto the callee's environment. Thus `(λ x y. x) Ω` terminates immediately
   without ever touching the diverging term `Ω` (verified in `evalConstOmega`
   below).

## Imports

```{.haskell}
{-# LANGUAGE AllowAmbiguousTypes, DependentTypes #-}
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
  , IsSelfApp (..)
  , selfAppEval
  , omegaLoopDiverges
  , omegaDiverges
  , EvalFun (..)
  , lookupEnvEvidence
  , toEvalFun
  , evalFunDeterm
  , evalFunKIdOmega
  , idClos
  , evalIdApp
  , evalConstOmega
  , evalKIdOmega
  , CloseEnv (..)
  , CbnRes (..)
  , cbnSim
  , CbnTerminates (..)
  , cbnToReduceW
  , cbnToReduce
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void)
import Data.Nat.Dependent (Nat (..))
import PLFH.Part1.Negation (Not)
import PLFH.Part2.Substitution
  ( HasTerm (..)
  , SubW
  , Subst
  , consSubst
  , consW
  , evalSubst
  , extsSingleBeta
  , ids
  , idsW
  , subId
  , termWToHas
  )
import PLFH.Part2.Untyped
  ( BetaStep (..)
  , BetaSteps (..)
  , Fin (..)
  , IdTerm
  , OmegaTerm
  , SelfApp
  , TermW (..)
  , UTerm (..)
  , bsApp1
  , bsTrans
  , extsU
  , mkTermW
  , substU
  )
```

## Environments, closures, and lookup

Notice the mutual recursion between `Env n` and `Clos`:
- `Env n` is a length-indexed list of `n` closures (`ENil` has length `Zero`;
  `ECons c e` adds closure `c` at de Bruijn index `FZ`).
- `Clos` existentially hides the scope depth `n` of a term `UTerm n` together
  with a matching environment `Env n` that closes all `n` of its free variables.

Because `Env n` and `Fin n` share the same scope depth `n`, runtime lookup
`lookupEnv :: Env n -> Fin n -> Clos` is **total**, no `Maybe` or out-of-bounds
error is possible.

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

Our big-step judgment `EvalBig e t v` (`e ⊢ t ⇓ v`) has just **three rules**, one
for each constructor of `UTerm`:

- **`EVar`**: Look up variable `x` in `e` via relational `EnvLookup` to obtain
  its suspended closure `MkClos m d`, and force it by evaluating `d ⊢ m ⇓ v`.
- **`ELam`**: A lambda abstraction `ULam b` is already in weak-head normal form,
  so it evaluates immediately to the closure `MkClos (ULam b) e` capturing the
  current environment `e`.
- **`EApp`**: Evaluate the operator `l` in `e` until it produces a lambda
  closure `MkClos (ULam b) d`, then evaluate the body `b` in `d` extended with
  the unevaluated argument closure `MkClos m e`.

<div class="rule-group">
  <div class="inference-rule">
    <div class="premises"><span>e(x) = ⟨M, d⟩</span><span>d ⊢ M ⇓ v</span></div>
    <div class="conclusion">e ⊢ x ⇓ v</div>
    <div class="rule-name">(EVar)</div>
  </div>
  <div class="inference-rule">
    <div class="premises">&nbsp;</div>
    <div class="conclusion">e ⊢ λ b ⇓ ⟨λ b, e⟩</div>
    <div class="rule-name">(ELam)</div>
  </div>
  <div class="inference-rule">
    <div class="premises"><span>e ⊢ L ⇓ ⟨λ b, d⟩</span><span>⟨M, e⟩ : d ⊢ b ⇓ w</span></div>
    <div class="conclusion">e ⊢ L · M ⇓ w</div>
    <div class="rule-name">(EApp)</div>
  </div>
</div>

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
unevaluated inside the resulting closure environment.

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

Unlike full β-reduction in [Untyped](/untyped/), call-by-name big-step
evaluation is **deterministic**: if `e ⊢ m ⇓ c₁` and `e ⊢ m ⇓ c₂`, then
`c₁ :~: c₂`. Both `envLookupDeterm` and `evalDeterm` prove in three lines by
structural induction, and `evalDeterm` directly powers the join case of
**Big-Step Adequacy** in [Adequacy](/adequacy/).

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

## Proving divergence: `Ω` has no big-step derivation (`omega-diverges`)

In big-step semantics, a diverging program is simply one with **no finite
derivation** `EvalBig ENil m c`. To prove `Not (EvalBig ENil OmegaTerm c)` by
structural induction on `EvalBig`, notice that each application step wraps `SelfApp`
inside another environment indirection `(UVar FZ, ECons ...)`. Capturing that
chain with the inductive invariant `IsSelfApp e m` yields a 6-line proof of
**`omegaDiverges`**, which in [Adequacy](/adequacy/) immediately proves that `Ω`
cannot denote any non-trivial function value.

```haskell
-- | Inductive invariant for closures that dereference to `<SelfApp, []>`:
-- either `SelfApp = λx. x x` directly in `ENil`, or a variable pointing to one.
type IsSelfApp :: forall (n :: Nat). Env n -> UTerm n -> Type
data IsSelfApp e m where
  SelfAppDirect :: IsSelfApp ENil SelfApp
  SelfAppVar    :: EnvLookup e x (MkClos m d) -> IsSelfApp d m -> IsSelfApp e (UVar x)

-- | Any `IsSelfApp` closure that evaluates must produce `<SelfApp, []>`.
selfAppEval :: IsSelfApp e m -> EvalBig e m c -> c :~: MkClos SelfApp ENil
selfAppEval SelfAppDirect       ELam          = Refl
selfAppEval (SelfAppVar lk1 sa) (EVar lk2 ev) = case envLookupDeterm lk1 lk2 of
  Refl -> selfAppEval sa ev

-- | Applying any two `IsSelfApp` closures cannot terminate under `EvalBig`.
omegaLoopDiverges :: IsSelfApp e m1 -> IsSelfApp e m2 -> EvalBig e (UApp m1 m2) c -> Void
omegaLoopDiverges sa1 sa2 (EApp ev1 ev2) = case selfAppEval sa1 ev1 of
  Refl -> omegaLoopDiverges (SelfAppVar ELZ sa2) (SelfAppVar ELZ sa2) ev2

-- | Exercise `omega-diverges`: `Ω = (λx. x x) (λx. x x)` has no big-step derivation!
omegaDiverges :: Not (EvalBig ENil OmegaTerm c)
omegaDiverges = omegaLoopDiverges SelfAppDirect SelfAppDirect
```

## Functional environment lookup (`EvalFun`)

The variable rule `EVar` above uses the inductive relation `EnvLookup`, which
we use directly in [Adequacy](/adequacy/). Under `-XDependentTypes`, GHC
publishes checked equations for the ordinary `lookupEnv` function, so we can
also state PLFA's functional variable rule directly via `EvalFun`:

```haskell
-- | Call-by-name big-step evaluation using ordinary `lookupEnv` in the same module!
type EvalFun :: forall (n :: Nat). Env n -> UTerm n -> Clos -> Type
data EvalFun e t v where
  EFVar :: (lookupEnv e x ~ MkClos m d) => EvalFun d m v -> EvalFun e (UVar x) v
  EFLam :: EvalFun e (ULam b) (MkClos (ULam b) e)
  EFApp :: EvalFun e l (MkClos (ULam b) d)
        -> EvalFun (ECons (MkClos m e) d) b w
        -> EvalFun e (UApp l m) w

-- | Relational `EnvLookup` agrees with functional `lookupEnv`.
lookupEnvEvidence :: EnvLookup e x c -> lookupEnv e x :~: c
lookupEnvEvidence ELZ     = Refl
lookupEnvEvidence (ELS p) = lookupEnvEvidence p

-- | Convert any relational `EvalBig` derivation to functional `EvalFun`.
toEvalFun :: EvalBig e t v -> EvalFun e t v
toEvalFun (EVar lk ev) = case lookupEnvEvidence lk of
  Refl -> EFVar (toEvalFun ev)
toEvalFun ELam         = EFLam
toEvalFun (EApp e1 e2) = EFApp (toEvalFun e1) (toEvalFun e2)

-- | Determinism of functional `EvalFun`: no lookup lemma needed.
evalFunDeterm :: EvalFun e m c1 -> EvalFun e m c2 -> c1 :~: c2
evalFunDeterm (EFVar e1)    (EFVar e2)    = evalFunDeterm e1 e2
evalFunDeterm EFLam         EFLam         = Refl
evalFunDeterm (EFApp l1 b1) (EFApp l2 b2) = case evalFunDeterm l1 l2 of
  Refl -> evalFunDeterm b1 b2

-- | Functional lookup for `((λx y. x) id) Ω ⇓ <id, []>` at `FS FZ`.
evalFunKIdOmega
  :: EvalFun ENil
       (UApp (UApp (ULam (ULam (UVar (FS FZ)))) IdTerm) OmegaTerm)
       (MkClos IdTerm ENil)
evalFunKIdOmega = EFApp (EFApp EFLam EFLam) (EFVar EFLam)
```

### Rejected example: wrong functional lookup target

Claiming that `((λx y. x) id) Ω` evaluates to `MkClos OmegaTerm ENil` instead
of `MkClos IdTerm ENil` via `EvalFun` is rejected by GHC with `GHC-83865`:

```{.haskell .fail name="NegBigStepBadLookup" expect="GHC-83865"}
{-# LANGUAGE DependentTypes #-}
module NegBigStepBadLookup (badLookup) where

import PLFH.Part2.BigStep (Clos (..), Env (..), EvalFun (..))
import PLFH.Part2.Untyped (Fin (..), IdTerm, OmegaTerm, UTerm (..))

-- Rejected: `FS FZ` looks up `IdTerm`, not `OmegaTerm`.
badLookup
  :: EvalFun ENil
             (UApp (UApp (ULam (ULam (UVar (FS FZ)))) IdTerm) OmegaTerm)
             (MkClos OmegaTerm ENil)
badLookup = EFApp (EFApp EFLam EFLam) (EFVar EFLam)
```

## Big-step to small-step bridge (`cbn→reduce`)

Every converging call-by-name big-step derivation `EvalBig ENil u (MkClos (ULam b) d)`
corresponds to a real multi-step full β-reduction `BetaSteps u (ULam b')`.

To prove `cbnToReduce` constructively without axioms or function extensionality,
we associate each runtime closure environment `e :: Env n` with its closing
simultaneous substitution `s :: Subst n Zero` via the 2-constructor witness
`CloseEnv e s`:

1. **`CloseNil`** closes the empty environment `ENil` with the identity
   substitution `ids`.
2. **`CloseCons`** closes `ECons (MkClos m e) d` with
   `consSubst (substU se m) sd`, substituting each bound closure's own
   environment `se` into `m`.
3. **`cbnSim`**: by structural induction on `EvalBig e t (MkClos (ULam b) d)`,
   `substU s t` β-reduces to `ULam (substU (extsU sd) b)`. In the `EApp` case,
   one functional **`Beta`** step reduces `(λ b [exts sd]) (m [s])` to
   `(b [exts sd]) [m [s]]`, which `Substitution.extsSingleBeta` equates directly
   with `b [m [s] • sd]`.
4. **`cbnToReduceW` / `cbnToReduce`**: specializing `cbnSim` to `CloseNil` and
   rewriting `substU ids u :~: u` via `Substitution.subId` yields
   `BetaSteps u (ULam b')` in four lines.

```haskell
-- | Inductive closing witness: `p :: Subst n Zero` closes `e :: Env n` by
-- recursively applying each closure's own closing substitution.
type CloseEnv :: forall (n :: Nat). Env n -> Subst n Zero -> Type
data CloseEnv e p where
  CloseNil  :: CloseEnv ENil (ids @Zero)
  CloseCons :: forall (ne nd :: Nat) (m :: UTerm ne) (e :: Env ne)
                      (f :: Subst ne Zero) (d :: Env nd) (g :: Subst nd Zero).
               TermW m
            -> CloseEnv e f -> SubW @ne @Zero f
            -> CloseEnv d g -> SubW @nd @Zero g
            -> CloseEnv (ECons (MkClos m e) d) (consSubst (substU f m) g)

type CloseHit :: forall (nd :: Nat). UTerm Zero -> UTerm nd -> Env nd -> Type
data CloseHit u a d where
  MkCloseHit :: forall (nd :: Nat) (u :: UTerm Zero)
                       (a :: UTerm nd) (d :: Env nd) (g :: Subst nd Zero).
                TermW a -> CloseEnv d g -> SubW @nd @Zero g
             -> u :~: substU g a
             -> CloseHit u a d

lookupClose :: forall (n nd :: Nat) (e :: Env n) (p :: Subst n Zero)
                      (x :: Fin n) (a :: UTerm nd) (d :: Env nd).
               CloseEnv e p -> EnvLookup e x (MkClos a d) -> CloseHit (p x) a d
lookupClose (CloseCons wa ce swe _ _) ELZ      = MkCloseHit wa ce swe Refl
lookupClose (CloseCons _  _  _  cd _) (ELS lk) = lookupClose cd lk

consHasW :: forall (nd :: Nat) (g :: Subst nd Zero) (t :: UTerm Zero).
            HasTerm t -> SubW @nd @Zero g -> SubW @(Succ nd) @Zero (consSubst t g)
consHasW ht _  FZ     = ht
consHasW _  sw (FS x) = sw x

-- | Simulation result: a closed lambda `ULam (substU (extsU g) b)` reached via `BetaSteps`.
type CbnRes :: forall (nd :: Nat). UTerm (Succ nd) -> Env nd -> UTerm Zero -> Type
data CbnRes b d u where
  MkCbnRes :: forall (nd :: Nat) (b :: UTerm (Succ nd)) (d :: Env nd)
                     (g :: Subst nd Zero) (u :: UTerm Zero).
              TermW b -> CloseEnv d g -> SubW @nd @Zero g
           -> BetaSteps u (ULam (substU (extsU g) b))
           -> CbnRes b d u

-- | Big-step evaluation simulates into multi-step full β-reduction under closing.
cbnSim :: forall (n nd :: Nat) (e :: Env n) (p :: Subst n Zero)
                 (t :: UTerm n) (b :: UTerm (Succ nd)) (d :: Env nd).
          EvalBig e t (MkClos (ULam b) d)
       -> CloseEnv e p -> SubW @n @Zero p -> TermW t
       -> CbnRes b d (substU p t)
cbnSim ELam ce sw (WLam wb) = MkCbnRes wb ce sw BRefl
cbnSim (EVar lk ev) ce _ _ = case lookupClose ce lk of
  MkCloseHit wa ca swa Refl -> cbnSim ev ca swa wa
cbnSim (EApp (evL :: EvalBig e l (MkClos (ULam b1) (d1 :: Env nd1))) evB) ce sw (WApp wl (wm :: TermW m)) =
  case cbnSim evL ce sw wl of
    MkCbnRes (wb :: TermW b1) (cd :: CloseEnv d1 g) swd stepsL ->
      case (termWToHas wm, termWToHas wb) of
        (MkHasTerm m', MkHasTerm b') ->
          let hsm = evalSubst @n @Zero @p sw m'
              swNew :: SubW @(Succ nd1) @Zero (consSubst (substU p m) g)
              swNew = consHasW @nd1 @g @(substU p m) hsm swd
              ceNew :: CloseEnv (ECons (MkClos m e) d1) (consSubst (substU p m) g)
              ceNew = CloseCons wm ce sw cd swd
          in case hsm of
            MkHasTerm sm ->
              case extsSingleBeta @nd1 @Zero @g swd sm b' of
                Refl -> case cbnSim @(Succ nd1) @nd @(ECons (MkClos m e) d1) @(consSubst (substU p m) g)
                               evB ceNew swNew wb of
                  MkCbnRes wbRes cf swf stepsB ->
                    MkCbnRes wbRes cf swf
                      (bsTrans (bsApp1 stepsL)
                        (BCons (Beta @Zero @(substU (extsU g) b1) @(substU p m)) stepsB))

-- | Small-step termination witness: `u` β-reduces to some lambda abstraction.
data CbnTerminates (u :: UTerm Zero) where
  MkCbnTerminates :: BetaSteps u (ULam b) -> CbnTerminates u

-- | Big-step → small-step bridge (`cbn→reduce`).
cbnToReduceW :: TermW u -> EvalBig ENil u (MkClos (ULam b) d) -> CbnTerminates u
cbnToReduceW wu ev = case termWToHas wu of
  MkHasTerm u' -> case subId @Zero u' of
    Refl -> case cbnSim ev CloseNil (idsW @Zero) wu of
      MkCbnRes _ _ _ steps -> MkCbnTerminates steps

cbnToReduce :: forall (nd :: Nat) (b :: UTerm (Succ nd)) (d :: Env nd).
               foreach (u :: UTerm Zero) -> EvalBig ENil u (MkClos (ULam b) d) -> CbnTerminates u
cbnToReduce u ev = cbnToReduceW (mkTermW u) ev
```

## Exercises

### Exercise `eval-fun-to-big` (practice)

Prove the converse of `toEvalFun`:
`fromEvalFun :: EvalFun e t v -> EvalBig e t v` (hint: prove a helper
`lookupEnvToRel :: foreach (e :: Env n) -> foreach (x :: Fin n) -> EnvLookup e x (lookupEnv e x)`).

### Exercise `big-alt-implies-multi` (recommended)

Define a substitution-based big-step relation `EvalSub :: UTerm Zero -> UTerm Zero -> Type`
that substitutes arguments directly instead of carrying a closure environment
`Env`, and prove that `EvalSub m v` implies `BetaSteps m v`.

## Changes from PLFA

- Provides both relational `EvalBig` (used in [Adequacy](/adequacy/)) and functional `EvalFun` over `lookupEnv`, proving `evalDeterm`, `omegaDiverges`, and the big-step to small-step bridge `cbnToReduce` via inductive environment closing `CloseEnv`.
- Omits PLFA's prose section on Plotkin standardization.
