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
{-# LANGUAGE DependentTypes #-}
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
  , SubEnv (..)
  , CloseSub (..)
  , AllLift (..)
  , closeId
  , ExtendSub (..)
  , LiftedClose (..)
  , CloseSubstRes (..)
  , closeBetaSubst
  , CbnRes (..)
  , cbnSim
  , CbnTerminates (..)
  , cbnToReduceW
  , cbnToReduce
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void)
import HaskLib.Nat (Nat (..))
import PLFH.Part1.Negation (Not)
import PLFH.Part2.Confluence
  ( FinW (..)
  , LeLift (..)
  , ShiftEx (..)
  , ShiftSubstRes (..)
  , TermW (..)
  , bsApp1
  , bsTrans
  , mkTermW
  , shiftEx
  , shiftSubstLe
  , substShiftCancel
  , substTargetW
  )
import PLFH.Part2.Untyped
  ( BetaStep (..)
  , BetaSteps (..)
  , BumpFin (..)
  , Fin (..)
  , IdTerm
  , OmegaTerm
  , RemoveFin (..)
  , SelfApp
  , ShiftU (..)
  , SubstAtU (..)
  , UTerm (..)
  )
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

## Proving divergence: `Ω` has no big-step derivation (`omega-diverges`)

In big-step semantics, a diverging program is simply one with **no finite
derivation** `EvalBig ENil m c`. To prove `Not (EvalBig ENil OmegaTerm c)` by
structural induction on `EvalBig`, notice that each application step wraps `SelfApp`
inside another environment indirection `(UVar FZ, ECons ...)`. Capturing that
chain with the inductive invariant `IsSelfApp e m` yields a 6-line proof of
**`omegaDiverges`**—which in [Adequacy](/Adequacy/) immediately proves that `Ω`
cannot denote any non-trivial function value!

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

## Same-module functional lookup (`EvalFun`)

The variable rule `EVar` above uses the inductive relation `EnvLookup`, which
we use directly in [Adequacy](/Adequacy/). Under `-XDependentTypes`, GHC
automatically publishes checked equations for the ordinary `lookupEnv` function
in **both the same module and downstream modules** (`PLFH.Part2.BigStepFunctional`),
so we can state PLFA's functional variable rule directly right here in `BigStep`
with zero promoted-constructor ticks:

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

-- | Convert any relational `EvalBig` derivation to same-module functional `EvalFun`.
toEvalFun :: EvalBig e t v -> EvalFun e t v
toEvalFun (EVar lk ev) = case lookupEnvEvidence lk of
  Refl -> EFVar (toEvalFun ev)
toEvalFun ELam         = EFLam
toEvalFun (EApp e1 e2) = EFApp (toEvalFun e1) (toEvalFun e2)

-- | Determinism of same-module functional `EvalFun`: no lookup lemma needed!
evalFunDeterm :: EvalFun e m c1 -> EvalFun e m c2 -> c1 :~: c2
evalFunDeterm (EFVar e1)    (EFVar e2)    = evalFunDeterm e1 e2
evalFunDeterm EFLam         EFLam         = Refl
evalFunDeterm (EFApp l1 b1) (EFApp l2 b2) = case evalFunDeterm l1 l2 of
  Refl -> evalFunDeterm b1 b2

-- | Same-module functional lookup for `((λx y. x) id) Ω ⇓ <id, []>` at `FS FZ`!
evalFunKIdOmega
  :: EvalFun ENil
       (UApp (UApp (ULam (ULam (UVar (FS FZ)))) IdTerm) OmegaTerm)
       (MkClos IdTerm ENil)
evalFunKIdOmega = EFApp (EFApp EFLam EFLam) (EFVar EFLam)
```

The companion client module `PLFH.Part2.BigStepFunctional`
(`clients/PLFH/Part2/BigStepFunctional.hs`) verifies the exact same functional
variable rule across the module boundary via `BigStep.hi`.

### Negative control: wrong functional lookup target is rejected

Attempting to claim that `((λx y. x) id) Ω` evaluates to a different closure
(such as `MkClos OmegaTerm ENil` instead of `MkClos IdTerm ENil`) via
`BigStepFunctional.Eval` is rejected by GHC with `GHC-83865`:

```{.haskell .fail name="NegBigStepBadLookup" expect="GHC-83865"}
{-# LANGUAGE DependentTypes #-}
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

## Big-step to small-step bridge (`cbn→reduce`)

Every converging call-by-name big-step derivation `EvalBig ENil u (MkClos (ULam b) d)`
corresponds to a real multi-step full β-reduction `BetaSteps u (ULam b')`!

To prove `cbnToReduce` unconditionally without axioms or function extensionality,
we close open terms under a closure environment `Env n` (possibly underneath `m`
local lambda binders, represented by `SubEnv n m`) using the inductive closing
relation `CloseSub s t u`:

1. **`closeId`**: for an empty environment (`AllLift s`), every witnessed term
   closes to itself (`CloseSub s u u`).
2. **`closeBetaSubst`**: substituting a closed argument `m0` (satisfying
   `CloseSub (FromEnv e) m m0`) into a closed lambda body `b0` (satisfying
   `CloseSub (LiftEnv (FromEnv d)) b b0`) produces a term `r` witnessing **both**
   the single β-substitution `SubstAtU FZ m0 b0 r` **and** the extended environment
   closing `CloseSub (FromEnv (ECons (MkClos m e) d)) b r` (reusing
   `substShiftCancel` and `shiftSubstLe` from [Confluence](/Confluence/)).
3. **`cbnSim`**: by structural induction on `EvalBig e t (MkClos (ULam b) d)`,
   any closing `CloseSub (FromEnv e) t u` reduces under `BetaSteps` to a lambda
   `ULam b'` matching the result closure `(ULam b, d)`.
4. **`cbnToReduceW` / `cbnToReduce`**: specializing `cbnSim` to `e = ENil` via
   `closeId ALNil` delivers `BetaSteps u (ULam b')` directly!

```haskell
-- | Substitution context: an outer closing `Env n` underneath `m` lambda binders.
data SubEnv (n :: Nat) (m :: Nat) where
  FromEnv :: Env n -> SubEnv n Zero
  LiftEnv :: SubEnv n m -> SubEnv (Succ n) (Succ m)

-- | Inductive closing substitution: closes outer variables via `Env` while
-- preserving inner lambda-bound variables and shifting closed values cleanly.
type CloseSub :: forall (n m :: Nat). SubEnv n m -> UTerm n -> UTerm m -> Type
data CloseSub s t u where
  CSVarEnv :: EnvLookup e x (MkClos a d)
           -> CloseSub (FromEnv d) a u
           -> CloseSub (FromEnv e) (UVar x) u
  CSVarZ   :: CloseSub (LiftEnv s) (UVar FZ) (UVar FZ)
  CSVarS   :: CloseSub s (UVar x) u
           -> ShiftU FZ u u'
           -> CloseSub (LiftEnv s) (UVar (FS x)) u'
  CSLam    :: CloseSub (LiftEnv s) b b'
           -> CloseSub s (ULam b) (ULam b')
  CSApp    :: CloseSub s l l'
           -> CloseSub s m m'
           -> CloseSub s (UApp l m) (UApp l' m')

-- | Identity closing context (`ENil` under `n` binders).
type AllLift :: forall (n :: Nat). SubEnv n n -> Type
data AllLift s where
  ALNil  :: AllLift (FromEnv ENil)
  ALLift :: AllLift s -> AllLift (LiftEnv s)

-- | Under `ENil` (plus any local binders), every witnessed term closes to itself.
closeId :: AllLift s -> TermW u -> CloseSub s u u
closeId ALNil       (WVar fx)       = case fx of {}
closeId (ALLift _)  (WVar WFZ)      = CSVarZ
closeId (ALLift al) (WVar (WFS fx)) = CSVarS (closeId al (WVar fx)) (ShiftVar BumpZ)
closeId al          (WLam wb)       = CSLam (closeId (ALLift al) wb)
closeId al          (WApp wl wm)    = CSApp (closeId al wl) (closeId al wm)

-- | `s1` extends `s2` with a newly bound closure `cl` at cutoff `c`.
type ExtendSub :: forall (n m :: Nat). Clos -> Fin (Succ m) -> SubEnv (Succ n) (Succ m) -> SubEnv (Succ n) m -> Type
data ExtendSub cl c s1 s2 where
  ExtendZ :: ExtendSub cl FZ (LiftEnv (FromEnv d)) (FromEnv (ECons cl d))
  ExtendS :: ExtendSub cl c s1 s2 -> ExtendSub cl (FS c) (LiftEnv s1) (LiftEnv s2)

-- | Closed argument term lifted under `mOut` local binders, paired with its witness.
type LiftedClose :: forall (mOut :: Nat). Clos -> UTerm mOut -> Type
data LiftedClose cl m0 where
  LCZero :: CloseSub (FromEnv e) m m0 -> TermW m0 -> LiftedClose (MkClos m e) m0
  LCSucc :: LiftedClose cl mPrev -> ShiftU FZ mPrev m0 -> TermW m0 -> LiftedClose cl m0

liftedTermW :: LiftedClose cl m0 -> TermW m0
liftedTermW (LCZero _ wm0)   = wm0
liftedTermW (LCSucc _ _ wm0) = wm0

type CloseSubstRes :: forall (n m :: Nat). SubEnv (Succ n) m -> Fin (Succ m) -> UTerm m -> UTerm (Succ n) -> UTerm (Succ m) -> Type
data CloseSubstRes s2 c m0 b b0 where
  MkCloseSubst :: SubstAtU c m0 b0 r -> CloseSub s2 b r -> CloseSubstRes s2 c m0 b b0

-- | Commuting β-substitution with environment closing (`closeBetaSubst`).
closeBetaSubst :: ExtendSub cl c s1 s2 -> LiftedClose cl m0 -> CloseSub s1 b b0
               -> CloseSubstRes s2 c m0 b b0
closeBetaSubst ExtendZ        (LCZero csM _)    CSVarZ                         =
  MkCloseSubst SUEq (CSVarEnv ELZ csM)
closeBetaSubst (ExtendS _)    _                 CSVarZ                         =
  MkCloseSubst (SUNeq RemLt) CSVarZ
closeBetaSubst ExtendZ        (LCZero _ wm0)    (CSVarS (CSVarEnv lk csA) shU) =
  MkCloseSubst (substShiftCancel wm0 shU) (CSVarEnv (ELS lk) csA)
closeBetaSubst (ExtendS ext0) (LCSucc lc0 shM _) (CSVarS csX shU)              =
  case closeBetaSubst ext0 lc0 csX of
    MkCloseSubst sub0 csR0 -> case shiftSubstLe LLZ shU shM sub0 of
      MkShiftSubst shR0 sub' -> MkCloseSubst sub' (CSVarS csR0 shR0)
closeBetaSubst ext            lc                (CSLam csB)                    =
  case shiftEx WFZ (liftedTermW lc) of
    MkShiftEx shM wm0' -> case closeBetaSubst (ExtendS ext) (LCSucc lc shM wm0') csB of
      MkCloseSubst subB csB' -> MkCloseSubst (SULam shM subB) (CSLam csB')
closeBetaSubst ext            lc                (CSApp csL csR)                =
  case (closeBetaSubst ext lc csL, closeBetaSubst ext lc csR) of
    (MkCloseSubst subL csL', MkCloseSubst subR csR') ->
      MkCloseSubst (SUApp subL subR) (CSApp csL' csR')

-- | Simulation result: a closed lambda `ULam b'` matching `(ULam b, d)` via `BetaSteps`.
type CbnRes :: forall (nd :: Nat). UTerm (Succ nd) -> Env nd -> UTerm Zero -> Type
data CbnRes b d u where
  MkCbnRes :: CloseSub (LiftEnv (FromEnv d)) b b'
           -> TermW b'
           -> BetaSteps u (ULam b')
           -> CbnRes b d u

-- | Big-step evaluation simulates into multi-step full β-reduction under closing.
cbnSim :: EvalBig e t (MkClos (ULam b) d) -> CloseSub (FromEnv e) t u -> TermW u -> CbnRes b d u
cbnSim ELam           (CSLam csB)        (WLam wb)    = MkCbnRes csB wb BRefl
cbnSim (EVar lk ev)   (CSVarEnv lk' csA) wu           = case envLookupDeterm lk lk' of
  Refl -> cbnSim ev csA wu
cbnSim (EApp evL evB) (CSApp csL csM)    (WApp wl wm) =
  case cbnSim evL csL wl of
    MkCbnRes csB0 wb0 stepsL -> case closeBetaSubst ExtendZ (LCZero csM wm) csB0 of
      MkCloseSubst sub csR -> case cbnSim evB csR (substTargetW sub wm wb0) of
        MkCbnRes csRes wbRes stepsB ->
          MkCbnRes csRes wbRes (bsTrans (bsApp1 stepsL) (BCons (Beta sub) stepsB))

-- | Small-step termination witness: `u` β-reduces to some lambda abstraction.
data CbnTerminates (u :: UTerm Zero) where
  MkCbnTerminates :: BetaSteps u (ULam b) -> CbnTerminates u

-- | Unconditional big-step → small-step bridge (`cbn→reduce`)!
cbnToReduceW :: TermW u -> EvalBig ENil u (MkClos (ULam b) d) -> CbnTerminates u
cbnToReduceW wu ev = case cbnSim ev (closeId ALNil wu) wu of
  MkCbnRes _ _ steps -> MkCbnTerminates steps

cbnToReduce :: forall (nd :: Nat) (b :: UTerm (Succ nd)) (d :: Env nd).
               foreach (u :: UTerm Zero) -> EvalBig ENil u (MkClos (ULam b) d) -> CbnTerminates u
cbnToReduce u ev = cbnToReduceW (mkTermW u) ev
```

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
  `EvalBig`, `evalBigIsLam`, `envLookupDeterm`, `evalDeterm`, `omegaDiverges`,
  same-module functional `EvalFun`/`lookupEnvEvidence`/`toEvalFun`/`evalFunDeterm`/`evalFunKIdOmega`,
  `evalIdApp`, `evalConstOmega`, `evalKIdOmega`, and the **unconditional
  big-step → small-step bridge (`cbnSim`, `cbnToReduceW`, `cbnToReduce`)** via
  inductive environment closing `CloseSub`, plus cross-module `B.lookupEnv` in
  `PLFH.Part2.BigStepFunctional` (verified by negative control
  `NegBigStepBadLookup`), with zero promoted-constructor ticks and zero
  `[WIP NOTICE]` boxes.
