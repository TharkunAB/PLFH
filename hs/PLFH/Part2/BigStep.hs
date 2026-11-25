-- Generated from content/part2/BigStep.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE AllowAmbiguousTypes, DependentTypes #-}
{-# LINE 37 "content/part2/BigStep.md" #-}
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
import HaskLib.Nat (Nat (..))
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

{-# LINE 116 "content/part2/BigStep.md" #-}
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

{-# LINE 153 "content/part2/BigStep.md" #-}
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

{-# LINE 180 "content/part2/BigStep.md" #-}
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

{-# LINE 225 "content/part2/BigStep.md" #-}
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

{-# LINE 250 "content/part2/BigStep.md" #-}
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

{-# LINE 283 "content/part2/BigStep.md" #-}
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

{-# LINE 370 "content/part2/BigStep.md" #-}
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

-- | Unconditional big-step → small-step bridge (`cbn→reduce`)!
cbnToReduceW :: TermW u -> EvalBig ENil u (MkClos (ULam b) d) -> CbnTerminates u
cbnToReduceW wu ev = case termWToHas wu of
  MkHasTerm u' -> case subId @Zero u' of
    Refl -> case cbnSim ev CloseNil (idsW @Zero) wu of
      MkCbnRes _ _ _ steps -> MkCbnTerminates steps

cbnToReduce :: forall (nd :: Nat) (b :: UTerm (Succ nd)) (d :: Env nd).
               foreach (u :: UTerm Zero) -> EvalBig ENil u (MkClos (ULam b) d) -> CbnTerminates u
cbnToReduce u ev = cbnToReduceW (mkTermW u) ev
