-- Generated from content/part2/BigStep.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, StandaloneKindSignatures, TypeOperators #-}
{-# OPTIONS_GHC -fwrite-source-equations #-}
{-# LINE 39 "content/part2/BigStep.md" #-}
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
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void)
import HaskLib.Nat (Nat (..))
import PLFH.Part1.Negation (Not)
import PLFH.Part2.Untyped (Fin (..), IdTerm, OmegaTerm, SelfApp, UTerm (..))

{-# LINE 85 "content/part2/BigStep.md" #-}
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

{-# LINE 122 "content/part2/BigStep.md" #-}
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

{-# LINE 149 "content/part2/BigStep.md" #-}
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

{-# LINE 194 "content/part2/BigStep.md" #-}
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

{-# LINE 219 "content/part2/BigStep.md" #-}
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

{-# LINE 252 "content/part2/BigStep.md" #-}
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
