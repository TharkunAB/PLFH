{-# LANGUAGE DependentTypes, ListTuplePuns #-}
-- | Call-by-name big-step evaluation using the ordinary Haskell function
-- `PLFH.Part2.BigStep.lookupEnv` directly inside the `Var` rule, together with
-- conversion from relational `EvalBig`, determinism (`evalDeterm`), and
-- concrete derivations at both `FZ` and `FS FZ` (zero promoted-constructor ticks).
module PLFH.Part2.BigStepFunctional
  ( Eval (..)
  , lookupEvidence
  , fromBigStep
  , evalDeterm
  , evalIdApp
  , evalKIdOmega
  , observeIdApp
  , observeKIdOmega
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import Data.Nat.Dependent (Nat)
import qualified PLFH.Part2.BigStep as B
import PLFH.Part2.Untyped (Fin (..), IdTerm, OmegaTerm, UTerm (..))

-- | Big-step evaluation with functional `B.lookupEnv` in the variable rule.
type Eval :: forall (n :: Nat). B.Env n -> UTerm n -> B.Clos -> Type
data Eval e t v where
  Var :: (B.lookupEnv e x ~ B.MkClos m d) => Eval d m v -> Eval e (UVar x) v
  Lam :: Eval e (ULam b) (B.MkClos (ULam b) e)
  App :: Eval e l (B.MkClos (ULam b) d)
      -> Eval (B.ECons (B.MkClos m e) d) b w
      -> Eval e (UApp l m) w

-- | Relational lookup agrees with the ordinary function `B.lookupEnv`.
lookupEvidence :: B.EnvLookup e x c -> B.lookupEnv e x :~: c
lookupEvidence B.ELZ        = Refl
lookupEvidence (B.ELS rest) = lookupEvidence rest

-- | Convert a relational derivation into a functional-lookup derivation.
fromBigStep :: B.EvalBig e t v -> Eval e t v
fromBigStep (B.EVar proof ev) = case lookupEvidence proof of
  Refl -> Var (fromBigStep ev)
fromBigStep B.ELam = Lam
fromBigStep (B.EApp fun arg) = App (fromBigStep fun) (fromBigStep arg)

-- | Determinism of functional-lookup call-by-name big-step evaluation.
evalDeterm :: Eval e t v1 -> Eval e t v2 -> v1 :~: v2
evalDeterm (Var ev1) (Var ev2) = evalDeterm ev1 ev2
evalDeterm Lam Lam = Refl
evalDeterm (App l1 b1) (App l2 b2) = case evalDeterm l1 l2 of
  Refl -> evalDeterm b1 b2

-- | Look up the argument at the front of the environment (`FZ`).
evalIdApp :: Eval B.ENil (UApp IdTerm IdTerm) (B.MkClos IdTerm B.ENil)
evalIdApp = App Lam (Var Lam)

-- | Look past the unevaluated Ω argument (`FS FZ`) to reach the identity closure.
evalKIdOmega
  :: Eval B.ENil
          (UApp (UApp (ULam (ULam (UVar (FS FZ)))) IdTerm) OmegaTerm)
          (B.MkClos IdTerm B.ENil)
evalKIdOmega = App (App Lam Lam) (Var Lam)

-- | Observe both direct and converted proofs of `(λx. x) (λy. y)`.
observeIdApp :: (Bool, Bool)
observeIdApp = (usesZero evalIdApp, usesZero (fromBigStep B.evalIdApp))
  where
    usesZero :: Eval e t v -> Bool
    usesZero (App Lam (Var Lam)) = True
    usesZero _                   = False

-- | Observe both direct and converted proofs of `((λx y. x) id) Ω`.
observeKIdOmega :: (Bool, Bool)
observeKIdOmega = (usesSuccessor evalKIdOmega, usesSuccessor (fromBigStep B.evalKIdOmega))
  where
    usesSuccessor :: Eval e t v -> Bool
    usesSuccessor (App (App Lam Lam) (Var Lam)) = True
    usesSuccessor _                             = False
