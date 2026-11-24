{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, PolyKinds, RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures, TypeAbstractions, TypeApplications #-}
-- | Intrinsically-typed de Bruijn STLC reduction (`Step`) with real functional
-- `PLFH.Part2.DeBruijn.substSingle`, capture-avoiding beta witnesses, and
-- checked application progress (`appProgress`).
module PLFH.Part2.DeBruijnProgress
  ( Step (..)
  , Progress (..)
  , appProgress
  , betaIdStep
  , betaCaptureAvoid
  , betaShiftUnderLam
  ) where

import Data.Kind (Type)
import qualified PLFH.Part2.DeBruijn as D

-- | Intrinsically type-preserving call-by-value reduction (`M —→ N`).
-- Preservation holds automatically by the kind of `Step`!
type Step :: forall (g :: D.Ctx) (a :: D.Ty). D.Term g a -> D.Term g a -> Type
data Step m n where
  XiApp1   :: Step l l' -> Step (D.App l m) (D.App l' m)
  XiApp2   :: D.Value l -> Step m m' -> Step (D.App l m) (D.App l m')
  XiSuc    :: Step m m' -> Step (D.Suc m) (D.Suc m')
  XiCase   :: Step l l' -> Step (D.Case l m n) (D.Case l' m n)
  BetaLam  :: forall g a b (n :: D.Term (D.CExt g a) b) (w :: D.Term g a).
              D.Value w -> Step (D.App (D.Lam n) w) (D.substSingle n w)
  BetaZero :: forall g a (m :: D.Term g a) (n :: D.Term (D.CExt g D.TNat) a).
              Step (D.Case D.Zero m n) m
  BetaSuc  :: forall g a (m :: D.Term g a) (n :: D.Term (D.CExt g D.TNat) a)
                         (v :: D.Term g D.TNat).
              D.Value v -> Step (D.Case (D.Suc v) m n) (D.substSingle n v)
  BetaMu   :: forall g a (n :: D.Term (D.CExt g a) a).
              Step (D.Mu n) (D.substSingle n (D.Mu n))

-- | Intrinsically-typed progress witness for closed terms.
type Progress :: forall (a :: D.Ty). D.Term D.CEmpty a -> Type
data Progress m where
  PStep :: Step m n -> Progress m
  PDone :: D.Value m -> Progress m

-- | Application case of intrinsic progress given progress for strict subterms.
appProgress
  :: forall (a :: D.Ty).
     (forall (b :: D.Ty). foreach (m :: D.Term D.CEmpty b) -> Progress m)
  -> foreach (t :: D.Term D.CEmpty a) -> Maybe (Progress t)
appProgress progress t = case t of
  D.App l m -> case progress l of
    PStep s -> Just (appLeft s)
    PDone v -> case progress m of
      PStep s -> Just (appRight v s)
      PDone w -> Just (appBeta v w)
  _ -> Nothing

appLeft :: forall a b (l :: D.Term D.CEmpty (D.TArr a b))
                      (l' :: D.Term D.CEmpty (D.TArr a b)) (m :: D.Term D.CEmpty a).
           Step l l' -> Progress (D.App l m)
appLeft s = PStep (XiApp1 s)

appRight :: forall a b (l :: D.Term D.CEmpty (D.TArr a b))
                       (m :: D.Term D.CEmpty a) (m' :: D.Term D.CEmpty a).
            D.Value l -> Step m m' -> Progress (D.App l m)
appRight v s = PStep (XiApp2 v s)

appBeta :: forall a b (l :: D.Term D.CEmpty (D.TArr a b)) (m :: D.Term D.CEmpty a).
           D.Value l -> D.Value m -> Progress (D.App l m)
appBeta (D.VLam @n) w = PStep (BetaLam @D.CEmpty @a @b @n @m w)

-- | Concrete β-reduction: (λ. 0) 0 —→ 0.
betaIdStep :: Step (D.App (D.Lam (D.Var D.Z)) D.Zero) D.Zero
betaIdStep = BetaLam D.VZero

-- | Concrete substitution under a binder: (λ. λ. 1) 0 —→ λ. 0.
betaCaptureAvoid :: Step (D.App (D.Lam (D.Lam (D.Var (D.S D.Z)))) D.Zero)
                         (D.Lam D.Zero)
betaCaptureAvoid = BetaLam D.VZero

-- | Capture-avoiding substitution of an open value under a binder:
-- in context (∅, Nat), substituting `w = λ. Var (S Z)` (which references the
-- free outer Nat) into `λ. Var (S Z)` shifts `w`'s free variable to `S (S Z)`!
betaShiftUnderLam
  :: Step @(D.CExt D.CEmpty D.TNat)
          @(D.TArr D.TNat (D.TArr D.TNat D.TNat))
          (D.App (D.Lam (D.Lam (D.Var (D.S D.Z)))) (D.Lam (D.Var (D.S D.Z))))
          (D.Lam (D.Lam (D.Var (D.S (D.S D.Z)))))
betaShiftUnderLam = BetaLam D.VLam
