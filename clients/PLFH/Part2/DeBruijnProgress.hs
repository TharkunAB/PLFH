{-# LANGUAGE DependentTypes #-}
-- | Complete intrinsically-typed de Bruijn STLC reduction (`Step`, `Steps`) with
-- real functional `PLFH.Part2.DeBruijn.substSingle`, capture-avoiding beta
-- witnesses, and unconditional full `progress` across all 7 term constructors!
module PLFH.Part2.DeBruijnProgress
  ( Step (..)
  , Steps (..)
  , Progress (..)
  , progress
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

-- | Reflexive-transitive closure of intrinsically-typed reduction (`M —↠ N`).
type Steps :: forall (g :: D.Ctx) (a :: D.Ty). D.Term g a -> D.Term g a -> Type
data Steps m n where
  StepsRefl :: Steps m m
  StepsCons :: Step l m -> Steps m n -> Steps l n

-- | Intrinsically-typed progress witness for closed terms.
type Progress :: forall (a :: D.Ty). D.Term D.CEmpty a -> Type
data Progress m where
  PStep :: Step m n -> Progress m
  PDone :: D.Value m -> Progress m

-- | Complete, unconditional Progress theorem for intrinsically-typed STLC:
-- every closed well-typed term is either a value or takes a type-preserving step!
progress :: forall (a :: D.Ty). foreach (m :: D.Term D.CEmpty a) -> Progress m
progress t = case t of
  D.Var x -> case x of {}
  D.Lam _ -> PDone D.VLam
  D.App l m -> case progress l of
    PStep s -> appLeft s
    PDone v -> case progress m of
      PStep s -> appRight v s
      PDone w -> appBeta v w
  D.Zero -> PDone D.VZero
  D.Suc n -> case progress n of
    PStep s -> sucStep s
    PDone v -> PDone (D.VSuc v)
  D.Case l m n -> case progress l of
    PStep s -> caseStep @a @l @_ @m @n s
    PDone v -> caseBeta @a @l @m @n v
  D.Mu n -> muStep @a @n

-- | Application case factored out as a standalone helper given subterm progress.
appProgress
  :: forall (a :: D.Ty).
     (forall (b :: D.Ty). foreach (m :: D.Term D.CEmpty b) -> Progress m)
  -> foreach (t :: D.Term D.CEmpty a) -> Maybe (Progress t)
appProgress recProg t = case t of
  D.App l m -> case recProg l of
    PStep s -> Just (appLeft s)
    PDone v -> case recProg m of
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

sucStep :: forall (n :: D.Term D.CEmpty D.TNat) (n' :: D.Term D.CEmpty D.TNat).
           Step n n' -> Progress (D.Suc n)
sucStep s = PStep (XiSuc s)

caseStep :: forall a (l :: D.Term D.CEmpty D.TNat) (l' :: D.Term D.CEmpty D.TNat)
                     (m :: D.Term D.CEmpty a) (n :: D.Term (D.CExt D.CEmpty D.TNat) a).
            Step l l' -> Progress (D.Case l m n)
caseStep s = PStep (XiCase s)

caseBeta :: forall a (l :: D.Term D.CEmpty D.TNat) (m :: D.Term D.CEmpty a)
                     (n :: D.Term (D.CExt D.CEmpty D.TNat) a).
            D.Value l -> Progress (D.Case l m n)
caseBeta D.VZero       = PStep (BetaZero @D.CEmpty @a @m @n)
caseBeta (D.VSuc @v w) = PStep (BetaSuc @D.CEmpty @a @m @n @v w)

muStep :: forall a (n :: D.Term (D.CExt D.CEmpty a) a). Progress (D.Mu n)
muStep = PStep (BetaMu @D.CEmpty @a @n)

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
