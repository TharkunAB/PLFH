-- Generated from content/part2/Untyped.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DependentTypes #-}
{-# LINE 35 "content/part2/Untyped.md" #-}
module PLFH.Part2.Untyped
  ( Fin (..)
  , UTerm (..)
  , extU
  , renameU
  , extsU
  , substU
  , substSingleU
  , BumpFin (..)
  , ShiftU (..)
  , RemoveFin (..)
  , SubstAtU (..)
  , Neutral (..)
  , Normal (..)
  , BetaStep (..)
  , BetaSteps (..)
  , IdTerm
  , SelfApp
  , OmegaTerm
  , CZero
  , COne
  , CTwo
  , idTerm
  , idIsNormal
  , cZeroIsNormal
  , cOneIsNormal
  , cTwoIsNormal
  , omegaTerm
  , idAppStep
  , omegaStep
  , kOmegaStep
  , BumpRes (..)
  , bumpProof
  , ShiftRes (..)
  , shiftProof
  , CmpFin (..)
  , cmpFin
  , SubstRes (..)
  , substProof
  , StepRes (..)
  , stepNormal
  , EvalRes (..)
  , evalNormal
  , evalNormalTerm
  ) where

import Data.Kind (Type)
import HaskLib.Nat (Nat (..))

{-# LINE 97 "content/part2/Untyped.md" #-}
-- | Finite set {0, ..., n-1}: well-scoped de Bruijn variables in depth `n`.
data Fin (n :: Nat) where
  FZ :: Fin (Succ n)
  FS :: Fin n -> Fin (Succ n)

-- | Well-scoped untyped lambda terms with `n` free variables in scope.
data UTerm (n :: Nat) where
  UVar :: Fin n -> UTerm n
  ULam :: UTerm (Succ n) -> UTerm n
  UApp :: UTerm n -> UTerm n -> UTerm n

-- | Closed identity term: λx. x.
idTerm :: UTerm Zero
idTerm = ULam (UVar FZ)

-- | The classic diverging term Ω = (λx. x x) (λx. x x).
omegaTerm :: UTerm Zero
omegaTerm = UApp selfApp selfApp
  where
    selfApp :: UTerm Zero
    selfApp = ULam (UApp (UVar FZ) (UVar FZ))

{-# LINE 134 "content/part2/Untyped.md" #-}
-- | Lift a variable renaming under a lambda binder.
extU :: (Fin m -> Fin n) -> Fin (Succ m) -> Fin (Succ n)
extU _   FZ     = FZ
extU rho (FS x) = FS (rho x)

-- | Simultaneous renaming on well-scoped untyped terms.
renameU :: (Fin m -> Fin n) -> UTerm m -> UTerm n
renameU rho (UVar x)   = UVar (rho x)
renameU rho (ULam b)   = ULam (renameU (extU rho) b)
renameU rho (UApp l m) = UApp (renameU rho l) (renameU rho m)

-- | Lift a substitution under a lambda binder.
extsU :: (Fin m -> UTerm n) -> Fin (Succ m) -> UTerm (Succ n)
extsU _     FZ     = UVar FZ
extsU sigma (FS x) = renameU FS (sigma x)

-- | Simultaneous capture-avoiding substitution on well-scoped untyped terms.
substU :: (Fin m -> UTerm n) -> UTerm m -> UTerm n
substU sigma (UVar x)   = sigma x
substU sigma (ULam b)   = ULam (substU (extsU sigma) b)
substU sigma (UApp l m) = UApp (substU sigma l) (substU sigma m)

-- | Single-variable substitution `b [ w ]`.
substSingleU :: UTerm (Succ n) -> UTerm n -> UTerm n
substSingleU b w = substU (\case { FZ -> w; FS x -> UVar x }) b

{-# LINE 185 "content/part2/Untyped.md" #-}
-- | Shift a variable `x :: Fin n` up by one slot at cutoff `c :: Fin (Succ n)`.
type BumpFin :: forall (n :: Nat). Fin (Succ n) -> Fin n -> Fin (Succ n) -> Type
data BumpFin c x y where
  BumpZ  :: BumpFin FZ x (FS x)
  BumpSZ :: forall {n} (c :: Fin (Succ n)). BumpFin (FS c) FZ FZ
  BumpSS :: BumpFin c x y -> BumpFin (FS c) (FS x) (FS y)

-- | Capture-avoiding weakening: shift all free variables >= `c` up by one.
type ShiftU :: forall (n :: Nat). Fin (Succ n) -> UTerm n -> UTerm (Succ n) -> Type
data ShiftU c m m' where
  ShiftVar :: BumpFin c x y -> ShiftU c (UVar x) (UVar y)
  ShiftLam :: ShiftU (FS c) b b' -> ShiftU c (ULam b) (ULam b')
  ShiftApp :: ShiftU c l l' -> ShiftU c m m' -> ShiftU c (UApp l m) (UApp l' m')

-- | Remove slot `c` from any distinct variable `x /= c` in `Fin (Succ n)`.
type RemoveFin :: forall (n :: Nat). Fin (Succ n) -> Fin (Succ n) -> Fin n -> Type
data RemoveFin c x y where
  RemGt :: forall {n} (y :: Fin n). RemoveFin FZ (FS y) y
  RemLt :: forall {n} (c :: Fin (Succ n)). RemoveFin (FS c) FZ FZ
  RemSS :: RemoveFin c x y -> RemoveFin (FS c) (FS x) (FS y)

-- | Deterministic relational single-variable substitution `m [ c := w ] ↦ m'`.
type SubstAtU :: forall (n :: Nat). Fin (Succ n) -> UTerm n -> UTerm (Succ n) -> UTerm n -> Type
data SubstAtU c w m m' where
  SUEq  :: SubstAtU c w (UVar c) w
  SUNeq :: RemoveFin c x y -> SubstAtU c w (UVar x) (UVar y)
  SULam :: ShiftU FZ w w' -> SubstAtU (FS c) w' b b' -> SubstAtU c w (ULam b) (ULam b')
  SUApp :: SubstAtU c w l l' -> SubstAtU c w m m' -> SubstAtU c w (UApp l m) (UApp l' m')

{-# LINE 236 "content/part2/Untyped.md" #-}
-- | Neutral terms: a variable applied to zero or more normal arguments.
type Neutral :: forall (n :: Nat). UTerm n -> Type
data Neutral t where
  NVar :: Neutral (UVar x)
  NApp :: Neutral l -> Normal m -> Neutral (UApp l m)

-- | Normal forms under full β-reduction (no β-redexes anywhere).
type Normal :: forall (n :: Nat). UTerm n -> Type
data Normal t where
  NNeu :: Neutral t -> Normal t
  NLam :: Normal b  -> Normal (ULam b)

-- | Full β-reduction (including under lambdas and in neutral arguments).
type BetaStep :: forall (n :: Nat). UTerm n -> UTerm n -> Type
data BetaStep t t' where
  XiApp1 :: BetaStep l l' -> BetaStep (UApp l m) (UApp l' m)
  XiApp2 :: BetaStep m m' -> BetaStep (UApp l m) (UApp l m')
  XiLam  :: BetaStep b b' -> BetaStep (ULam b) (ULam b')
  Beta   :: forall (n :: Nat) (w :: UTerm n) (b :: UTerm (Succ n)) (r :: UTerm n).
            SubstAtU FZ w b r -> BetaStep (UApp (ULam b) w) r

-- | Multi-step full β-reduction.
type BetaSteps :: forall (n :: Nat). UTerm n -> UTerm n -> Type
data BetaSteps t t' where
  BRefl :: BetaSteps t t
  BCons :: BetaStep s t -> BetaSteps t u -> BetaSteps s u

{-# LINE 270 "content/part2/Untyped.md" #-}
-- | Promoted closed terms: λx. x, λx. x x, and Ω = (λx. x x) (λx. x x).
type IdTerm    = (ULam (UVar FZ) :: UTerm Zero)
type SelfApp   = (ULam (UApp (UVar FZ) (UVar FZ)) :: UTerm Zero)
type OmegaTerm = (UApp SelfApp SelfApp :: UTerm Zero)

-- | Evidence that λx. x is in full normal form!
idIsNormal :: Normal IdTerm
idIsNormal = NLam (NNeu NVar)

-- | Concrete sound β-step: (λx. x) (λx. x) —→ (λx. x).
idAppStep :: BetaStep (UApp IdTerm IdTerm) IdTerm
idAppStep = Beta SUEq

-- | Concrete sound β-step: Ω —→ Ω!
omegaStep :: BetaStep OmegaTerm OmegaTerm
omegaStep = Beta (SUApp SUEq SUEq)

-- | Church numerals 0, 1, 2 in the untyped λ-calculus (λ s. λ z. s^n z).
type CZero = (ULam (ULam (UVar FZ)) :: UTerm Zero)
type COne  = (ULam (ULam (UApp (UVar (FS FZ)) (UVar FZ))) :: UTerm Zero)
type CTwo  = (ULam (ULam (UApp (UVar (FS FZ)) (UApp (UVar (FS FZ)) (UVar FZ)))) :: UTerm Zero)

-- | Church numerals are in full normal form (`Church-numerals`).
cZeroIsNormal :: Normal CZero
cZeroIsNormal = NLam (NLam (NNeu NVar))

cOneIsNormal :: Normal COne
cOneIsNormal = NLam (NLam (NNeu (NApp NVar (NNeu NVar))))

cTwoIsNormal :: Normal CTwo
cTwoIsNormal = NLam (NLam (NNeu (NApp NVar (NNeu (NApp NVar (NNeu NVar))))))

-- | Normal-order termination on a diverging argument (`K-omega`):
-- `(λ x. λ y. y) Ω —→ λ y. y` in a single outermost β-step!
kOmegaStep :: BetaStep (UApp (ULam (ULam (UVar FZ))) OmegaTerm) IdTerm
kOmegaStep =
  Beta (SULam
    (ShiftApp
      (ShiftLam (ShiftApp (ShiftVar BumpSZ) (ShiftVar BumpSZ)))
      (ShiftLam (ShiftApp (ShiftVar BumpSZ) (ShiftVar BumpSZ))))
    (SUNeq RemLt))

{-# LINE 348 "content/part2/Untyped.md" #-}
-- | Constructive witness for `BumpFin c x y`.
type BumpRes :: forall (n :: Nat). Fin (Succ n) -> Fin n -> Type
data BumpRes c x where
  MkBump :: foreach (y :: Fin (Succ n)) -> BumpFin c x y -> BumpRes c x

-- | Compute the bumped variable `y` together with its `BumpFin` proof.
bumpProof :: forall (n :: Nat).
             foreach (c :: Fin (Succ n)) -> foreach (x :: Fin n) -> BumpRes c x
bumpProof c x = case c of
  FZ    -> MkBump (FS x) BumpZ
  FS c' -> case x of
    FZ    -> MkBump FZ (BumpSZ @c')
    FS x' -> case bumpProof c' x' of
      MkBump y b -> MkBump (FS y) (BumpSS b)

-- | Constructive witness for `ShiftU c m m'`.
type ShiftRes :: forall (n :: Nat). Fin (Succ n) -> UTerm n -> Type
data ShiftRes c m where
  MkShift :: foreach (m' :: UTerm (Succ n)) -> ShiftU c m m' -> ShiftRes c m

-- | Compute capture-avoiding weakening together with its `ShiftU` proof.
shiftProof :: forall (n :: Nat).
              foreach (c :: Fin (Succ n)) -> foreach (m :: UTerm n) -> ShiftRes c m
shiftProof c m = case m of
  UVar x -> case bumpProof c x of
    MkBump y b -> MkShift (UVar y) (ShiftVar b)
  ULam b -> case shiftProof (FS c) b of
    MkShift b' sb -> MkShift (ULam b') (ShiftLam sb)
  UApp l r -> case shiftProof c l of
    MkShift l' sl -> case shiftProof c r of
      MkShift r' sr -> MkShift (UApp l' r') (ShiftApp sl sr)

-- | Compare two indices in `Fin (Succ n)`: either equal or separated by `RemoveFin`.
type CmpFin :: forall (n :: Nat). Fin (Succ n) -> Fin (Succ n) -> Type
data CmpFin c x where
  CmpEq  :: CmpFin c c
  CmpNeq :: foreach (y :: Fin n) -> RemoveFin c x y -> CmpFin c x

-- | Helper for comparing `FZ` against any `x :: Fin (Succ m)`.
cmpFinZ :: forall (m :: Nat).
           foreach (x :: Fin (Succ m)) -> CmpFin (FZ @m) x
cmpFinZ x = case x of
  FZ   -> CmpEq
  FS y -> CmpNeq y (RemGt @y)

-- | Helper for the `FS FZ` branch where the outer scope index is manifestly `Succ m`.
cmpFinFZ :: forall (m :: Nat).
            foreach (x :: Fin (Succ (Succ m))) -> CmpFin (FS (FZ @m)) x
cmpFinFZ x = case x of
  FZ    -> CmpNeq FZ (RemLt @FZ)
  FS x' -> case x' of
    FZ   -> CmpEq
    FS y -> CmpNeq (FS y) (RemSS (RemGt @y))

-- | Helper for the `FS (FS c'')` branch where the outer scope index is manifestly `Succ m`.
cmpFinFSS :: forall (m :: Nat).
             foreach (c'' :: Fin m) -> foreach (x :: Fin (Succ (Succ m)))
          -> CmpFin (FS (FS c'')) x
cmpFinFSS c'' x = case x of
  FZ    -> CmpNeq FZ (RemLt @(FS c''))
  FS x' -> case c'' of
    FZ -> case cmpFinFZ x' of
      CmpEq      -> CmpEq
      CmpNeq y r -> CmpNeq (FS y) (RemSS r)
    FS c''' -> case cmpFinFSS c''' x' of
      CmpEq      -> CmpEq
      CmpNeq y r -> CmpNeq (FS y) (RemSS r)

-- | Decidable comparison with `RemoveFin` evidence.
cmpFin :: forall (n :: Nat).
          foreach (c :: Fin (Succ n)) -> foreach (x :: Fin (Succ n)) -> CmpFin c x
cmpFin c x = case c of
  FZ    -> cmpFinZ x
  FS c' -> case c' of
    FZ     -> cmpFinFZ x
    FS c'' -> cmpFinFSS c'' x

-- | Constructive witness for `SubstAtU c w m r`.
type SubstRes :: forall (n :: Nat). Fin (Succ n) -> UTerm n -> UTerm (Succ n) -> Type
data SubstRes c w m where
  MkSubst :: foreach (r :: UTerm n) -> SubstAtU c w m r -> SubstRes c w m

-- | Compute single-variable substitution `m [ c := w ]` with its `SubstAtU` proof.
substProof :: forall (n :: Nat).
              foreach (c :: Fin (Succ n))
           -> foreach (w :: UTerm n)
           -> foreach (m :: UTerm (Succ n))
           -> SubstRes c w m
substProof c w m = case m of
  UVar x -> case cmpFin c x of
    CmpEq      -> MkSubst w SUEq
    CmpNeq y r -> MkSubst (UVar y) (SUNeq r)
  ULam b -> case shiftProof FZ w of
    MkShift w' sw -> case substProof (FS c) w' b of
      MkSubst b' sb -> MkSubst (ULam b') (SULam sw sb)
  UApp l r -> case substProof c w l of
    MkSubst l' sl -> case substProof c w r of
      MkSubst r' sr -> MkSubst (UApp l' r') (SUApp sl sr)

-- | Outcome of one leftmost-outermost (normal-order) reduction step.
type StepRes :: forall (n :: Nat). UTerm n -> Type
data StepRes t where
  Reduct :: foreach (t' :: UTerm n) -> BetaStep t t' -> StepRes t
  IsNorm :: Normal t -> StepRes t

-- | Normal-order step for an application `UApp l m`.
stepApp :: forall (n :: Nat).
           foreach (l m :: UTerm n) -> StepRes (UApp l m)
stepApp l m = case l of
  ULam b -> case substProof FZ m b of
    MkSubst r sr -> Reduct r (Beta sr)
  UVar x -> case stepNormal m of
    Reduct m' sm -> Reduct (UApp (UVar x) m') (XiApp2 sm)
    IsNorm nm    -> IsNorm (NNeu (NApp NVar nm))
  UApp l1 l2 -> case stepApp l1 l2 of
    Reduct l' sl -> Reduct (UApp l' m) (XiApp1 sl)
    IsNorm nl    -> case nl of
      NNeu neuL -> case stepNormal m of
        Reduct m' sm -> Reduct (UApp (UApp l1 l2) m') (XiApp2 sm)
        IsNorm nm    -> IsNorm (NNeu (NApp neuL nm))

-- | Constructive normal-order single-step reducer (`stepNormal`).
stepNormal :: forall (n :: Nat). foreach (t :: UTerm n) -> StepRes t
stepNormal t = case t of
  UVar _   -> IsNorm (NNeu NVar)
  ULam b   -> case stepNormal b of
    Reduct b' sb -> Reduct (ULam b') (XiLam sb)
    IsNorm nb    -> IsNorm (NLam nb)
  UApp l m -> stepApp l m

-- | Outcome of gas-bounded normal-order evaluation (`Finished` in PLFA).
type EvalRes :: forall (n :: Nat). UTerm n -> Type
data EvalRes t where
  EvalDone     :: foreach (nf :: UTerm n) -> BetaSteps t nf -> Normal nf -> EvalRes t
  EvalOutOfGas :: foreach (t' :: UTerm n) -> BetaSteps t t' -> EvalRes t

-- | Gas-bounded normal-order evaluator returning a certified `BetaSteps` trace
-- and `Normal` proof!
evalNormal :: forall (n :: Nat). Nat -> foreach (t :: UTerm n) -> EvalRes t
evalNormal gas t = case gas of
  Zero   -> EvalOutOfGas t BRefl
  Succ g -> case stepNormal t of
    IsNorm nt    -> EvalDone t BRefl nt
    Reduct t' st -> case evalNormal g t' of
      EvalDone nf bs nnf -> EvalDone nf (BCons st bs) nnf
      EvalOutOfGas u bs  -> EvalOutOfGas u (BCons st bs)

-- | Plain wrapper for running `evalNormal` on arbitrary runtime `UTerm n` values.
evalNormalTerm :: forall (n :: Nat). Nat -> UTerm n -> Maybe (UTerm n)
evalNormalTerm gas t = case evalNormal gas t of
  EvalDone nf _ _  -> Just nf
  EvalOutOfGas _ _ -> Nothing
