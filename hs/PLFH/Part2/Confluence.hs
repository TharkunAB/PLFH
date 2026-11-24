-- Generated from content/part2/Confluence.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DependentTypes #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
{-# LINE 67 "content/part2/Confluence.md" #-}
module PLFH.Part2.Confluence
  ( bsTrans
  , bsApp1
  , bsApp2
  , bsLam
  , Par (..)
  , FinW (..)
  , TermW (..)
  , mkFinW
  , mkTermW
  , parRefl
  , betaToPar
  , ParSteps (..)
  , psTrans
  , parToBetas
  , parsToBetas
  , omegaPar
  , Joinable (..)
  , joinSym
  , bumpDeterm
  , remDeterm
  , shiftDeterm
  , substDeterm
  , parShift
  , parSubst
  , parDiamondW
  , parDiamond
  , stripW
  , strip
  , parConfluenceW
  , parConfluence
  , betasToParsW
  , betasToPars
  , churchRosser
  , neutralNoBetaStep
  , normalNoBetaStep
  , normalNoBetaSteps
  , neutralPar
  , normalPar
  , normalParSteps
  , uniqueNormalForm
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void, absurd)
import HaskLib.Nat (Nat (..))
import PLFH.Part1.Decidable (Not)
import PLFH.Part2.Untyped
  ( BetaStep (..)
  , BetaSteps (..)
  , BumpFin (..)
  , Fin (..)
  , Neutral (..)
  , Normal (..)
  , OmegaTerm
  , RemoveFin (..)
  , ShiftU (..)
  , SubstAtU (..)
  , UTerm (..)
  )

{-# LINE 136 "content/part2/Confluence.md" #-}
-- | Transitivity of multi-step β-reduction.
bsTrans :: BetaSteps s t -> BetaSteps t u -> BetaSteps s u
bsTrans BRefl       q = q
bsTrans (BCons s p) q = BCons s (bsTrans p q)

-- | Congruence of multi-step β-reduction in function, argument, and lambda body.
bsApp1 :: BetaSteps l l' -> BetaSteps (UApp l m) (UApp l' m)
bsApp1 BRefl       = BRefl
bsApp1 (BCons s p) = BCons (XiApp1 s) (bsApp1 p)

bsApp2 :: BetaSteps m m' -> BetaSteps (UApp l m) (UApp l m')
bsApp2 BRefl       = BRefl
bsApp2 (BCons s p) = BCons (XiApp2 s) (bsApp2 p)

bsLam :: BetaSteps b b' -> BetaSteps (ULam b) (ULam b')
bsLam BRefl       = BRefl
bsLam (BCons s p) = BCons (XiLam s) (bsLam p)

{-# LINE 170 "content/part2/Confluence.md" #-}
-- | Parallel β-reduction: contract any subset of redexes simultaneously.
type Par :: forall (n :: Nat). UTerm n -> UTerm n -> Type
data Par t t' where
  PVar  :: Par (UVar x) (UVar x)
  PLam  :: Par b b' -> Par (ULam b) (ULam b')
  PApp  :: Par l l' -> Par m m' -> Par (UApp l m) (UApp l' m')
  PBeta :: forall (n :: Nat) (b :: UTerm (Succ n)) (b' :: UTerm (Succ n))
                  (w :: UTerm n) (w' :: UTerm n) (r :: UTerm n).
           Par b b' -> Par w w' -> SubstAtU FZ w' b' r
        -> Par (UApp (ULam b) w) r

-- | Reflexive-transitive closure of parallel reduction (`_⇛*_`).
type ParSteps :: forall (n :: Nat). UTerm n -> UTerm n -> Type
data ParSteps t t' where
  PSRefl :: ParSteps t t
  PSCons :: Par s t -> ParSteps t u -> ParSteps s u

psTrans :: ParSteps x y -> ParSteps y z -> ParSteps x z
psTrans PSRefl        ys = ys
psTrans (PSCons x xs) ys = PSCons x (psTrans xs ys)

-- | Every parallel reduction step is simulated by zero or more β-steps!
parToBetas :: Par m n -> BetaSteps m n
parToBetas PVar              = BRefl
parToBetas (PLam p)          = bsLam (parToBetas p)
parToBetas (PApp pl pm)      = bsTrans (bsApp1 (parToBetas pl)) (bsApp2 (parToBetas pm))
parToBetas (PBeta pb pw sub) =
  bsTrans (bsApp1 (bsLam (parToBetas pb)))
    (bsTrans (bsApp2 (parToBetas pw)) (BCons (Beta sub) BRefl))

-- | Multi-step parallel reduction embeds into multi-step β-reduction.
parsToBetas :: ParSteps m n -> BetaSteps m n
parsToBetas PSRefl       = BRefl
parsToBetas (PSCons p q) = bsTrans (parToBetas p) (parsToBetas q)

-- | Concrete parallel reduction step: Ω ⇛ Ω.
omegaPar :: Par OmegaTerm OmegaTerm
omegaPar = PBeta (PApp PVar PVar) (PLam (PApp PVar PVar)) (SUApp SUEq SUEq)

{-# LINE 220 "content/part2/Confluence.md" #-}
-- | Inductive singleton witness for a de Bruijn index `x :: Fin n`.
type FinW :: forall (n :: Nat). Fin n -> Type
data FinW x where
  WFZ :: FinW FZ
  WFS :: FinW x -> FinW (FS x)

-- | Inductive singleton witness for a well-scoped term `t :: UTerm n`.
type TermW :: forall (n :: Nat). UTerm n -> Type
data TermW t where
  WVar :: FinW x -> TermW (UVar x)
  WLam :: TermW b -> TermW (ULam b)
  WApp :: TermW l -> TermW m -> TermW (UApp l m)

mkFinW :: forall (n :: Nat). foreach (x :: Fin n) -> FinW x
mkFinW FZ     = WFZ
mkFinW (FS x) = WFS (mkFinW x)

mkTermW :: forall (n :: Nat). foreach (t :: UTerm n) -> TermW t
mkTermW (UVar x)   = WVar (mkFinW x)
mkTermW (ULam b)   = WLam (mkTermW b)
mkTermW (UApp l m) = WApp (mkTermW l) (mkTermW m)

-- | Constructive existence of index bumping and term weakening for witnessed terms.
type BumpEx :: forall (n :: Nat). Fin (Succ n) -> Fin n -> Type
data BumpEx c x where
  MkBumpEx :: BumpFin c x y -> FinW y -> BumpEx c x

bumpEx :: FinW c -> FinW x -> BumpEx c x
bumpEx WFZ      fx       = MkBumpEx BumpZ (WFS fx)
bumpEx (WFS _)  WFZ      = MkBumpEx BumpSZ WFZ
bumpEx (WFS fc) (WFS fx) = case bumpEx fc fx of
  MkBumpEx b fy -> MkBumpEx (BumpSS b) (WFS fy)

type ShiftEx :: forall (n :: Nat). Fin (Succ n) -> UTerm n -> Type
data ShiftEx c t where
  MkShiftEx :: ShiftU c t t' -> TermW t' -> ShiftEx c t

shiftEx :: FinW c -> TermW t -> ShiftEx c t
shiftEx fc (WVar fx)   = case bumpEx fc fx of
  MkBumpEx b fy -> MkShiftEx (ShiftVar b) (WVar fy)
shiftEx fc (WLam wb)   = case shiftEx (WFS fc) wb of
  MkShiftEx sh wb' -> MkShiftEx (ShiftLam sh) (WLam wb')
shiftEx fc (WApp wl wm) = case (shiftEx fc wl, shiftEx fc wm) of
  (MkShiftEx shL wl', MkShiftEx shM wm') -> MkShiftEx (ShiftApp shL shM) (WApp wl' wm')

-- | Witness preservation across bumping, removal, weakening, substitution, and reduction.
bumpFinW :: BumpFin c x y -> FinW x -> FinW y
bumpFinW BumpZ      fx       = WFS fx
bumpFinW BumpSZ     WFZ      = WFZ
bumpFinW (BumpSS b) (WFS fx) = WFS (bumpFinW b fx)

remFinW :: RemoveFin c x y -> FinW x -> FinW y
remFinW RemGt     (WFS fy) = fy
remFinW RemLt     WFZ      = WFZ
remFinW (RemSS r) (WFS fx) = WFS (remFinW r fx)

shiftTargetW :: ShiftU c t t' -> TermW t -> TermW t'
shiftTargetW (ShiftVar b)     (WVar fx)    = WVar (bumpFinW b fx)
shiftTargetW (ShiftLam sh)    (WLam wb)    = WLam (shiftTargetW sh wb)
shiftTargetW (ShiftApp s1 s2) (WApp wl wm) = WApp (shiftTargetW s1 wl) (shiftTargetW s2 wm)

substTargetW :: SubstAtU c w b r -> TermW w -> TermW b -> TermW r
substTargetW SUEq           ww _            = ww
substTargetW (SUNeq r)      _  (WVar fx)    = WVar (remFinW r fx)
substTargetW (SULam sh sub) ww (WLam wb)    = WLam (substTargetW sub (shiftTargetW sh ww) wb)
substTargetW (SUApp s1 s2)  ww (WApp wl wm) = WApp (substTargetW s1 ww wl) (substTargetW s2 ww wm)

parTargetW :: Par t t' -> TermW t -> TermW t'
parTargetW PVar              (WVar fx)          = WVar fx
parTargetW (PLam pb)         (WLam wb)          = WLam (parTargetW pb wb)
parTargetW (PApp pl pm)      (WApp wl wm)       = WApp (parTargetW pl wl) (parTargetW pm wm)
parTargetW (PBeta pb pw sub) (WApp (WLam wb) ww) =
  substTargetW sub (parTargetW pw ww) (parTargetW pb wb)

betaTargetW :: BetaStep t t' -> TermW t -> TermW t'
betaTargetW (XiApp1 sl) (WApp wl wm)       = WApp (betaTargetW sl wl) wm
betaTargetW (XiApp2 sm) (WApp wl wm)       = WApp wl (betaTargetW sm wm)
betaTargetW (XiLam sb)  (WLam wb)          = WLam (betaTargetW sb wb)
betaTargetW (Beta sub)  (WApp (WLam wb) ww) = substTargetW sub ww wb

-- | Parallel reduction is reflexive across the non-uniform scope index `n`.
parReflW :: TermW m -> Par m m
parReflW (WVar _)     = PVar
parReflW (WLam wb)    = PLam (parReflW wb)
parReflW (WApp wl wm) = PApp (parReflW wl) (parReflW wm)

parRefl :: forall (n :: Nat). foreach (m :: UTerm n) -> Par m m
parRefl m = parReflW (mkTermW m)

-- | Every single β-step is a parallel reduction step (`—→-to-⇒`).
betaToParW :: TermW l -> BetaStep l r -> Par l r
betaToParW (WVar _)           s          = case s of {}
betaToParW (WApp wl wm)       (XiApp1 sl) = PApp (betaToParW wl sl) (parReflW wm)
betaToParW (WApp wl wm)       (XiApp2 sm) = PApp (parReflW wl) (betaToParW wm sm)
betaToParW (WLam wb)          (XiLam sb)  = PLam (betaToParW wb sb)
betaToParW (WApp (WLam wb) ww) (Beta sub) = PBeta (parReflW wb) (parReflW ww) sub

betaToPar :: forall (n :: Nat) (r :: UTerm n).
             foreach (l :: UTerm n) -> BetaStep l r -> Par l r
betaToPar l s = betaToParW (mkTermW l) s

-- | Lift single-step `BetaStep -> Par` to multi-step reduction (`—↠-to-⇒*`).
betasToParsW :: TermW m1 -> BetaSteps m1 m2 -> ParSteps m1 m2
betasToParsW _  BRefl        = PSRefl
betasToParsW wm (BCons s bs) = PSCons (betaToParW wm s) (betasToParsW (betaTargetW s wm) bs)

betasToPars :: forall (n :: Nat) (m2 :: UTerm n).
               foreach (m1 :: UTerm n) -> BetaSteps m1 m2 -> ParSteps m1 m2
betasToPars m1 bs = betasToParsW (mkTermW m1) bs

{-# LINE 351 "content/part2/Confluence.md" #-}
-- | Determinism of `BumpFin`, `RemoveFin`, `ShiftU`, and `SubstAtU`.
bumpDeterm :: BumpFin c x y1 -> BumpFin c x y2 -> y1 :~: y2
bumpDeterm BumpZ       BumpZ       = Refl
bumpDeterm BumpSZ      BumpSZ      = Refl
bumpDeterm (BumpSS b1) (BumpSS b2) = case bumpDeterm b1 b2 of Refl -> Refl

remIrrefl :: RemoveFin c c y -> Void
remIrrefl (RemSS r) = remIrrefl r

remDeterm :: RemoveFin c x y1 -> RemoveFin c x y2 -> y1 :~: y2
remDeterm RemGt      RemGt      = Refl
remDeterm RemLt      RemLt      = Refl
remDeterm (RemSS r1) (RemSS r2) = case remDeterm r1 r2 of Refl -> Refl

shiftDeterm :: ShiftU c t t1 -> ShiftU c t t2 -> t1 :~: t2
shiftDeterm (ShiftVar b1)    (ShiftVar b2)    = case bumpDeterm b1 b2 of Refl -> Refl
shiftDeterm (ShiftLam s1)    (ShiftLam s2)    = case shiftDeterm s1 s2 of Refl -> Refl
shiftDeterm (ShiftApp l1 m1) (ShiftApp l2 m2) =
  case (shiftDeterm l1 l2, shiftDeterm m1 m2) of (Refl, Refl) -> Refl

substDeterm :: SubstAtU c w b r1 -> SubstAtU c w b r2 -> r1 :~: r2
substDeterm SUEq          SUEq          = Refl
substDeterm SUEq          (SUNeq r)     = absurd (remIrrefl r)
substDeterm (SUNeq r)     SUEq          = absurd (remIrrefl r)
substDeterm (SUNeq r1)    (SUNeq r2)    = case remDeterm r1 r2 of Refl -> Refl
substDeterm (SULam s1 b1) (SULam s2 b2) =
  case shiftDeterm s1 s2 of
    Refl -> case substDeterm b1 b2 of Refl -> Refl
substDeterm (SUApp l1 m1) (SUApp l2 m2) =
  case (substDeterm l1 l2, substDeterm m1 m2) of (Refl, Refl) -> Refl

-- | Cutoff invariant `k <= c`, carrying both `k :: Fin (Succ n)` and its
-- same-value copy `kHi :: Fin (Succ (Succ n))`.
type LeLift :: forall (n :: Nat). Fin (Succ n) -> Fin (Succ (Succ n)) -> Fin (Succ n) -> Type
data LeLift k kHi c where
  LLZ :: LeLift FZ FZ c
  LLS :: LeLift k kHi c -> LeLift (FS k) (FS kHi) (FS c)

-- | Shift-shift sequential commutation (`c <= d`).
type BumpSeqRes :: forall (n :: Nat). Fin (Succ (Succ n)) -> Fin (Succ n) -> Fin n -> Fin (Succ (Succ n)) -> Type
data BumpSeqRes d' c x z where
  MkBumpSeq :: BumpFin c x y' -> BumpFin d' y' z -> BumpSeqRes d' c x z

bumpShiftCommute :: LeLift c cHi d -> BumpFin d x y -> BumpFin cHi y z -> BumpSeqRes (FS d) c x z
bumpShiftCommute LLZ      bD          BumpZ       = MkBumpSeq BumpZ (BumpSS bD)
bumpShiftCommute (LLS _)  BumpSZ      BumpSZ      = MkBumpSeq BumpSZ BumpSZ
bumpShiftCommute (LLS ll) (BumpSS bD) (BumpSS bC) = case bumpShiftCommute ll bD bC of
  MkBumpSeq bC' bD' -> MkBumpSeq (BumpSS bC') (BumpSS bD')

type ShiftSeqRes :: forall (n :: Nat). Fin (Succ (Succ n)) -> Fin (Succ n) -> UTerm n -> UTerm (Succ (Succ n)) -> Type
data ShiftSeqRes d' c w w2 where
  MkShiftSeq :: ShiftU c w wTmp -> ShiftU d' wTmp w2 -> ShiftSeqRes d' c w w2

shiftShift :: LeLift c cHi d -> ShiftU d w w1 -> ShiftU cHi w1 w2 -> ShiftSeqRes (FS d) c w w2
shiftShift ll (ShiftVar bD)    (ShiftVar bC)    = case bumpShiftCommute ll bD bC of
  MkBumpSeq bC' bD' -> MkShiftSeq (ShiftVar bC') (ShiftVar bD')
shiftShift ll (ShiftLam sD)    (ShiftLam sC)    = case shiftShift (LLS ll) sD sC of
  MkShiftSeq sC' sD' -> MkShiftSeq (ShiftLam sC') (ShiftLam sD')
shiftShift ll (ShiftApp lD mD) (ShiftApp lC mC) = case (shiftShift ll lD lC, shiftShift ll mD mC) of
  (MkShiftSeq lC' lD', MkShiftSeq mC' mD') -> MkShiftSeq (ShiftApp lC' mC') (ShiftApp lD' mD')

-- | Shift-shift fork (pushout) commutation (`k <= c`).
type BumpForkRes :: forall (n :: Nat). Fin (Succ (Succ n)) -> Fin (Succ (Succ n)) -> Fin (Succ n) -> Fin (Succ n) -> Type
data BumpForkRes c' kHi y1 y2 where
  MkBumpFork :: BumpFin c' y1 y3 -> BumpFin kHi y2 y3 -> BumpForkRes c' kHi y1 y2

bumpFork :: LeLift k kHi c -> BumpFin k x y1 -> BumpFin c x y2 -> BumpForkRes (FS c) kHi y1 y2
bumpFork LLZ      BumpZ       bC          = MkBumpFork (BumpSS bC) BumpZ
bumpFork (LLS _)  BumpSZ      BumpSZ      = MkBumpFork BumpSZ BumpSZ
bumpFork (LLS ll) (BumpSS bK) (BumpSS bC) = case bumpFork ll bK bC of
  MkBumpFork bC' bK' -> MkBumpFork (BumpSS bC') (BumpSS bK')

type ShiftForkRes :: forall (n :: Nat). Fin (Succ (Succ n)) -> Fin (Succ (Succ n)) -> UTerm (Succ n) -> UTerm (Succ n) -> Type
data ShiftForkRes c' kHi w1 w2 where
  MkShiftFork :: ShiftU c' w1 w3 -> ShiftU kHi w2 w3 -> ShiftForkRes c' kHi w1 w2

shiftShiftFork :: LeLift k kHi c -> ShiftU k w w1 -> ShiftU c w w2 -> ShiftForkRes (FS c) kHi w1 w2
shiftShiftFork ll (ShiftVar bK)    (ShiftVar bC)    = case bumpFork ll bK bC of
  MkBumpFork bC' bK' -> MkShiftFork (ShiftVar bC') (ShiftVar bK')
shiftShiftFork ll (ShiftLam sK)    (ShiftLam sC)    = case shiftShiftFork (LLS ll) sK sC of
  MkShiftFork sC' sK' -> MkShiftFork (ShiftLam sC') (ShiftLam sK')
shiftShiftFork ll (ShiftApp lK mK) (ShiftApp lC mC) = case (shiftShiftFork ll lK lC, shiftShiftFork ll mK mC) of
  (MkShiftFork lC' lK', MkShiftFork mC' mK') -> MkShiftFork (ShiftApp lC' mC') (ShiftApp lK' mK')

-- | Shift-substitution commutation above (`d <= c`) and below (`k <= c`).
type BumpRemRes :: forall (n :: Nat). Fin (Succ n) -> Fin (Succ (Succ n)) -> Fin (Succ (Succ n)) -> Fin n -> Type
data BumpRemRes c dHi x1 y where
  MkBumpRem :: BumpFin c y y1 -> RemoveFin dHi x1 y1 -> BumpRemRes c dHi x1 y

bumpGeEq :: LeLift d dHi c -> BumpFin (FS c) d x1 -> x1 :~: dHi
bumpGeEq LLZ      BumpSZ      = Refl
bumpGeEq (LLS ll) (BumpSS b)  = case bumpGeEq ll b of Refl -> Refl

bumpRemGe :: LeLift d dHi c -> BumpFin (FS c) x x1 -> RemoveFin d x y -> BumpRemRes c dHi x1 y
bumpRemGe LLZ      BumpSZ       r          = case r of {}
bumpRemGe LLZ      (BumpSS bY)  RemGt      = MkBumpRem bY RemGt
bumpRemGe (LLS _)  BumpSZ       RemLt      = MkBumpRem BumpSZ RemLt
bumpRemGe (LLS ll) (BumpSS bX0) (RemSS r0) = case bumpRemGe ll bX0 r0 of
  MkBumpRem bY0 r0' -> MkBumpRem (BumpSS bY0) (RemSS r0')

type ShiftSubstRes :: forall (n :: Nat). Fin (Succ n) -> Fin (Succ (Succ n)) -> UTerm (Succ n) -> UTerm (Succ (Succ n)) -> UTerm n -> Type
data ShiftSubstRes c dHi v1 b1 r where
  MkShiftSubst :: ShiftU c r r1 -> SubstAtU dHi v1 b1 r1 -> ShiftSubstRes c dHi v1 b1 r

shiftSubstGe :: LeLift d dHi c -> ShiftU (FS c) b b1 -> ShiftU c v v1 -> SubstAtU d v b r -> ShiftSubstRes c dHi v1 b1 r
shiftSubstGe ll (ShiftVar bX) shV SUEq = case bumpGeEq ll bX of
  Refl -> MkShiftSubst shV SUEq
shiftSubstGe ll (ShiftVar bX) _ (SUNeq rem) = case bumpRemGe ll bX rem of
  MkBumpRem bY rem' -> MkShiftSubst (ShiftVar bY) (SUNeq rem')
shiftSubstGe ll (ShiftLam shB0) shV (SULam shV0 subB) =
  case shiftShiftFork LLZ shV0 shV of
    MkShiftFork shV0' shV1 -> case shiftSubstGe (LLS ll) shB0 shV0' subB of
      MkShiftSubst shR0 subB1 -> MkShiftSubst (ShiftLam shR0) (SULam shV1 subB1)
shiftSubstGe ll (ShiftApp shL shM) shV (SUApp subL subM) =
  case (shiftSubstGe ll shL shV subL, shiftSubstGe ll shM shV subM) of
    (MkShiftSubst shRL subL1, MkShiftSubst shRM subM1) ->
      MkShiftSubst (ShiftApp shRL shRM) (SUApp subL1 subM1)

bumpLeEq :: LeLift k kHi c -> BumpFin kHi c x1 -> x1 :~: FS c
bumpLeEq LLZ      BumpZ      = Refl
bumpLeEq (LLS ll) (BumpSS b) = case bumpLeEq ll b of Refl -> Refl

bumpRemLe :: LeLift k kHi c -> BumpFin kHi x x1 -> RemoveFin c x y -> BumpRemRes k (FS c) x1 y
bumpRemLe LLZ      BumpZ        rem        = MkBumpRem BumpZ (RemSS rem)
bumpRemLe (LLS _)  BumpSZ       RemLt      = MkBumpRem BumpSZ RemLt
bumpRemLe (LLS ll) (BumpSS bX0) (RemSS r0) = case bumpRemLe ll bX0 r0 of
  MkBumpRem bY0 r0' -> MkBumpRem (BumpSS bY0) (RemSS r0')

shiftSubstLe :: LeLift k kHi c -> ShiftU kHi v v1 -> ShiftU k w w1 -> SubstAtU c w v v' -> ShiftSubstRes k (FS c) w1 v1 v'
shiftSubstLe ll (ShiftVar bX) shW SUEq = case bumpLeEq ll bX of
  Refl -> MkShiftSubst shW SUEq
shiftSubstLe ll (ShiftVar bX) _ (SUNeq rem) = case bumpRemLe ll bX rem of
  MkBumpRem bY rem' -> MkShiftSubst (ShiftVar bY) (SUNeq rem')
shiftSubstLe ll (ShiftLam shB0) shW (SULam shW0 subB) =
  case shiftShiftFork LLZ shW0 shW of
    MkShiftFork shW0' shW1 -> case shiftSubstLe (LLS ll) shB0 shW0' subB of
      MkShiftSubst shV0' subB1 -> MkShiftSubst (ShiftLam shV0') (SULam shW1 subB1)
shiftSubstLe ll (ShiftApp shL shM) shW (SUApp subL subM) =
  case (shiftSubstLe ll shL shW subL, shiftSubstLe ll shM shW subM) of
    (MkShiftSubst shVL subL1, MkShiftSubst shVM subM1) ->
      MkShiftSubst (ShiftApp shVL shVM) (SUApp subL1 subM1)

-- | Strengthening: substituting into a freshly weakened slot cancels the weakening.
bumpToRemove :: BumpFin d x y -> RemoveFin d y x
bumpToRemove BumpZ      = RemGt
bumpToRemove BumpSZ     = RemLt
bumpToRemove (BumpSS b) = RemSS (bumpToRemove b)

substShiftCancel :: TermW v -> ShiftU d w w1 -> SubstAtU d v w1 w
substShiftCancel _  (ShiftVar b)     = SUNeq (bumpToRemove b)
substShiftCancel wv (ShiftLam shB)   = case shiftEx WFZ wv of
  MkShiftEx shV wv' -> SULam shV (substShiftCancel wv' shB)
substShiftCancel wv (ShiftApp s1 s2) = SUApp (substShiftCancel wv s1) (substShiftCancel wv s2)

-- | Substitution commutation (`d <= c`): substituting at `dHi` then `c` equals
-- substituting `shift d w` at `FS c` then `v[c := w]` at `d`.
leLiftNeq :: LeLift d dHi c -> dHi :~: FS c -> Void
leLiftNeq LLZ      eq   = case eq of {}
leLiftNeq (LLS ll) Refl = leLiftNeq ll Refl

leLiftRem :: LeLift d dHi c -> RemoveFin (FS c) dHi y -> y :~: d
leLiftRem LLZ      RemLt      = Refl
leLiftRem (LLS ll) (RemSS r)  = case leLiftRem ll r of Refl -> Refl

leLiftRemHi :: LeLift d dHi c -> RemoveFin dHi (FS c) y -> y :~: c
leLiftRemHi LLZ      RemGt     = Refl
leLiftRemHi (LLS ll) (RemSS r) = case leLiftRemHi ll r of Refl -> Refl

type RemCommRes :: forall (n :: Nat). Fin (Succ n) -> Fin (Succ n) -> Fin (Succ n) -> Fin (Succ n) -> Type
data RemCommRes c d y1 y2 where
  MkRemComm :: RemoveFin c y1 z -> RemoveFin d y2 z -> RemCommRes c d y1 y2

remCommuteLe :: LeLift d dHi c -> RemoveFin dHi x y1 -> RemoveFin (FS c) x y2 -> RemCommRes c d y1 y2
remCommuteLe LLZ      RemGt      (RemSS r2) = MkRemComm r2 RemGt
remCommuteLe (LLS _)  RemLt      RemLt      = MkRemComm RemLt RemLt
remCommuteLe (LLS ll) (RemSS r1) (RemSS r2) = case remCommuteLe ll r1 r2 of
  MkRemComm rc rd -> MkRemComm (RemSS rc) (RemSS rd)

type SubstSubstRes :: forall (n :: Nat). Fin (Succ n) -> UTerm n -> Fin (Succ n) -> UTerm n -> UTerm (Succ n) -> UTerm (Succ n) -> Type
data SubstSubstRes c w d v' r1 r2 where
  MkSubstSubst :: SubstAtU c w r1 rFinal -> SubstAtU d v' r2 rFinal -> SubstSubstRes c w d v' r1 r2

substSubst :: LeLift d dHi c -> TermW v' -> ShiftU d w w1 -> SubstAtU c w v v'
           -> SubstAtU dHi v b r1 -> SubstAtU (FS c) w1 b r2
           -> SubstSubstRes c w d v' r1 r2
substSubst ll _   _   _    SUEq              SUEq               = absurd (leLiftNeq ll Refl)
substSubst ll _   _   subW SUEq              (SUNeq rem2)       = case leLiftRem ll rem2 of
  Refl -> MkSubstSubst subW SUEq
substSubst ll wv' shW _    (SUNeq rem1)      SUEq               = case leLiftRemHi ll rem1 of
  Refl -> MkSubstSubst SUEq (substShiftCancel wv' shW)
substSubst ll _   _   _    (SUNeq rem1)      (SUNeq rem2)       = case remCommuteLe ll rem1 rem2 of
  MkRemComm rc rd -> MkSubstSubst (SUNeq rc) (SUNeq rd)
substSubst ll wv' shW subW (SULam shV subB1) (SULam shW1 subB2) =
  case shiftShift LLZ shW shW1 of
    MkShiftSeq shW0 shW1' -> case shiftSubstLe LLZ shV shW0 subW of
      MkShiftSubst shV' subW1 ->
        case substSubst (LLS ll) (shiftTargetW shV' wv') shW1' subW1 subB1 subB2 of
          MkSubstSubst subOut1 subOut2 ->
            MkSubstSubst (SULam shW0 subOut1) (SULam shV' subOut2)
substSubst ll wv' shW subW (SUApp s1L s1M)   (SUApp s2L s2M)    =
  case (substSubst ll wv' shW subW s1L s2L, substSubst ll wv' shW subW s1M s2M) of
    (MkSubstSubst o1L o2L, MkSubstSubst o1M o2M) ->
      MkSubstSubst (SUApp o1L o1M) (SUApp o2L o2M)

{-# LINE 569 "content/part2/Confluence.md" #-}
-- | Two terms `m1` and `m2` are joinable under `rel` if they share a common reduct `k`.
type Joinable :: forall (n :: Nat). (UTerm n -> UTerm n -> Type) -> UTerm n -> UTerm n -> Type
data Joinable rel m1 m2 where
  Join :: rel m1 k -> rel m2 k -> Joinable rel m1 m2

-- | Joinability is symmetric for any reduction relation `rel`.
joinSym :: Joinable rel m1 m2 -> Joinable rel m2 m1
joinSym (Join p1 p2) = Join p2 p1

-- | Weakening preserves parallel reduction.
type ParShiftRes :: forall (n :: Nat). Fin (Succ n) -> UTerm n -> UTerm (Succ n) -> Type
data ParShiftRes c w' w1 where
  MkParShift :: ShiftU c w' w1' -> Par w1 w1' -> ParShiftRes c w' w1

parShift :: ShiftU c w w1 -> Par w w' -> ParShiftRes c w' w1
parShift (ShiftVar b)                PVar              = MkParShift (ShiftVar b) PVar
parShift (ShiftLam sh)               (PLam pb)         = case parShift sh pb of
  MkParShift sh' pb' -> MkParShift (ShiftLam sh') (PLam pb')
parShift (ShiftApp sL sM)            (PApp pL pM)      = case (parShift sL pL, parShift sM pM) of
  (MkParShift sL' pL', MkParShift sM' pM') -> MkParShift (ShiftApp sL' sM') (PApp pL' pM')
parShift (ShiftApp (ShiftLam shB) shV) (PBeta pb pv sub) =
  case (parShift shB pb, parShift shV pv) of
    (MkParShift shB' pb1, MkParShift shV' pv1) -> case shiftSubstGe LLZ shB' shV' sub of
      MkShiftSubst shR sub1 -> MkParShift shR (PBeta pb1 pv1 sub1)

-- | Parallel substitution lemma: `Par b b'` and `Par w w'` preserve `SubstAtU c w b r`.
type ParSubstRes :: forall (n :: Nat). Fin (Succ n) -> UTerm n -> UTerm (Succ n) -> UTerm n -> Type
data ParSubstRes c w' b' r where
  MkParSubst :: SubstAtU c w' b' r' -> Par r r' -> ParSubstRes c w' b' r

parSubst :: TermW b -> TermW w' -> SubstAtU c w b r -> Par b b' -> Par w w' -> ParSubstRes c w' b' r
parSubst _  _   SUEq          PVar pw = MkParSubst SUEq pw
parSubst _  _   (SUNeq rem)   PVar _  = MkParSubst (SUNeq rem) PVar
parSubst (WLam wb0) ww' (SULam shW subB) (PLam pb) pw =
  case parShift shW pw of
    MkParShift shW' pw1 -> case parSubst wb0 (shiftTargetW shW' ww') subB pb pw1 of
      MkParSubst subB' pb' -> MkParSubst (SULam shW' subB') (PLam pb')
parSubst (WApp wl wm) ww' (SUApp sL sM) (PApp pL pM) pw =
  case (parSubst wl ww' sL pL pw, parSubst wm ww' sM pM pw) of
    (MkParSubst sL' pL', MkParSubst sM' pM') -> MkParSubst (SUApp sL' sM') (PApp pL' pM')
parSubst (WApp (WLam wb0) wv0) ww' (SUApp (SULam shW subB) subV) (PBeta pb pv subInner) pw =
  case parShift shW pw of
    MkParShift shW' pw1 ->
      case (parSubst wb0 (shiftTargetW shW' ww') subB pb pw1, parSubst wv0 ww' subV pv pw) of
        (MkParSubst subB' pb1, MkParSubst subV' pv1) ->
          let wrV' = substTargetW subV' ww' (parTargetW pv wv0)
          in case substSubst LLZ wrV' shW' subV' subInner subB' of
               MkSubstSubst subOut subBeta -> MkParSubst subOut (PBeta pb1 pv1 subBeta)

-- | One-step Diamond Property of parallel reduction (`par-diamond`)!
parDiamondW :: TermW m -> Par m n1 -> Par m n2 -> Joinable Par n1 n2
parDiamondW _                PVar             PVar             = Join PVar PVar
parDiamondW (WLam wb)        (PLam b1)        (PLam b2)        = case parDiamondW wb b1 b2 of
  Join q1 q2 -> Join (PLam q1) (PLam q2)
parDiamondW (WApp wl wm)     (PApp l1 m1)     (PApp l2 m2)     =
  case (parDiamondW wl l1 l2, parDiamondW wm m1 m2) of
    (Join ql1 ql2, Join qm1 qm2) -> Join (PApp ql1 qm1) (PApp ql2 qm2)
parDiamondW (WApp (WLam wb) ww) (PApp (PLam b1) w1) (PBeta b2 w2 sub2) =
  case (parDiamondW wb b1 b2, parDiamondW ww w1 w2) of
    (Join qb1 qb2, Join qw1 qw2) ->
      let wb2'   = parTargetW b2 wb
          wwStar = parTargetW qw2 (parTargetW w2 ww)
      in case parSubst wb2' wwStar sub2 qb2 qw2 of
           MkParSubst subStar pr2 -> Join (PBeta qb1 qw1 subStar) pr2
parDiamondW (WApp (WLam wb) ww) (PBeta b1 w1 sub1) (PApp (PLam b2) w2) =
  joinSym (parDiamondW (WApp (WLam wb) ww) (PApp (PLam b2) w2) (PBeta b1 w1 sub1))
parDiamondW (WApp (WLam wb) ww) (PBeta b1 w1 sub1) (PBeta b2 w2 sub2) =
  case (parDiamondW wb b1 b2, parDiamondW ww w1 w2) of
    (Join qb1 qb2, Join qw1 qw2) ->
      let wb1'   = parTargetW b1 wb
          wb2'   = parTargetW b2 wb
          wwStar = parTargetW qw1 (parTargetW w1 ww)
      in case (parSubst wb1' wwStar sub1 qb1 qw1, parSubst wb2' wwStar sub2 qb2 qw2) of
           (MkParSubst subStar1 pr1, MkParSubst subStar2 pr2) ->
             case substDeterm subStar1 subStar2 of
               Refl -> Join pr1 pr2

parDiamond :: forall (n :: Nat) (n1 n2 :: UTerm n).
              foreach (m :: UTerm n) -> Par m n1 -> Par m n2 -> Joinable Par n1 n2
parDiamond m = parDiamondW (mkTermW m)

{-# LINE 667 "content/part2/Confluence.md" #-}
-- | Strip Lemma: one `Par` step commutes with any sequence of `ParSteps`.
stripW :: TermW m -> Par m n1 -> ParSteps m n2 -> Joinable ParSteps n1 n2
stripW _  p1 PSRefl         = Join PSRefl (PSCons p1 PSRefl)
stripW wm p1 (PSCons p2 ps) = case parDiamondW wm p1 p2 of
  Join q1 q2 -> case stripW (parTargetW p2 wm) q2 ps of
    Join r1 r2 -> Join (PSCons q1 r1) r2

strip :: forall (n :: Nat) (n1 n2 :: UTerm n).
         foreach (m :: UTerm n) -> Par m n1 -> ParSteps m n2 -> Joinable ParSteps n1 n2
strip m = stripW (mkTermW m)

-- | Confluence of parallel reduction (`par-confluence`).
parConfluenceW :: TermW l -> ParSteps l m1 -> ParSteps l m2 -> Joinable ParSteps m1 m2
parConfluenceW _  PSRefl         ps2 = Join ps2 PSRefl
parConfluenceW wl (PSCons p1 q1) ps2 = case stripW wl p1 ps2 of
  Join r1 r2 -> case parConfluenceW (parTargetW p1 wl) q1 r1 of
    Join s1 s2 -> Join s1 (psTrans r2 s2)

parConfluence :: forall (n :: Nat) (m1 m2 :: UTerm n).
                 foreach (l :: UTerm n) -> ParSteps l m1 -> ParSteps l m2 -> Joinable ParSteps m1 m2
parConfluence l = parConfluenceW (mkTermW l)

-- | Unconditional Church-Rosser Confluence for full β-reduction (`_—↠_`)!
churchRosser :: forall (n :: Nat) (m1 m2 :: UTerm n).
                foreach (l :: UTerm n)
             -> BetaSteps l m1 -> BetaSteps l m2
             -> Joinable BetaSteps m1 m2
churchRosser l bs1 bs2 =
  let wl = mkTermW l
  in case parConfluenceW wl (betasToParsW wl bs1) (betasToParsW wl bs2) of
       Join ps1 ps2 -> Join (parsToBetas ps1) (parsToBetas ps2)

-- | Neutral terms cannot take a β-step.
neutralNoBetaStep :: Neutral m -> Not (BetaStep m n)
neutralNoBetaStep NVar         s          = case s of {}
neutralNoBetaStep (NApp nl _)  (XiApp1 s) = neutralNoBetaStep nl s
neutralNoBetaStep (NApp _  nm) (XiApp2 s) = normalNoBetaStep nm s
neutralNoBetaStep (NApp nl _)  (Beta _)   = case nl of {}

-- | Normal forms cannot take a β-step.
normalNoBetaStep :: Normal m -> Not (BetaStep m n)
normalNoBetaStep (NNeu nm) s         = neutralNoBetaStep nm s
normalNoBetaStep (NLam nb) (XiLam s) = normalNoBetaStep nb s

-- | A normal form reduces in zero or more steps only to itself.
normalNoBetaSteps :: Normal m -> BetaSteps m n -> m :~: n
normalNoBetaSteps _  BRefl       = Refl
normalNoBetaSteps nm (BCons s _) = absurd (normalNoBetaStep nm s)

-- | Neutral terms reduce under parallel reduction only to themselves (`neutral-⇒`).
neutralPar :: Neutral m -> Par m n -> m :~: n
neutralPar NVar         PVar         = Refl
neutralPar (NApp nl nm) (PApp pl pm) = case (neutralPar nl pl, normalPar nm pm) of
  (Refl, Refl) -> Refl
neutralPar (NApp nl _)  (PBeta _ _ _) = case nl of {}

-- | Normal forms reduce under parallel reduction only to themselves (`normal-⇒`).
normalPar :: Normal m -> Par m n -> m :~: n
normalPar (NNeu nm) p         = neutralPar nm p
normalPar (NLam nb) (PLam pb) = case normalPar nb pb of
  Refl -> Refl

-- | Normal forms reduce under multi-step parallel reduction only to themselves (`normal-⇒*`).
normalParSteps :: Normal m -> ParSteps m n -> m :~: n
normalParSteps _  PSRefl        = Refl
normalParSteps nm (PSCons p ps) = case normalPar nm p of
  Refl -> normalParSteps nm ps

-- | Unconditional corollary of Church-Rosser: every term has at most one normal form!
uniqueNormalForm :: forall (n :: Nat) (m1 m2 :: UTerm n).
                    foreach (l :: UTerm n)
                 -> BetaSteps l m1 -> BetaSteps l m2
                 -> Normal m1 -> Normal m2
                 -> m1 :~: m2
uniqueNormalForm l bs1 bs2 nm1 nm2 =
  case churchRosser l bs1 bs2 of
    Join r1 r2 -> case (normalNoBetaSteps nm1 r1, normalNoBetaSteps nm2 r2) of
      (Refl, Refl) -> Refl
