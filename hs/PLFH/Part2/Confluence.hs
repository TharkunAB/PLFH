-- Generated from content/part2/Confluence.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE AllowAmbiguousTypes, DependentTypes #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
{-# LINE 77 "content/part2/Confluence.md" #-}
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
  , betaTargetW
  , parRefl
  , betaToPar
  , ParSteps (..)
  , psTrans
  , parToBetas
  , parsToBetas
  , omegaPar
  , Joinable (..)
  , joinSym
  , parRename
  , ParSub
  , parSubst
  , parSubstSingle
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
import Data.Void (absurd)
import Data.Nat.Dependent (Nat (..))
import PLFH.Part1.Decidable (Not)
import PLFH.Part2.Substitution
  ( HasFin (..)
  , HasTerm (..)
  , RenW
  , Rename
  , SubW
  , Subst
  , evalSubst
  , extRenW
  , extsW
  , finWToHas
  , hasToTermW
  , renCommute
  , shiftW
  , singleW
  , substCommute
  , termWToHas
  )
import PLFH.Part2.Untyped
  ( BetaStep (..)
  , BetaSteps (..)
  , Fin (..)
  , FinW (..)
  , Neutral (..)
  , Normal (..)
  , OmegaTerm
  , TermW (..)
  , UTerm (..)
  , bsApp1
  , bsApp2
  , bsLam
  , bsTrans
  , extU
  , extsU
  , mkFinW
  , mkTermW
  , renameU
  , shiftFin
  , singleSubstU
  , substSingleU
  , substU
  )

{-# LINE 205 "content/part2/Confluence.md" #-}
-- | Parallel β-reduction: contract any subset of redexes simultaneously.
type Par :: forall (n :: Nat). UTerm n -> UTerm n -> Type
data Par t t' where
  PVar  :: Par (UVar x) (UVar x)
  PLam  :: Par b b' -> Par (ULam b) (ULam b')
  PApp  :: Par l l' -> Par m m' -> Par (UApp l m) (UApp l' m')
  PBeta :: forall (n :: Nat) (b b' :: UTerm (Succ n)) (w w' :: UTerm n).
           Par b b' -> Par w w' -> Par (UApp (ULam b) w) (substSingleU b' w')

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
parToBetas PVar          = BRefl
parToBetas (PLam p)      = bsLam (parToBetas p)
parToBetas (PApp pl pm)  = bsTrans (bsApp1 (parToBetas pl)) (bsApp2 (parToBetas pm))
parToBetas (PBeta pb pw) =
  bsTrans (bsApp1 (bsLam (parToBetas pb)))
    (bsTrans (bsApp2 (parToBetas pw)) (BCons Beta BRefl))

-- | Multi-step parallel reduction embeds into multi-step β-reduction.
parsToBetas :: ParSteps m n -> BetaSteps m n
parsToBetas PSRefl       = BRefl
parsToBetas (PSCons p q) = bsTrans (parToBetas p) (parsToBetas q)

-- | Concrete parallel reduction step: Ω ⇛ Ω.
omegaPar :: Par OmegaTerm OmegaTerm
omegaPar = PBeta (PApp PVar PVar) (PLam (PApp PVar PVar))

{-# LINE 252 "content/part2/Confluence.md" #-}
substSingleW :: forall (n :: Nat) (b :: UTerm (Succ n)) (w :: UTerm n).
                TermW b -> TermW w -> TermW (substSingleU b w)
substSingleW wb ww = case (termWToHas wb, termWToHas ww) of
  (MkHasTerm b', MkHasTerm w') ->
    hasToTermW (evalSubst @(Succ n) @n @(singleSubstU w) (singleW @n w') b')

parTargetW :: Par t t' -> TermW t -> TermW t'
parTargetW PVar          (WVar fx)          = WVar fx
parTargetW (PLam pb)     (WLam wb)          = WLam (parTargetW pb wb)
parTargetW (PApp pl pm)  (WApp wl wm)       = WApp (parTargetW pl wl) (parTargetW pm wm)
parTargetW (PBeta pb pw) (WApp (WLam wb) ww) =
  substSingleW (parTargetW pb wb) (parTargetW pw ww)

betaTargetW :: BetaStep t t' -> TermW t -> TermW t'
betaTargetW (XiApp1 sl) (WApp wl wm)       = WApp (betaTargetW sl wl) wm
betaTargetW (XiApp2 sm) (WApp wl wm)       = WApp wl (betaTargetW sm wm)
betaTargetW (XiLam sb)  (WLam wb)          = WLam (betaTargetW sb wb)
betaTargetW Beta        (WApp (WLam wb) ww) = substSingleW wb ww

-- | Parallel reduction is reflexive across the non-uniform scope index `n`.
parReflW :: TermW m -> Par m m
parReflW (WVar _)     = PVar
parReflW (WLam wb)    = PLam (parReflW wb)
parReflW (WApp wl wm) = PApp (parReflW wl) (parReflW wm)

parRefl :: forall (n :: Nat). foreach (m :: UTerm n) -> Par m m
parRefl m = parReflW (mkTermW m)

-- | Every single β-step is a parallel reduction step (`—→-to-⇒`).
betaToParW :: TermW l -> BetaStep l r -> Par l r
betaToParW (WVar _)            s           = case s of {}
betaToParW (WApp wl wm)        (XiApp1 sl) = PApp (betaToParW wl sl) (parReflW wm)
betaToParW (WApp wl wm)        (XiApp2 sm) = PApp (parReflW wl) (betaToParW wm sm)
betaToParW (WLam wb)           (XiLam sb)  = PLam (betaToParW wb sb)
betaToParW (WApp (WLam wb) ww) Beta        = PBeta (parReflW wb) (parReflW ww)

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

{-# LINE 320 "content/part2/Confluence.md" #-}
-- | Two terms `m1` and `m2` are joinable under `rel` if they share a common reduct `k`.
type Joinable :: forall (n :: Nat). (UTerm n -> UTerm n -> Type) -> UTerm n -> UTerm n -> Type
data Joinable rel m1 m2 where
  Join :: rel m1 k -> rel m2 k -> Joinable rel m1 m2

-- | Joinability is symmetric for any reduction relation `rel`.
joinSym :: Joinable rel m1 m2 -> Joinable rel m2 m1
joinSym (Join p1 p2) = Join p2 p1

-- | Simultaneous renaming preserves parallel reduction (`rename-⇒`).
parRename :: forall m n (r :: Rename m n) (t t' :: UTerm m).
             RenW @m @n r -> TermW t -> Par t t' -> Par (renameU r t) (renameU r t')
parRename _  _                PVar         = PVar
parRename rw (WLam wb)        (PLam pb)    =
  PLam (parRename @(Succ m) @(Succ n) @(extU r) (extRenW @m @n @r rw) wb pb)
parRename rw (WApp wl wm)     (PApp pl pm) =
  PApp (parRename @m @n @r rw wl pl) (parRename @m @n @r rw wm pm)
parRename rw (WApp (WLam wb) ww) (PBeta pb pw) =
  case (termWToHas (parTargetW pb wb), termWToHas (parTargetW pw ww)) of
    (MkHasTerm b', MkHasTerm w') ->
      case renCommute @m @n @r rw w' b' of
        Refl -> PBeta (parRename @(Succ m) @(Succ n) @(extU r) (extRenW @m @n @r rw) wb pb)
                      (parRename @m @n @r rw ww pw)

-- | Pointwise parallel reduction between two simultaneous substitutions.
type ParSub :: forall m n. Subst m n -> Subst m n -> Type
type ParSub @m @n s1 s2 = foreach (x :: Fin m) -> Par (s1 x) (s2 x)

parSubstExts :: forall m n (s1 s2 :: Subst m n).
                SubW @m @n s1 -> ParSub @m @n s1 s2
             -> ParSub @(Succ m) @(Succ n) (extsU s1) (extsU s2)
parSubstExts _   _  FZ     = PVar
parSubstExts sw1 ps (FS x) =
  parRename @n @(Succ n) @shiftFin (shiftW @n) (hasToTermW (sw1 x)) (ps x)

-- | Simultaneous parallel substitution lemma (`subst-⇒`).
parSubst :: forall m n (s1 s2 :: Subst m n) (t t' :: UTerm m).
            SubW @m @n s1 -> SubW @m @n s2
         -> ParSub @m @n s1 s2
         -> TermW t -> Par t t'
         -> Par (substU s1 t) (substU s2 t')
parSubst _   _   ps (WVar fx)    PVar         = case finWToHas fx of MkHasFin x -> ps x
parSubst sw1 sw2 ps (WLam wb)    (PLam pb)    =
  PLam (parSubst @(Succ m) @(Succ n) @(extsU s1) @(extsU s2)
          (extsW @m @n @s1 sw1) (extsW @m @n @s2 sw2)
          (parSubstExts @m @n @s1 @s2 sw1 ps) wb pb)
parSubst sw1 sw2 ps (WApp wl wm) (PApp pl pm) =
  PApp (parSubst @m @n @s1 @s2 sw1 sw2 ps wl pl)
       (parSubst @m @n @s1 @s2 sw1 sw2 ps wm pm)
parSubst sw1 sw2 ps (WApp (WLam wb) ww) (PBeta pb pw) =
  case (termWToHas (parTargetW pb wb), termWToHas (parTargetW pw ww)) of
    (MkHasTerm b', MkHasTerm w') ->
      case substCommute @m @n @s2 sw2 w' b' of
        Refl ->
          PBeta (parSubst @(Succ m) @(Succ n) @(extsU s1) @(extsU s2)
                   (extsW @m @n @s1 sw1) (extsW @m @n @s2 sw2)
                   (parSubstExts @m @n @s1 @s2 sw1 ps) wb pb)
                (parSubst @m @n @s1 @s2 sw1 sw2 ps ww pw)

singleParSub :: forall n (w w' :: UTerm n).
                Par w w' -> ParSub @(Succ n) @n (singleSubstU w) (singleSubstU w')
singleParSub pw FZ     = pw
singleParSub _  (FS x) = parReflW (WVar (mkFinW x))

-- | Single-variable parallel substitution lemma: `Par b b'` and `Par w w'` imply
-- `Par (substSingleU b w) (substSingleU b' w')`.
parSubstSingle :: forall n (b b' :: UTerm (Succ n)) (w w' :: UTerm n).
                  TermW b -> TermW w -> TermW w'
               -> Par b b' -> Par w w'
               -> Par (substSingleU b w) (substSingleU b' w')
parSubstSingle wb ww ww' pb pw =
  case (termWToHas ww, termWToHas ww') of
    (MkHasTerm w1, MkHasTerm w2) ->
      parSubst @(Succ n) @n @(singleSubstU w) @(singleSubstU w')
        (singleW @n w1) (singleW @n w2) (singleParSub @n pw) wb pb

-- | One-step Diamond Property of parallel reduction (`par-diamond`)!
parDiamondW :: TermW m -> Par m n1 -> Par m n2 -> Joinable Par n1 n2
parDiamondW _                PVar             PVar             = Join PVar PVar
parDiamondW (WLam wb)        (PLam b1)        (PLam b2)        = case parDiamondW wb b1 b2 of
  Join q1 q2 -> Join (PLam q1) (PLam q2)
parDiamondW (WApp wl wm)     (PApp l1 m1)     (PApp l2 m2)     =
  case (parDiamondW wl l1 l2, parDiamondW wm m1 m2) of
    (Join ql1 ql2, Join qm1 qm2) -> Join (PApp ql1 qm1) (PApp ql2 qm2)
parDiamondW (WApp (WLam wb) ww) (PApp (PLam b1) w1) (PBeta b2 w2) =
  case (parDiamondW wb b1 b2, parDiamondW ww w1 w2) of
    (Join qb1 qb2, Join qw1 qw2) ->
      let wb2'   = parTargetW b2 wb
          ww2'   = parTargetW w2 ww
          wwStar = parTargetW qw2 ww2'
      in Join (PBeta qb1 qw1) (parSubstSingle wb2' ww2' wwStar qb2 qw2)
parDiamondW (WApp (WLam wb) ww) (PBeta b1 w1) (PApp (PLam b2) w2) =
  joinSym (parDiamondW (WApp (WLam wb) ww) (PApp (PLam b2) w2) (PBeta b1 w1))
parDiamondW (WApp (WLam wb) ww) (PBeta b1 w1) (PBeta b2 w2) =
  case (parDiamondW wb b1 b2, parDiamondW ww w1 w2) of
    (Join qb1 qb2, Join qw1 qw2) ->
      let wb1'   = parTargetW b1 wb
          wb2'   = parTargetW b2 wb
          ww1'   = parTargetW w1 ww
          ww2'   = parTargetW w2 ww
          wwStar = parTargetW qw1 ww1'
      in Join (parSubstSingle wb1' ww1' wwStar qb1 qw1)
              (parSubstSingle wb2' ww2' wwStar qb2 qw2)

parDiamond :: forall (n :: Nat) (n1 n2 :: UTerm n).
              foreach (m :: UTerm n) -> Par m n1 -> Par m n2 -> Joinable Par n1 n2
parDiamond m = parDiamondW (mkTermW m)

{-# LINE 444 "content/part2/Confluence.md" #-}
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

-- | Church-Rosser confluence for full β-reduction (`_—↠_`).
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
neutralNoBetaStep (NApp nl _)  Beta       = case nl of {}

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
neutralPar (NApp nl _)  (PBeta _ _)  = case nl of {}

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

-- | Corollary of Church-Rosser: every term has at most one normal form.
uniqueNormalForm :: forall (n :: Nat) (m1 m2 :: UTerm n).
                    foreach (l :: UTerm n)
                 -> BetaSteps l m1 -> BetaSteps l m2
                 -> Normal m1 -> Normal m2
                 -> m1 :~: m2
uniqueNormalForm l bs1 bs2 nm1 nm2 =
  case churchRosser l bs1 bs2 of
    Join r1 r2 -> case (normalNoBetaSteps nm1 r1, normalNoBetaSteps nm2 r2) of
      (Refl, Refl) -> Refl
