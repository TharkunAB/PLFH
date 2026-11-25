-- Generated from content/part2/Bisimulation.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE AllowAmbiguousTypes, DependentTypes #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
{-# LINE 53 "content/part2/Bisimulation.md" #-}
module PLFH.Part2.Bisimulation
  ( SimRel (..)
  , simRefl
  , simTrans
  , simValue
  , simValueInv
  , valNoStep
  , Renaming
  , simRename
  , SubstFn
  , Compatible
  , simExt
  , simSubst
  , Leg (..)
  , LegInv (..)
  , SubstCompat (..)
  , sim
  , simInv
  , simSteps
  , simStepsInv
  , letDesugarSim
  , letDesugarSteps
  , letDesugarStepsInv
  ) where

import Data.Kind (Type)
import Data.Void (Void, absurd)
import GHC.Exts (U)
import qualified PLFH.Part2.More as M

{-# LINE 99 "content/part2/Bisimulation.md" #-}
-- | Structural bisimulation relation relating `let x = m in n` to `(λx. n') m'`
-- across all 19 constructors of `PLFH.Part2.More.Term`.
type SimRel :: forall (g :: M.Ctx) (a :: M.Ty). M.Term g a -> M.Term g a -> Type
data SimRel m m' where
  SimVar     :: SimRel (M.Var x) (M.Var x)
  SimLam     :: SimRel n n' -> SimRel (M.Lam n) (M.Lam n')
  SimApp     :: SimRel l l' -> SimRel m m' -> SimRel (M.App l m) (M.App l' m')
  SimZero    :: SimRel M.Zero M.Zero
  SimSuc     :: SimRel m m' -> SimRel (M.Suc m) (M.Suc m')
  SimCaseNat :: SimRel n n' -> SimRel z z' -> SimRel s s'
             -> SimRel (M.CaseNat n z s) (M.CaseNat n' z' s')
  SimMu      :: SimRel n n' -> SimRel (M.Mu n) (M.Mu n')
  SimLet     :: SimRel m m' -> SimRel n n' -> SimRel (M.Let m n) (M.Let m' n')
  SimLetApp  :: SimRel m m' -> SimRel n n' -> SimRel (M.Let m n) (M.App (M.Lam n') m')
  SimTT      :: SimRel M.TT M.TT
  SimPair    :: SimRel l l' -> SimRel r r' -> SimRel (M.Pair l r) (M.Pair l' r')
  SimFst     :: SimRel p p' -> SimRel (M.Fst p) (M.Fst p')
  SimSnd     :: SimRel p p' -> SimRel (M.Snd p) (M.Snd p')
  SimInl     :: SimRel x x' -> SimRel (M.Inl x) (M.Inl x')
  SimInr     :: SimRel y y' -> SimRel (M.Inr y) (M.Inr y')
  SimCaseSum :: SimRel s s' -> SimRel l l' -> SimRel r r'
             -> SimRel (M.CaseSum s l r) (M.CaseSum s' l' r')
  SimAbsurd  :: SimRel m m' -> SimRel (M.Absurd m) (M.Absurd m')
  SimNil     :: SimRel M.Nil M.Nil
  SimCons    :: SimRel x x' -> SimRel xs xs' -> SimRel (M.Cons x xs) (M.Cons x' xs')
  SimCaseLst :: SimRel s s' -> SimRel n n' -> SimRel c c'
             -> SimRel (M.CaseLst s n c) (M.CaseLst s' n' c')

{-# LINE 135 "content/part2/Bisimulation.md" #-}
-- | Reflexivity (`~-refl`): every extended STLC term is related to itself.
simRefl :: forall (g :: M.Ctx) (a :: M.Ty). foreach (m :: M.Term g a) -> SimRel m m
simRefl t = case t of
  M.Var _         -> SimVar
  M.Lam n         -> SimLam (simRefl n)
  M.App l m       -> SimApp (simRefl l) (simRefl m)
  M.Zero          -> SimZero
  M.Suc n         -> SimSuc (simRefl n)
  M.CaseNat n z s -> SimCaseNat (simRefl n) (simRefl z) (simRefl s)
  M.Mu n          -> SimMu (simRefl n)
  M.Let m n       -> SimLet (simRefl m) (simRefl n)
  M.TT            -> SimTT
  M.Pair l r      -> SimPair (simRefl l) (simRefl r)
  M.Fst p         -> SimFst (simRefl p)
  M.Snd p         -> SimSnd (simRefl p)
  M.Inl x         -> SimInl (simRefl x)
  M.Inr y         -> SimInr (simRefl y)
  M.CaseSum s l r -> SimCaseSum (simRefl s) (simRefl l) (simRefl r)
  M.Absurd m      -> SimAbsurd (simRefl m)
  M.Nil           -> SimNil
  M.Cons x xs     -> SimCons (simRefl x) (simRefl xs)
  M.CaseLst s n c -> SimCaseLst (simRefl s) (simRefl n) (simRefl c)

-- | Transitivity of `SimRel`: `l ~ m` and `m ~ n` implies `l ~ n`.
simTrans :: SimRel l m -> SimRel m n -> SimRel l n
simTrans SimVar                 SimVar                  = SimVar
simTrans (SimLam s1)            (SimLam s2)             = SimLam (simTrans s1 s2)
simTrans (SimApp l1 m1)         (SimApp l2 m2)          = SimApp (simTrans l1 l2) (simTrans m1 m2)
simTrans SimZero                SimZero                 = SimZero
simTrans (SimSuc s1)            (SimSuc s2)             = SimSuc (simTrans s1 s2)
simTrans (SimCaseNat n1 z1 s1)  (SimCaseNat n2 z2 s2)   = SimCaseNat (simTrans n1 n2) (simTrans z1 z2) (simTrans s1 s2)
simTrans (SimMu s1)             (SimMu s2)              = SimMu (simTrans s1 s2)
simTrans (SimLet m1 n1)         (SimLet m2 n2)          = SimLet (simTrans m1 m2) (simTrans n1 n2)
simTrans (SimLet m1 n1)         (SimLetApp m2 n2)       = SimLetApp (simTrans m1 m2) (simTrans n1 n2)
simTrans (SimLetApp m1 n1)      (SimApp (SimLam n2) m2) = SimLetApp (simTrans m1 m2) (simTrans n1 n2)
simTrans SimTT                  SimTT                   = SimTT
simTrans (SimPair l1 r1)        (SimPair l2 r2)         = SimPair (simTrans l1 l2) (simTrans r1 r2)
simTrans (SimFst p1)            (SimFst p2)             = SimFst (simTrans p1 p2)
simTrans (SimSnd p1)            (SimSnd p2)             = SimSnd (simTrans p1 p2)
simTrans (SimInl x1)            (SimInl x2)             = SimInl (simTrans x1 x2)
simTrans (SimInr y1)            (SimInr y2)             = SimInr (simTrans y1 y2)
simTrans (SimCaseSum s1 l1 r1)  (SimCaseSum s2 l2 r2)   = SimCaseSum (simTrans s1 s2) (simTrans l1 l2) (simTrans r1 r2)
simTrans (SimAbsurd m1)         (SimAbsurd m2)          = SimAbsurd (simTrans m1 m2)
simTrans SimNil                 SimNil                  = SimNil
simTrans (SimCons x1 xs1)       (SimCons x2 xs2)        = SimCons (simTrans x1 x2) (simTrans xs1 xs2)
simTrans (SimCaseLst s1 n1 c1)  (SimCaseLst s2 n2 c2)   = SimCaseLst (simTrans s1 s2) (simTrans n1 n2) (simTrans c1 c2)

{-# LINE 192 "content/part2/Bisimulation.md" #-}
-- | Forward value preservation (`~-val`): all 9 value constructors.
simValue :: SimRel m m' -> M.Value m -> M.Value m'
simValue rel val = case val of
  M.VLam        -> case rel of { SimLam _      -> M.VLam }
  M.VZero       -> case rel of { SimZero       -> M.VZero }
  M.VSuc v      -> case rel of { SimSuc s      -> M.VSuc (simValue s v) }
  M.VTT         -> case rel of { SimTT         -> M.VTT }
  M.VPair v1 v2 -> case rel of { SimPair s1 s2 -> M.VPair (simValue s1 v1) (simValue s2 v2) }
  M.VInl v      -> case rel of { SimInl s      -> M.VInl (simValue s v) }
  M.VInr v      -> case rel of { SimInr s      -> M.VInr (simValue s v) }
  M.VNil        -> case rel of { SimNil        -> M.VNil }
  M.VCons v1 v2 -> case rel of { SimCons s1 s2 -> M.VCons (simValue s1 v1) (simValue s2 v2) }

-- | Backward value preservation (`~-val⁻¹`): all 9 value constructors.
simValueInv :: SimRel m m' -> M.Value m' -> M.Value m
simValueInv rel val = case val of
  M.VLam        -> case rel of { SimLam _      -> M.VLam }
  M.VZero       -> case rel of { SimZero       -> M.VZero }
  M.VSuc v      -> case rel of { SimSuc s      -> M.VSuc (simValueInv s v) }
  M.VTT         -> case rel of { SimTT         -> M.VTT }
  M.VPair v1 v2 -> case rel of { SimPair s1 s2 -> M.VPair (simValueInv s1 v1) (simValueInv s2 v2) }
  M.VInl v      -> case rel of { SimInl s      -> M.VInl (simValueInv s v) }
  M.VInr v      -> case rel of { SimInr s      -> M.VInr (simValueInv s v) }
  M.VNil        -> case rel of { SimNil        -> M.VNil }
  M.VCons v1 v2 -> case rel of { SimCons s1 s2 -> M.VCons (simValueInv s1 v1) (simValueInv s2 v2) }

-- | Values never step in extended call-by-value STLC.
valNoStep :: M.Value m -> M.Step m n -> Void
valNoStep val st = case val of
  M.VLam       -> case st of {}
  M.VZero      -> case st of {}
  M.VSuc v     -> case st of { M.XiSuc s -> valNoStep v s }
  M.VTT        -> case st of {}
  M.VPair v w  -> case st of { M.XiPair1 s -> valNoStep v s; M.XiPair2 _ s -> valNoStep w s }
  M.VInl v     -> case st of { M.XiInl s -> valNoStep v s }
  M.VInr v     -> case st of { M.XiInr s -> valNoStep v s }
  M.VNil       -> case st of {}
  M.VCons v vs -> case st of { M.XiCons1 s -> valNoStep v s; M.XiCons2 _ s -> valNoStep vs s }

{-# LINE 244 "content/part2/Bisimulation.md" #-}
-- | A sort-preserving map between lookup contexts.
type Renaming g d = forall x. M.Lookup g x %U -> M.Lookup d x

-- | Renaming preserves the structural simulation relation across all 20 constructors!
simRename :: forall g d a (r :: Renaming g d) (m :: M.Term g a) (n :: M.Term g a).
             SimRel m n -> SimRel (M.rename r m) (M.rename r n)
simRename SimVar = SimVar
simRename (SimLam s) = SimLam (simRename @_ @_ @_ @(M.ext r) s)
simRename (SimApp l m) = SimApp (simRename @_ @_ @_ @r l) (simRename @_ @_ @_ @r m)
simRename SimZero = SimZero
simRename (SimSuc s) = SimSuc (simRename @_ @_ @_ @r s)
simRename (SimCaseNat n z s) =
  SimCaseNat (simRename @_ @_ @_ @r n) (simRename @_ @_ @_ @r z)
             (simRename @_ @_ @_ @(M.ext r) s)
simRename (SimMu s) = SimMu (simRename @_ @_ @_ @(M.ext r) s)
simRename (SimLet m n) = SimLet (simRename @_ @_ @_ @r m) (simRename @_ @_ @_ @(M.ext r) n)
simRename (SimLetApp m n) = SimLetApp (simRename @_ @_ @_ @r m) (simRename @_ @_ @_ @(M.ext r) n)
simRename SimTT = SimTT
simRename (SimPair l r') = SimPair (simRename @_ @_ @_ @r l) (simRename @_ @_ @_ @r r')
simRename (SimFst p) = SimFst (simRename @_ @_ @_ @r p)
simRename (SimSnd p) = SimSnd (simRename @_ @_ @_ @r p)
simRename (SimInl s) = SimInl (simRename @_ @_ @_ @r s)
simRename (SimInr s) = SimInr (simRename @_ @_ @_ @r s)
simRename (SimCaseSum s l r') =
  SimCaseSum (simRename @_ @_ @_ @r s) (simRename @_ @_ @_ @(M.ext r) l)
             (simRename @_ @_ @_ @(M.ext r) r')
simRename (SimAbsurd s) = SimAbsurd (simRename @_ @_ @_ @r s)
simRename SimNil = SimNil
simRename (SimCons x xs) = SimCons (simRename @_ @_ @_ @r x) (simRename @_ @_ @_ @r xs)
simRename (SimCaseLst xs n c) =
  SimCaseLst (simRename @_ @_ @_ @r xs) (simRename @_ @_ @_ @r n)
             (simRename @_ @_ @_ @(M.ext (M.ext r)) c)

{-# LINE 288 "content/part2/Bisimulation.md" #-}
-- | A sort-preserving simultaneous substitution callback between contexts.
type SubstFn g d = forall a. M.Lookup g a %U -> M.Term d a

-- | Pointwise simulation compatibility between two simultaneous substitutions.
type Compatible :: forall g d. SubstFn g d -> SubstFn g d -> Type
type Compatible @g @d p q = forall a. foreach (x :: M.Lookup g a) -> SimRel (p x) (q x)

-- | Extending two compatible substitutions under a binder preserves compatibility (`~-exts`).
simExt :: forall g d b (p :: SubstFn g d) (q :: SubstFn g d).
          Compatible p q
       -> Compatible @(M.CExt g b) @(M.CExt d b) (M.exts @g @d @b p) (M.exts @g @d @b q)
simExt step index = case index of
  M.Z   -> SimVar
  M.S x -> simRename @d @(M.CExt d b) @_ @(M.weakenLookup @d @b) @(p x) @(q x) (step x)

-- | Simultaneous substitution preserves `SimRel` across all 20 constructors (`~-subst`)!
simSubst :: forall g d a (p :: SubstFn g d) (q :: SubstFn g d) (n :: M.Term g a).
            foreach (m :: M.Term g a)
         -> Compatible p q
         -> SimRel m n
         -> SimRel (M.subst p m) (M.subst q n)
simSubst term = case term of
  M.Var x -> \step rel -> case rel of
    SimVar -> step x
  M.Lam body -> \step rel -> case rel of
    SimLam p0 ->
      SimLam (simSubst @(M.CExt g _) @(M.CExt d _) @_ @(M.exts @g @d @_ p) @(M.exts @g @d @_ q)
                body (simExt @g @d @_ @p @q step) p0)
  M.App f x -> \step rel -> case rel of
    SimApp p0 p1 ->
      SimApp (simSubst @g @d @_ @p @q f step p0) (simSubst @g @d @_ @p @q x step p1)
  M.Zero -> \_ rel -> case rel of
    SimZero -> SimZero
  M.Suc n -> \step rel -> case rel of
    SimSuc p0 -> SimSuc (simSubst @g @d @_ @p @q n step p0)
  M.CaseNat n z suc -> \step rel -> case rel of
    SimCaseNat p0 p1 p2 ->
      SimCaseNat (simSubst @g @d @_ @p @q n step p0)
                 (simSubst @g @d @_ @p @q z step p1)
                 (simSubst @(M.CExt g _) @(M.CExt d _) @_ @(M.exts @g @d @_ p) @(M.exts @g @d @_ q)
                    suc (simExt @g @d @_ @p @q step) p2)
  M.Mu body -> \step rel -> case rel of
    SimMu p0 ->
      SimMu (simSubst @(M.CExt g _) @(M.CExt d _) @_ @(M.exts @g @d @_ p) @(M.exts @g @d @_ q)
               body (simExt @g @d @_ @p @q step) p0)
  M.Let x body -> \step rel -> case rel of
    SimLet p0 p1 ->
      SimLet (simSubst @g @d @_ @p @q x step p0)
             (simSubst @(M.CExt g _) @(M.CExt d _) @_ @(M.exts @g @d @_ p) @(M.exts @g @d @_ q)
                body (simExt @g @d @_ @p @q step) p1)
    SimLetApp p0 p1 ->
      SimLetApp (simSubst @g @d @_ @p @q x step p0)
                (simSubst @(M.CExt g _) @(M.CExt d _) @_ @(M.exts @g @d @_ p) @(M.exts @g @d @_ q)
                   body (simExt @g @d @_ @p @q step) p1)
  M.TT -> \_ rel -> case rel of
    SimTT -> SimTT
  M.Pair x y -> \step rel -> case rel of
    SimPair p0 p1 ->
      SimPair (simSubst @g @d @_ @p @q x step p0) (simSubst @g @d @_ @p @q y step p1)
  M.Fst x -> \step rel -> case rel of
    SimFst p0 -> SimFst (simSubst @g @d @_ @p @q x step p0)
  M.Snd x -> \step rel -> case rel of
    SimSnd p0 -> SimSnd (simSubst @g @d @_ @p @q x step p0)
  M.Inl x -> \step rel -> case rel of
    SimInl p0 -> SimInl @(M.subst p x) (simSubst @g @d @_ @p @q x step p0)
  M.Inr y -> \step rel -> case rel of
    SimInr p0 -> SimInr @(M.subst p y) (simSubst @g @d @_ @p @q y step p0)
  M.CaseSum x l r -> \step rel -> case rel of
    SimCaseSum p0 p1 p2 ->
      SimCaseSum (simSubst @g @d @_ @p @q x step p0)
                 (simSubst @(M.CExt g _) @(M.CExt d _) @_ @(M.exts @g @d @_ p) @(M.exts @g @d @_ q)
                    l (simExt @g @d @_ @p @q step) p1)
                 (simSubst @(M.CExt g _) @(M.CExt d _) @_ @(M.exts @g @d @_ p) @(M.exts @g @d @_ q)
                    r (simExt @g @d @_ @p @q step) p2)
  M.Absurd x -> \step rel -> case rel of
    SimAbsurd p0 -> SimAbsurd @(M.subst p x) (simSubst @g @d @_ @p @q x step p0)
  M.Nil -> \_ rel -> case rel of
    SimNil -> SimNil
  M.Cons x xs -> \step rel -> case rel of
    SimCons p0 p1 ->
      SimCons (simSubst @g @d @_ @p @q x step p0) (simSubst @g @d @_ @p @q xs step p1)
  M.CaseLst xs z body -> \step rel -> case rel of
    SimCaseLst p0 p1 p2 ->
      SimCaseLst (simSubst @g @d @_ @p @q xs step p0)
                 (simSubst @g @d @_ @p @q z step p1)
                 (simSubst @(M.CExt (M.CExt g _) _) @(M.CExt (M.CExt d _) _) @_
                    @(M.exts @(M.CExt g _) @(M.CExt d _) @_ (M.exts @g @d @_ p))
                    @(M.exts @(M.CExt g _) @(M.CExt d _) @_ (M.exts @g @d @_ q))
                    body
                    (simExt @(M.CExt g _) @(M.CExt d _) @_
                       @(M.exts @g @d @_ p) @(M.exts @g @d @_ q)
                       (simExt @g @d @_ @p @q step))
                    p2)

{-# LINE 398 "content/part2/Bisimulation.md" #-}
-- | Forward simulation leg: `m' —→ n'` with `n ~ n'`.
type Leg :: forall (g :: M.Ctx) (a :: M.Ty).
            (M.Term g a -> M.Term g a -> Type) -> M.Term g a -> M.Term g a -> Type
data Leg step m' n where
  MkLeg :: step m' n' -> SimRel n n' -> Leg step m' n

-- | Backward simulation leg: `m —→ n` with `n ~ n'`.
type LegInv :: forall (g :: M.Ctx) (a :: M.Ty).
               (M.Term g a -> M.Term g a -> Type) -> M.Term g a -> M.Term g a -> Type
data LegInv step m n' where
  MkLegInv :: step m n -> SimRel n n' -> LegInv step m n'

-- | Substitution compatibility bundle for `M.substSingle` and `M.substDouble`.
data SubstCompat where
  MkSubstCompat
    :: (forall (g :: M.Ctx) (a :: M.Ty) (b :: M.Ty)
               (n :: M.Term (M.CExt g a) b) (n' :: M.Term (M.CExt g a) b)
               (v :: M.Term g a) (v' :: M.Term g a).
          SimRel n n' -> SimRel v v' -> SimRel (M.substSingle n v) (M.substSingle n' v'))
    -> (forall (g :: M.Ctx) (a :: M.Ty) (b :: M.Ty)
               (c :: M.Term (M.CExt (M.CExt g a) (M.TList a)) b)
               (c' :: M.Term (M.CExt (M.CExt g a) (M.TList a)) b)
               (x :: M.Term g a) (x' :: M.Term g a)
               (xs :: M.Term g (M.TList a)) (xs' :: M.Term g (M.TList a)).
          SimRel c c' -> SimRel x x' -> SimRel xs xs'
       -> SimRel (M.substDouble c x xs) (M.substDouble c' x' xs'))
    -> SubstCompat

{-# LINE 465 "content/part2/Bisimulation.md" #-}
-- | Complete forward lock-step simulation across all 27 rules of `More.Step`.
sim :: SubstCompat -> SimRel m m' -> M.Step m n -> Leg M.Step m' n
sim sc@(MkSubstCompat sc1 sc2) rel st = case st of
  M.XiApp1 stL -> case rel of
    SimApp sl sm -> case sim sc sl stL of
      MkLeg stL' sl' -> MkLeg (M.XiApp1 stL') (SimApp sl' sm)
  M.XiApp2 vl stM -> case rel of
    SimApp sl sm -> case sim sc sm stM of
      MkLeg stM' sm' -> MkLeg (M.XiApp2 (simValue sl vl) stM') (SimApp sl sm')
  M.BetaLam vm -> case rel of
    SimApp (SimLam sn) sm -> MkLeg (M.BetaLam (simValue sm vm)) (sc1 sn sm)

  M.XiSuc stM -> case rel of
    SimSuc sm -> case sim sc sm stM of
      MkLeg stM' sm' -> MkLeg (M.XiSuc stM') (SimSuc sm')
  M.XiCaseNat stN -> case rel of
    SimCaseNat sn sz ss -> case sim sc sn stN of
      MkLeg stN' sn' -> MkLeg (M.XiCaseNat stN') (SimCaseNat sn' sz ss)
  M.BetaZero -> case rel of
    SimCaseNat SimZero sz _ -> MkLeg M.BetaZero sz
  M.BetaSuc vv -> case rel of
    SimCaseNat (SimSuc sv) _ ss -> MkLeg (M.BetaSuc (simValue sv vv)) (sc1 ss sv)
  M.BetaMu -> case rel of
    SimMu sn -> MkLeg M.BetaMu (sc1 sn (SimMu sn))

  M.XiLet stM -> case rel of
    SimLet sm sn -> case sim sc sm stM of
      MkLeg stM' sm' -> MkLeg (M.XiLet stM') (SimLet sm' sn)
    SimLetApp sm sn -> case sim sc sm stM of
      MkLeg stM' sm' -> MkLeg (M.XiApp2 M.VLam stM') (SimLetApp sm' sn)
  M.BetaLet vm -> case rel of
    SimLet sm sn    -> MkLeg (M.BetaLet (simValue sm vm)) (sc1 sn sm)
    SimLetApp sm sn -> MkLeg (M.BetaLam (simValue sm vm)) (sc1 sn sm)

  M.XiPair1 stL -> case rel of
    SimPair sl sr -> case sim sc sl stL of
      MkLeg stL' sl' -> MkLeg (M.XiPair1 stL') (SimPair sl' sr)
  M.XiPair2 vl stR -> case rel of
    SimPair sl sr -> case sim sc sr stR of
      MkLeg stR' sr' -> MkLeg (M.XiPair2 (simValue sl vl) stR') (SimPair sl sr')
  M.XiFst stP -> case rel of
    SimFst sp -> case sim sc sp stP of
      MkLeg stP' sp' -> MkLeg (M.XiFst stP') (SimFst sp')
  M.XiSnd stP -> case rel of
    SimSnd sp -> case sim sc sp stP of
      MkLeg stP' sp' -> MkLeg (M.XiSnd stP') (SimSnd sp')
  M.BetaFst vl vr -> case rel of
    SimFst (SimPair sl sr) -> MkLeg (M.BetaFst (simValue sl vl) (simValue sr vr)) sl
  M.BetaSnd vl vr -> case rel of
    SimSnd (SimPair sl sr) -> MkLeg (M.BetaSnd (simValue sl vl) (simValue sr vr)) sr

  M.XiInl stX -> case rel of
    SimInl sx -> case sim sc sx stX of
      MkLeg stX' sx' -> MkLeg (M.XiInl stX') (SimInl sx')
  M.XiInr stY -> case rel of
    SimInr sy -> case sim sc sy stY of
      MkLeg stY' sy' -> MkLeg (M.XiInr stY') (SimInr sy')
  M.XiCaseSum stS -> case rel of
    SimCaseSum ss sl sr -> case sim sc ss stS of
      MkLeg stS' ss' -> MkLeg (M.XiCaseSum stS') (SimCaseSum ss' sl sr)
  M.BetaInl vx -> case rel of
    SimCaseSum (SimInl sx) sl _ -> MkLeg (M.BetaInl (simValue sx vx)) (sc1 sl sx)
  M.BetaInr vy -> case rel of
    SimCaseSum (SimInr sy) _ sr -> MkLeg (M.BetaInr (simValue sy vy)) (sc1 sr sy)
  M.XiAbsurd stM -> case rel of
    SimAbsurd sm -> case sim sc sm stM of
      MkLeg stM' sm' -> MkLeg (M.XiAbsurd stM') (SimAbsurd sm')

  M.XiCons1 stX -> case rel of
    SimCons sx sxs -> case sim sc sx stX of
      MkLeg stX' sx' -> MkLeg (M.XiCons1 stX') (SimCons sx' sxs)
  M.XiCons2 vx stXs -> case rel of
    SimCons sx sxs -> case sim sc sxs stXs of
      MkLeg stXs' sxs' -> MkLeg (M.XiCons2 (simValue sx vx) stXs') (SimCons sx sxs')
  M.XiCaseLst stS -> case rel of
    SimCaseLst ss sn scons -> case sim sc ss stS of
      MkLeg stS' ss' -> MkLeg (M.XiCaseLst stS') (SimCaseLst ss' sn scons)
  M.BetaNil -> case rel of
    SimCaseLst SimNil sn _ -> MkLeg M.BetaNil sn
  M.BetaCons vx vxs -> case rel of
    SimCaseLst (SimCons sx sxs) _ scons ->
      MkLeg (M.BetaCons (simValue sx vx) (simValue sxs vxs)) (sc2 scons sx sxs)

-- | Complete backward lock-step simulation (`sim⁻¹`) across all 27 rules!
simInv :: SubstCompat -> SimRel m m' -> M.Step m' n' -> LegInv M.Step m n'
simInv sc@(MkSubstCompat sc1 sc2) rel st = case st of
  M.XiApp1 stL' -> case rel of
    SimApp sl sm -> case simInv sc sl stL' of
      MkLegInv stL sl' -> MkLegInv (M.XiApp1 stL) (SimApp sl' sm)
    SimLetApp _ _ -> absurd (valNoStep M.VLam stL')
  M.XiApp2 vl' stM' -> case rel of
    SimApp sl sm -> case simInv sc sm stM' of
      MkLegInv stM sm' -> MkLegInv (M.XiApp2 (simValueInv sl vl') stM) (SimApp sl sm')
    SimLetApp sm sn -> case simInv sc sm stM' of
      MkLegInv stM sm' -> MkLegInv (M.XiLet stM) (SimLetApp sm' sn)
  M.BetaLam vm' -> case rel of
    SimApp (SimLam sn) sm -> MkLegInv (M.BetaLam (simValueInv sm vm')) (sc1 sn sm)
    SimLetApp sm sn       -> MkLegInv (M.BetaLet (simValueInv sm vm')) (sc1 sn sm)

  M.XiSuc stM' -> case rel of
    SimSuc sm -> case simInv sc sm stM' of
      MkLegInv stM sm' -> MkLegInv (M.XiSuc stM) (SimSuc sm')
  M.XiCaseNat stN' -> case rel of
    SimCaseNat sn sz ss -> case simInv sc sn stN' of
      MkLegInv stN sn' -> MkLegInv (M.XiCaseNat stN) (SimCaseNat sn' sz ss)
  M.BetaZero -> case rel of
    SimCaseNat SimZero sz _ -> MkLegInv M.BetaZero sz
  M.BetaSuc vv' -> case rel of
    SimCaseNat (SimSuc sv) _ ss -> MkLegInv (M.BetaSuc (simValueInv sv vv')) (sc1 ss sv)
  M.BetaMu -> case rel of
    SimMu sn -> MkLegInv M.BetaMu (sc1 sn (SimMu sn))

  M.XiLet stM' -> case rel of
    SimLet sm sn -> case simInv sc sm stM' of
      MkLegInv stM sm' -> MkLegInv (M.XiLet stM) (SimLet sm' sn)
  M.BetaLet vm' -> case rel of
    SimLet sm sn -> MkLegInv (M.BetaLet (simValueInv sm vm')) (sc1 sn sm)

  M.XiPair1 stL' -> case rel of
    SimPair sl sr -> case simInv sc sl stL' of
      MkLegInv stL sl' -> MkLegInv (M.XiPair1 stL) (SimPair sl' sr)
  M.XiPair2 vl' stR' -> case rel of
    SimPair sl sr -> case simInv sc sr stR' of
      MkLegInv stR sr' -> MkLegInv (M.XiPair2 (simValueInv sl vl') stR) (SimPair sl sr')
  M.XiFst stP' -> case rel of
    SimFst sp -> case simInv sc sp stP' of
      MkLegInv stP sp' -> MkLegInv (M.XiFst stP) (SimFst sp')
  M.XiSnd stP' -> case rel of
    SimSnd sp -> case simInv sc sp stP' of
      MkLegInv stP sp' -> MkLegInv (M.XiSnd stP) (SimSnd sp')
  M.BetaFst vl' vr' -> case rel of
    SimFst (SimPair sl sr) -> MkLegInv (M.BetaFst (simValueInv sl vl') (simValueInv sr vr')) sl
  M.BetaSnd vl' vr' -> case rel of
    SimSnd (SimPair sl sr) -> MkLegInv (M.BetaSnd (simValueInv sl vl') (simValueInv sr vr')) sr

  M.XiInl stX' -> case rel of
    SimInl sx -> case simInv sc sx stX' of
      MkLegInv stX sx' -> MkLegInv (M.XiInl stX) (SimInl sx')
  M.XiInr stY' -> case rel of
    SimInr sy -> case simInv sc sy stY' of
      MkLegInv stY sy' -> MkLegInv (M.XiInr stY) (SimInr sy')
  M.XiCaseSum stS' -> case rel of
    SimCaseSum ss sl sr -> case simInv sc ss stS' of
      MkLegInv stS ss' -> MkLegInv (M.XiCaseSum stS) (SimCaseSum ss' sl sr)
  M.BetaInl vx' -> case rel of
    SimCaseSum (SimInl sx) sl _ -> MkLegInv (M.BetaInl (simValueInv sx vx')) (sc1 sl sx)
  M.BetaInr vy' -> case rel of
    SimCaseSum (SimInr sy) _ sr -> MkLegInv (M.BetaInr (simValueInv sy vy')) (sc1 sr sy)
  M.XiAbsurd stM' -> case rel of
    SimAbsurd sm -> case simInv sc sm stM' of
      MkLegInv stM sm' -> MkLegInv (M.XiAbsurd stM) (SimAbsurd sm')

  M.XiCons1 stX' -> case rel of
    SimCons sx sxs -> case simInv sc sx stX' of
      MkLegInv stX sx' -> MkLegInv (M.XiCons1 stX) (SimCons sx' sxs)
  M.XiCons2 vx' stXs' -> case rel of
    SimCons sx sxs -> case simInv sc sxs stXs' of
      MkLegInv stXs sxs' -> MkLegInv (M.XiCons2 (simValueInv sx vx') stXs) (SimCons sx sxs')
  M.XiCaseLst stS' -> case rel of
    SimCaseLst ss sn scons -> case simInv sc ss stS' of
      MkLegInv stS ss' -> MkLegInv (M.XiCaseLst stS) (SimCaseLst ss' sn scons)
  M.BetaNil -> case rel of
    SimCaseLst SimNil sn _ -> MkLegInv M.BetaNil sn
  M.BetaCons vx' vxs' -> case rel of
    SimCaseLst (SimCons sx sxs) _ scons ->
      MkLegInv (M.BetaCons (simValueInv sx vx') (simValueInv sxs vxs')) (sc2 scons sx sxs)

{-# LINE 640 "content/part2/Bisimulation.md" #-}
-- | Multi-step forward simulation (`—↠`).
simSteps :: SubstCompat -> SimRel m m' -> M.Steps m n -> Leg M.Steps m' n
simSteps _  rel M.StepsRefl        = MkLeg M.StepsRefl rel
simSteps sc rel (M.StepsCons s ss) = case sim sc rel s of
  MkLeg s' rel1 -> case simSteps sc rel1 ss of
    MkLeg ss' rel2 -> MkLeg (M.StepsCons s' ss') rel2

-- | Multi-step backward simulation (`—↠`).
simStepsInv :: SubstCompat -> SimRel m m' -> M.Steps m' n' -> LegInv M.Steps m n'
simStepsInv _  rel M.StepsRefl        = MkLegInv M.StepsRefl rel
simStepsInv sc rel (M.StepsCons s ss) = case simInv sc rel s of
  MkLegInv s' rel1 -> case simStepsInv sc rel1 ss of
    MkLegInv ss' rel2 -> MkLegInv (M.StepsCons s' ss') rel2

-- | Concrete closed lock-step bisimulation witnesses (zero assumptions!):
-- `let x = fst (0, 1) in suc x` simulates `(λx. suc x) (fst (0, 1))`
-- through both `XiLet` ↔ `XiApp2 VLam` and `BetaLet` ↔ `BetaLam`!
letDesugarSim
  :: SimRel @M.CEmpty @M.TNat
            (M.Let (M.Fst (M.Pair M.Zero (M.Suc M.Zero))) (M.Suc (M.Var M.Z)))
            (M.App (M.Lam (M.Suc (M.Var M.Z))) (M.Fst (M.Pair M.Zero (M.Suc M.Zero))))
letDesugarSim = SimLetApp (SimFst (SimPair SimZero (SimSuc SimZero))) (SimSuc SimVar)

letDesugarSteps
  :: Leg @M.CEmpty @M.TNat M.Steps
         (M.App (M.Lam (M.Suc (M.Var M.Z))) (M.Fst (M.Pair M.Zero (M.Suc M.Zero))))
         (M.Suc M.Zero)
letDesugarSteps =
  MkLeg
    (M.StepsCons (M.XiApp2 M.VLam (M.BetaFst M.VZero (M.VSuc M.VZero)))
      (M.StepsCons (M.BetaLam M.VZero) M.StepsRefl))
    (SimSuc SimZero)

letDesugarStepsInv
  :: LegInv @M.CEmpty @M.TNat M.Steps
            (M.Let (M.Fst (M.Pair M.Zero (M.Suc M.Zero))) (M.Suc (M.Var M.Z)))
            (M.Suc M.Zero)
letDesugarStepsInv =
  MkLegInv
    (M.StepsCons (M.XiLet (M.BetaFst M.VZero (M.VSuc M.VZero)))
      (M.StepsCons (M.BetaLet M.VZero) M.StepsRefl))
    (SimSuc SimZero)
