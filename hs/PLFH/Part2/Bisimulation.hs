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
  , RenCompat
  , extRenCompat
  , simRename
  , simWeaken
  , SubstFn
  , Compatible
  , simExt
  , simSubst
  , simSubstSingle
  , simSubstDouble
  , Leg (..)
  , LegInv (..)
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
import qualified PLFH.Part2.More as M

{-# LINE 102 "content/part2/Bisimulation.md" #-}
-- | Structural bisimulation relation relating `let x = m in n` to `(λx. n') m'`
-- across all 19 constructors of `PLFH.Part2.More.Term`.
type SimRel :: forall (g :: M.Ctx) (a :: M.Ty). M.Term g a -> M.Term g a -> Type
data SimRel m m' where
  SimVar     :: foreach (x :: M.Lookup g a) -> SimRel (M.Var x) (M.Var x)
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

{-# LINE 138 "content/part2/Bisimulation.md" #-}
-- | Reflexivity (`~-refl`): every extended STLC term is related to itself.
simRefl :: forall (g :: M.Ctx) (a :: M.Ty). foreach (m :: M.Term g a) -> SimRel m m
simRefl (M.Var x)         = SimVar x
simRefl (M.Lam n)         = SimLam (simRefl n)
simRefl (M.App l m)       = SimApp (simRefl l) (simRefl m)
simRefl M.Zero            = SimZero
simRefl (M.Suc n)         = SimSuc (simRefl n)
simRefl (M.CaseNat n z s) = SimCaseNat (simRefl n) (simRefl z) (simRefl s)
simRefl (M.Mu n)          = SimMu (simRefl n)
simRefl (M.Let m n)       = SimLet (simRefl m) (simRefl n)
simRefl M.TT              = SimTT
simRefl (M.Pair l r)      = SimPair (simRefl l) (simRefl r)
simRefl (M.Fst p)         = SimFst (simRefl p)
simRefl (M.Snd p)         = SimSnd (simRefl p)
simRefl (M.Inl x)         = SimInl (simRefl x)
simRefl (M.Inr y)         = SimInr (simRefl y)
simRefl (M.CaseSum s l r) = SimCaseSum (simRefl s) (simRefl l) (simRefl r)
simRefl (M.Absurd m)      = SimAbsurd (simRefl m)
simRefl M.Nil             = SimNil
simRefl (M.Cons x xs)     = SimCons (simRefl x) (simRefl xs)
simRefl (M.CaseLst s n c) = SimCaseLst (simRefl s) (simRefl n) (simRefl c)

-- | Transitivity of `SimRel`: `l ~ m` and `m ~ n` implies `l ~ n`.
simTrans :: SimRel l m -> SimRel m n -> SimRel l n
simTrans (SimVar x)             (SimVar _)              = SimVar x
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

{-# LINE 194 "content/part2/Bisimulation.md" #-}
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

{-# LINE 245 "content/part2/Bisimulation.md" #-}
-- | A sort-preserving map between lookup contexts.
type Renaming g d = forall x. M.Lookup g x -> M.Lookup d x

-- | Runtime witness that renaming `r` preserves variable lookups inside `SimVar`.
type RenCompat :: forall g d. Renaming g d -> Type
type RenCompat @g @d r = forall a. foreach (x :: M.Lookup g a) -> SimRel (M.Var (r x)) (M.Var (r x))

-- | Lifting a renaming witness under one binder (`M.ext r`).
extRenCompat :: forall g d b (r :: Renaming g d).
                RenCompat @g @d r
             -> RenCompat @(M.CExt g b) @(M.CExt d b) (M.ext r)
extRenCompat rc x = case x of
  M.Z    -> SimVar (M.Z :: M.Lookup (M.CExt d b) b)
  M.S x' -> case rc x' of
    SimVar y -> SimVar (M.S y)

-- | Renaming preserves the structural simulation relation across all 20 constructors!
simRename :: forall g d a (r :: Renaming g d) (m :: M.Term g a) (n :: M.Term g a).
             RenCompat @g @d r
          -> SimRel m n -> SimRel (M.rename r m) (M.rename r n)
simRename rc (SimVar x)           = rc x
simRename rc (SimLam s)           = SimLam (simRename (extRenCompat rc) s)
simRename rc (SimApp l m)         = SimApp (simRename rc l) (simRename rc m)
simRename _  SimZero              = SimZero
simRename rc (SimSuc s)           = SimSuc (simRename rc s)
simRename rc (SimCaseNat n z s)   = SimCaseNat (simRename rc n) (simRename rc z) (simRename (extRenCompat rc) s)
simRename rc (SimMu s)            = SimMu (simRename (extRenCompat rc) s)
simRename rc (SimLet m n)         = SimLet (simRename rc m) (simRename (extRenCompat rc) n)
simRename rc (SimLetApp m n)      = SimLetApp (simRename rc m) (simRename (extRenCompat rc) n)
simRename _  SimTT                = SimTT
simRename rc (SimPair l r')       = SimPair (simRename rc l) (simRename rc r')
simRename rc (SimFst p)           = SimFst (simRename rc p)
simRename rc (SimSnd p)           = SimSnd (simRename rc p)
simRename rc (SimInl s)           = SimInl (simRename rc s)
simRename rc (SimInr s)           = SimInr (simRename rc s)
simRename rc (SimCaseSum s l r')  = SimCaseSum (simRename rc s) (simRename (extRenCompat rc) l) (simRename (extRenCompat rc) r')
simRename rc (SimAbsurd s)        = SimAbsurd (simRename rc s)
simRename _  SimNil               = SimNil
simRename rc (SimCons x xs)       = SimCons (simRename rc x) (simRename rc xs)
simRename rc (SimCaseLst xs n c)  = SimCaseLst (simRename rc xs) (simRename rc n) (simRename (extRenCompat (extRenCompat rc)) c)

-- | Shifting an extended term into an extended context (`M.weakenLookup`) preserves `SimRel`.
weakenRenCompat :: forall d b. RenCompat @d @(M.CExt d b) (M.weakenLookup @d @b)
weakenRenCompat x = SimVar (M.S x)

simWeaken :: forall d b a (m :: M.Term d a) (n :: M.Term d a).
             SimRel m n -> SimRel (M.rename (M.weakenLookup @d @b) m) (M.rename (M.weakenLookup @d @b) n)
simWeaken = simRename (weakenRenCompat @d @b)

{-# LINE 308 "content/part2/Bisimulation.md" #-}
-- | A sort-preserving simultaneous substitution callback between contexts.
type SubstFn g d = forall a. M.Lookup g a -> M.Term d a

-- | Pointwise simulation compatibility between two simultaneous substitutions.
type Compatible :: forall g d. SubstFn g d -> SubstFn g d -> Type
type Compatible @g @d p q = forall a. foreach (x :: M.Lookup g a) -> SimRel (p x) (q x)

-- | Extending two compatible substitutions under a binder preserves compatibility (`~-exts`).
simExt :: forall g d b (p :: SubstFn g d) (q :: SubstFn g d).
          Compatible @g @d p q
       -> Compatible @(M.CExt g b) @(M.CExt d b) (M.exts @g @d @b p) (M.exts @g @d @b q)
simExt step x = case x of
  M.Z    -> SimVar (M.Z :: M.Lookup (M.CExt d b) b)
  M.S x' -> simWeaken @d @b (step x')

-- | Simultaneous substitution preserves `SimRel` across all 20 constructors (`~-subst`)!
simSubst :: forall g d a (p :: SubstFn g d) (q :: SubstFn g d) (m :: M.Term g a) (n :: M.Term g a).
            Compatible @g @d p q
         -> SimRel m n
         -> SimRel (M.subst p m) (M.subst q n)
simSubst step (SimVar x)          = step x
simSubst step (SimLam p0)         = SimLam (simSubst (simExt step) p0)
simSubst step (SimApp p0 p1)      = SimApp (simSubst step p0) (simSubst step p1)
simSubst _    SimZero             = SimZero
simSubst step (SimSuc p0)         = SimSuc (simSubst step p0)
simSubst step (SimCaseNat p0 p1 p2) =
  SimCaseNat (simSubst step p0) (simSubst step p1) (simSubst (simExt step) p2)
simSubst step (SimMu p0)          = SimMu (simSubst (simExt step) p0)
simSubst step (SimLet p0 p1)      = SimLet (simSubst step p0) (simSubst (simExt step) p1)
simSubst step (SimLetApp p0 p1)   = SimLetApp (simSubst step p0) (simSubst (simExt step) p1)
simSubst _    SimTT               = SimTT
simSubst step (SimPair p0 p1)     = SimPair (simSubst step p0) (simSubst step p1)
simSubst step (SimFst p0)         = SimFst (simSubst step p0)
simSubst step (SimSnd p0)         = SimSnd (simSubst step p0)
simSubst step (SimInl p0)         = SimInl (simSubst step p0)
simSubst step (SimInr p0)         = SimInr (simSubst step p0)
simSubst step (SimCaseSum p0 p1 p2) =
  SimCaseSum (simSubst step p0) (simSubst (simExt step) p1) (simSubst (simExt step) p2)
simSubst step (SimAbsurd p0)      = SimAbsurd (simSubst step p0)
simSubst _    SimNil              = SimNil
simSubst step (SimCons p0 p1)     = SimCons (simSubst step p0) (simSubst step p1)
simSubst step (SimCaseLst p0 p1 p2) =
  SimCaseLst (simSubst step p0) (simSubst step p1) (simSubst (simExt (simExt step)) p2)

singleCompat :: forall g a (v :: M.Term g a) (v' :: M.Term g a).
                SimRel v v'
             -> Compatible @(M.CExt g a) @g (M.singleSubst v) (M.singleSubst v')
singleCompat sv x = case x of
  M.Z    -> sv
  M.S x' -> SimVar x'

-- | Single-variable substitution preserves `SimRel`.
simSubstSingle :: forall g a b (n :: M.Term (M.CExt g a) b) (n' :: M.Term (M.CExt g a) b)
                               (v :: M.Term g a) (v' :: M.Term g a).
                  SimRel n n' -> SimRel v v'
               -> SimRel (M.substSingle n v) (M.substSingle n' v')
simSubstSingle sn sv = simSubst (singleCompat sv) sn

doubleCompat :: forall g a b (v :: M.Term g a) (v' :: M.Term g a)
                             (w :: M.Term g b) (w' :: M.Term g b).
                SimRel v v' -> SimRel w w'
             -> Compatible @(M.CExt (M.CExt g a) b) @g (M.doubleSubst v w) (M.doubleSubst v' w')
doubleCompat sv sw x = case x of
  M.Z         -> sw
  M.S M.Z     -> sv
  M.S (M.S y) -> SimVar y

-- | Double-variable substitution preserves `SimRel`.
simSubstDouble :: forall g a b c (n :: M.Term (M.CExt (M.CExt g a) b) c)
                                 (n' :: M.Term (M.CExt (M.CExt g a) b) c)
                                 (v :: M.Term g a) (v' :: M.Term g a)
                                 (w :: M.Term g b) (w' :: M.Term g b).
                  SimRel n n' -> SimRel v v' -> SimRel w w'
               -> SimRel (M.substDouble n v w) (M.substDouble n' v' w')
simSubstDouble sn sv sw = simSubst (doubleCompat sv sw) sn

{-# LINE 400 "content/part2/Bisimulation.md" #-}
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

{-# LINE 434 "content/part2/Bisimulation.md" #-}
-- | Forward lock-step simulation across all 27 rules of `More.Step`.
sim :: SimRel m m' -> M.Step m n -> Leg M.Step m' n
sim rel st = case st of
  M.XiApp1 stL -> case rel of
    SimApp sl sm -> case sim sl stL of
      MkLeg stL' sl' -> MkLeg (M.XiApp1 stL') (SimApp sl' sm)
  M.XiApp2 vl stM -> case rel of
    SimApp sl sm -> case sim sm stM of
      MkLeg stM' sm' -> MkLeg (M.XiApp2 (simValue sl vl) stM') (SimApp sl sm')
  M.BetaLam vm -> case rel of
    SimApp (SimLam sn) sm -> MkLeg (M.BetaLam (simValue sm vm)) (simSubstSingle sn sm)

  M.XiSuc stM -> case rel of
    SimSuc sm -> case sim sm stM of
      MkLeg stM' sm' -> MkLeg (M.XiSuc stM') (SimSuc sm')
  M.XiCaseNat stN -> case rel of
    SimCaseNat sn sz ss -> case sim sn stN of
      MkLeg stN' sn' -> MkLeg (M.XiCaseNat stN') (SimCaseNat sn' sz ss)
  M.BetaZero -> case rel of
    SimCaseNat SimZero sz _ -> MkLeg M.BetaZero sz
  M.BetaSuc vv -> case rel of
    SimCaseNat (SimSuc sv) _ ss -> MkLeg (M.BetaSuc (simValue sv vv)) (simSubstSingle ss sv)
  M.BetaMu -> case rel of
    SimMu sn -> MkLeg M.BetaMu (simSubstSingle sn (SimMu sn))

  M.XiLet stM -> case rel of
    SimLet sm sn -> case sim sm stM of
      MkLeg stM' sm' -> MkLeg (M.XiLet stM') (SimLet sm' sn)
    SimLetApp sm sn -> case sim sm stM of
      MkLeg stM' sm' -> MkLeg (M.XiApp2 M.VLam stM') (SimLetApp sm' sn)
  M.BetaLet vm -> case rel of
    SimLet sm sn    -> MkLeg (M.BetaLet (simValue sm vm)) (simSubstSingle sn sm)
    SimLetApp sm sn -> MkLeg (M.BetaLam (simValue sm vm)) (simSubstSingle sn sm)

  M.XiPair1 stL -> case rel of
    SimPair sl sr -> case sim sl stL of
      MkLeg stL' sl' -> MkLeg (M.XiPair1 stL') (SimPair sl' sr)
  M.XiPair2 vl stR -> case rel of
    SimPair sl sr -> case sim sr stR of
      MkLeg stR' sr' -> MkLeg (M.XiPair2 (simValue sl vl) stR') (SimPair sl sr')
  M.XiFst stP -> case rel of
    SimFst sp -> case sim sp stP of
      MkLeg stP' sp' -> MkLeg (M.XiFst stP') (SimFst sp')
  M.XiSnd stP -> case rel of
    SimSnd sp -> case sim sp stP of
      MkLeg stP' sp' -> MkLeg (M.XiSnd stP') (SimSnd sp')
  M.BetaFst vl vr -> case rel of
    SimFst (SimPair sl sr) -> MkLeg (M.BetaFst (simValue sl vl) (simValue sr vr)) sl
  M.BetaSnd vl vr -> case rel of
    SimSnd (SimPair sl sr) -> MkLeg (M.BetaSnd (simValue sl vl) (simValue sr vr)) sr

  M.XiInl stX -> case rel of
    SimInl sx -> case sim sx stX of
      MkLeg stX' sx' -> MkLeg (M.XiInl stX') (SimInl sx')
  M.XiInr stY -> case rel of
    SimInr sy -> case sim sy stY of
      MkLeg stY' sy' -> MkLeg (M.XiInr stY') (SimInr sy')
  M.XiCaseSum stS -> case rel of
    SimCaseSum ss sl sr -> case sim ss stS of
      MkLeg stS' ss' -> MkLeg (M.XiCaseSum stS') (SimCaseSum ss' sl sr)
  M.BetaInl vx -> case rel of
    SimCaseSum (SimInl sx) sl _ -> MkLeg (M.BetaInl (simValue sx vx)) (simSubstSingle sl sx)
  M.BetaInr vy -> case rel of
    SimCaseSum (SimInr sy) _ sr -> MkLeg (M.BetaInr (simValue sy vy)) (simSubstSingle sr sy)
  M.XiAbsurd stM -> case rel of
    SimAbsurd sm -> case sim sm stM of
      MkLeg stM' sm' -> MkLeg (M.XiAbsurd stM') (SimAbsurd sm')

  M.XiCons1 stX -> case rel of
    SimCons sx sxs -> case sim sx stX of
      MkLeg stX' sx' -> MkLeg (M.XiCons1 stX') (SimCons sx' sxs)
  M.XiCons2 vx stXs -> case rel of
    SimCons sx sxs -> case sim sxs stXs of
      MkLeg stXs' sxs' -> MkLeg (M.XiCons2 (simValue sx vx) stXs') (SimCons sx sxs')
  M.XiCaseLst stS -> case rel of
    SimCaseLst ss sn scons -> case sim ss stS of
      MkLeg stS' ss' -> MkLeg (M.XiCaseLst stS') (SimCaseLst ss' sn scons)
  M.BetaNil -> case rel of
    SimCaseLst SimNil sn _ -> MkLeg M.BetaNil sn
  M.BetaCons vx vxs -> case rel of
    SimCaseLst (SimCons sx sxs) _ scons ->
      MkLeg (M.BetaCons (simValue sx vx) (simValue sxs vxs)) (simSubstDouble scons sx sxs)

-- | Backward lock-step simulation (`sim⁻¹`) across all 27 rules.
simInv :: SimRel m m' -> M.Step m' n' -> LegInv M.Step m n'
simInv rel st = case st of
  M.XiApp1 stL' -> case rel of
    SimApp sl sm -> case simInv sl stL' of
      MkLegInv stL sl' -> MkLegInv (M.XiApp1 stL) (SimApp sl' sm)
    SimLetApp _ _ -> absurd (valNoStep M.VLam stL')
  M.XiApp2 vl' stM' -> case rel of
    SimApp sl sm -> case simInv sm stM' of
      MkLegInv stM sm' -> MkLegInv (M.XiApp2 (simValueInv sl vl') stM) (SimApp sl sm')
    SimLetApp sm sn -> case simInv sm stM' of
      MkLegInv stM sm' -> MkLegInv (M.XiLet stM) (SimLetApp sm' sn)
  M.BetaLam vm' -> case rel of
    SimApp (SimLam sn) sm -> MkLegInv (M.BetaLam (simValueInv sm vm')) (simSubstSingle sn sm)
    SimLetApp sm sn       -> MkLegInv (M.BetaLet (simValueInv sm vm')) (simSubstSingle sn sm)

  M.XiSuc stM' -> case rel of
    SimSuc sm -> case simInv sm stM' of
      MkLegInv stM sm' -> MkLegInv (M.XiSuc stM) (SimSuc sm')
  M.XiCaseNat stN' -> case rel of
    SimCaseNat sn sz ss -> case simInv sn stN' of
      MkLegInv stN sn' -> MkLegInv (M.XiCaseNat stN) (SimCaseNat sn' sz ss)
  M.BetaZero -> case rel of
    SimCaseNat SimZero sz _ -> MkLegInv M.BetaZero sz
  M.BetaSuc vv' -> case rel of
    SimCaseNat (SimSuc sv) _ ss -> MkLegInv (M.BetaSuc (simValueInv sv vv')) (simSubstSingle ss sv)
  M.BetaMu -> case rel of
    SimMu sn -> MkLegInv M.BetaMu (simSubstSingle sn (SimMu sn))

  M.XiLet stM' -> case rel of
    SimLet sm sn -> case simInv sm stM' of
      MkLegInv stM sm' -> MkLegInv (M.XiLet stM) (SimLet sm' sn)
  M.BetaLet vm' -> case rel of
    SimLet sm sn -> MkLegInv (M.BetaLet (simValueInv sm vm')) (simSubstSingle sn sm)

  M.XiPair1 stL' -> case rel of
    SimPair sl sr -> case simInv sl stL' of
      MkLegInv stL sl' -> MkLegInv (M.XiPair1 stL) (SimPair sl' sr)
  M.XiPair2 vl' stR' -> case rel of
    SimPair sl sr -> case simInv sr stR' of
      MkLegInv stR sr' -> MkLegInv (M.XiPair2 (simValueInv sl vl') stR) (SimPair sl sr')
  M.XiFst stP' -> case rel of
    SimFst sp -> case simInv sp stP' of
      MkLegInv stP sp' -> MkLegInv (M.XiFst stP) (SimFst sp')
  M.XiSnd stP' -> case rel of
    SimSnd sp -> case simInv sp stP' of
      MkLegInv stP sp' -> MkLegInv (M.XiSnd stP) (SimSnd sp')
  M.BetaFst vl' vr' -> case rel of
    SimFst (SimPair sl sr) -> MkLegInv (M.BetaFst (simValueInv sl vl') (simValueInv sr vr')) sl
  M.BetaSnd vl' vr' -> case rel of
    SimSnd (SimPair sl sr) -> MkLegInv (M.BetaSnd (simValueInv sl vl') (simValueInv sr vr')) sr

  M.XiInl stX' -> case rel of
    SimInl sx -> case simInv sx stX' of
      MkLegInv stX sx' -> MkLegInv (M.XiInl stX) (SimInl sx')
  M.XiInr stY' -> case rel of
    SimInr sy -> case simInv sy stY' of
      MkLegInv stY sy' -> MkLegInv (M.XiInr stY) (SimInr sy')
  M.XiCaseSum stS' -> case rel of
    SimCaseSum ss sl sr -> case simInv ss stS' of
      MkLegInv stS ss' -> MkLegInv (M.XiCaseSum stS) (SimCaseSum ss' sl sr)
  M.BetaInl vx' -> case rel of
    SimCaseSum (SimInl sx) sl _ -> MkLegInv (M.BetaInl (simValueInv sx vx')) (simSubstSingle sl sx)
  M.BetaInr vy' -> case rel of
    SimCaseSum (SimInr sy) _ sr -> MkLegInv (M.BetaInr (simValueInv sy vy')) (simSubstSingle sr sy)
  M.XiAbsurd stM' -> case rel of
    SimAbsurd sm -> case simInv sm stM' of
      MkLegInv stM sm' -> MkLegInv (M.XiAbsurd stM) (SimAbsurd sm')

  M.XiCons1 stX' -> case rel of
    SimCons sx sxs -> case simInv sx stX' of
      MkLegInv stX sx' -> MkLegInv (M.XiCons1 stX) (SimCons sx' sxs)
  M.XiCons2 vx' stXs' -> case rel of
    SimCons sx sxs -> case simInv sxs stXs' of
      MkLegInv stXs sxs' -> MkLegInv (M.XiCons2 (simValueInv sx vx') stXs) (SimCons sx sxs')
  M.XiCaseLst stS' -> case rel of
    SimCaseLst ss sn scons -> case simInv ss stS' of
      MkLegInv stS ss' -> MkLegInv (M.XiCaseLst stS) (SimCaseLst ss' sn scons)
  M.BetaNil -> case rel of
    SimCaseLst SimNil sn _ -> MkLegInv M.BetaNil sn
  M.BetaCons vx' vxs' -> case rel of
    SimCaseLst (SimCons sx sxs) _ scons ->
      MkLegInv (M.BetaCons (simValueInv sx vx') (simValueInv sxs vxs')) (simSubstDouble scons sx sxs)

{-# LINE 609 "content/part2/Bisimulation.md" #-}
-- | Multi-step forward simulation (`—↠`).
simSteps :: SimRel m m' -> M.Steps m n -> Leg M.Steps m' n
simSteps rel M.StepsRefl        = MkLeg M.StepsRefl rel
simSteps rel (M.StepsCons s ss) = case sim rel s of
  MkLeg s' rel1 -> case simSteps rel1 ss of
    MkLeg ss' rel2 -> MkLeg (M.StepsCons s' ss') rel2

-- | Multi-step backward simulation (`—↠`).
simStepsInv :: SimRel m m' -> M.Steps m' n' -> LegInv M.Steps m n'
simStepsInv rel M.StepsRefl        = MkLegInv M.StepsRefl rel
simStepsInv rel (M.StepsCons s ss) = case simInv rel s of
  MkLegInv s' rel1 -> case simStepsInv rel1 ss of
    MkLegInv ss' rel2 -> MkLegInv (M.StepsCons s' ss') rel2

-- | Concrete closed lock-step bisimulation witnesses (computed by `simSteps` / `simStepsInv`!):
-- `let x = fst (0, 1) in suc x` simulates `(λx. suc x) (fst (0, 1))`
-- through both `XiLet` ↔ `XiApp2 VLam` and `BetaLet` ↔ `BetaLam`!
letDesugarSim
  :: SimRel @M.CEmpty @M.TNat
            (M.Let (M.Fst (M.Pair M.Zero (M.Suc M.Zero))) (M.Suc (M.Var M.Z)))
            (M.App (M.Lam (M.Suc (M.Var M.Z))) (M.Fst (M.Pair M.Zero (M.Suc M.Zero))))
letDesugarSim =
  SimLetApp (SimFst (SimPair SimZero (SimSuc SimZero)))
            (SimSuc (SimVar (M.Z :: M.Lookup (M.CExt M.CEmpty M.TNat) M.TNat)))

letDesugarSteps
  :: Leg @M.CEmpty @M.TNat M.Steps
         (M.App (M.Lam (M.Suc (M.Var M.Z))) (M.Fst (M.Pair M.Zero (M.Suc M.Zero))))
         (M.Suc M.Zero)
letDesugarSteps =
  simSteps letDesugarSim
    (M.StepsCons (M.XiLet (M.BetaFst M.VZero (M.VSuc M.VZero)))
      (M.StepsCons (M.BetaLet M.VZero) M.StepsRefl))

letDesugarStepsInv
  :: LegInv @M.CEmpty @M.TNat M.Steps
            (M.Let (M.Fst (M.Pair M.Zero (M.Suc M.Zero))) (M.Suc (M.Var M.Z)))
            (M.Suc M.Zero)
letDesugarStepsInv =
  simStepsInv letDesugarSim
    (M.StepsCons (M.XiApp2 M.VLam (M.BetaFst M.VZero (M.VSuc M.VZero)))
      (M.StepsCons (M.BetaLam M.VZero) M.StepsRefl))
