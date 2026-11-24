-- Generated from content/part2/Bisimulation.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, StandaloneKindSignatures, TypeAbstractions, TypeApplications #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
{-# LINE 54 "content/part2/Bisimulation.md" #-}
module PLFH.Part2.Bisimulation
  ( SimRel (..)
  , simRefl
  , simTrans
  , simValue
  , simValueInv
  , valNoStep
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
import qualified PLFH.Part2.More as M
import qualified PLFH.Part2.MoreProgress as MP

{-# LINE 94 "content/part2/Bisimulation.md" #-}
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

{-# LINE 130 "content/part2/Bisimulation.md" #-}
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

{-# LINE 187 "content/part2/Bisimulation.md" #-}
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
valNoStep :: M.Value m -> MP.Step m n -> Void
valNoStep val st = case val of
  M.VLam       -> case st of {}
  M.VZero      -> case st of {}
  M.VSuc v     -> case st of { MP.XiSuc s -> valNoStep v s }
  M.VTT        -> case st of {}
  M.VPair v w  -> case st of { MP.XiPair1 s -> valNoStep v s; MP.XiPair2 _ s -> valNoStep w s }
  M.VInl v     -> case st of { MP.XiInl s -> valNoStep v s }
  M.VInr v     -> case st of { MP.XiInr s -> valNoStep v s }
  M.VNil       -> case st of {}
  M.VCons v vs -> case st of { MP.XiCons1 s -> valNoStep v s; MP.XiCons2 _ s -> valNoStep vs s }

{-# LINE 242 "content/part2/Bisimulation.md" #-}
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

{-# LINE 305 "content/part2/Bisimulation.md" #-}
-- | Complete forward lock-step simulation across all 27 rules of `MoreProgress.Step`.
sim :: SubstCompat -> SimRel m m' -> MP.Step m n -> Leg MP.Step m' n
sim sc@(MkSubstCompat sc1 sc2) rel st = case st of
  MP.XiApp1 stL -> case rel of
    SimApp sl sm -> case sim sc sl stL of
      MkLeg stL' sl' -> MkLeg (MP.XiApp1 stL') (SimApp sl' sm)
  MP.XiApp2 vl stM -> case rel of
    SimApp sl sm -> case sim sc sm stM of
      MkLeg stM' sm' -> MkLeg (MP.XiApp2 (simValue sl vl) stM') (SimApp sl sm')
  MP.BetaLam vm -> case rel of
    SimApp (SimLam sn) sm -> MkLeg (MP.BetaLam (simValue sm vm)) (sc1 sn sm)

  MP.XiSuc stM -> case rel of
    SimSuc sm -> case sim sc sm stM of
      MkLeg stM' sm' -> MkLeg (MP.XiSuc stM') (SimSuc sm')
  MP.XiCaseNat stN -> case rel of
    SimCaseNat sn sz ss -> case sim sc sn stN of
      MkLeg stN' sn' -> MkLeg (MP.XiCaseNat stN') (SimCaseNat sn' sz ss)
  MP.BetaZero -> case rel of
    SimCaseNat SimZero sz _ -> MkLeg MP.BetaZero sz
  MP.BetaSuc vv -> case rel of
    SimCaseNat (SimSuc sv) _ ss -> MkLeg (MP.BetaSuc (simValue sv vv)) (sc1 ss sv)
  MP.BetaMu -> case rel of
    SimMu sn -> MkLeg MP.BetaMu (sc1 sn (SimMu sn))

  MP.XiLet stM -> case rel of
    SimLet sm sn -> case sim sc sm stM of
      MkLeg stM' sm' -> MkLeg (MP.XiLet stM') (SimLet sm' sn)
    SimLetApp sm sn -> case sim sc sm stM of
      MkLeg stM' sm' -> MkLeg (MP.XiApp2 M.VLam stM') (SimLetApp sm' sn)
  MP.BetaLet vm -> case rel of
    SimLet sm sn    -> MkLeg (MP.BetaLet (simValue sm vm)) (sc1 sn sm)
    SimLetApp sm sn -> MkLeg (MP.BetaLam (simValue sm vm)) (sc1 sn sm)

  MP.XiPair1 stL -> case rel of
    SimPair sl sr -> case sim sc sl stL of
      MkLeg stL' sl' -> MkLeg (MP.XiPair1 stL') (SimPair sl' sr)
  MP.XiPair2 vl stR -> case rel of
    SimPair sl sr -> case sim sc sr stR of
      MkLeg stR' sr' -> MkLeg (MP.XiPair2 (simValue sl vl) stR') (SimPair sl sr')
  MP.XiFst stP -> case rel of
    SimFst sp -> case sim sc sp stP of
      MkLeg stP' sp' -> MkLeg (MP.XiFst stP') (SimFst sp')
  MP.XiSnd stP -> case rel of
    SimSnd sp -> case sim sc sp stP of
      MkLeg stP' sp' -> MkLeg (MP.XiSnd stP') (SimSnd sp')
  MP.BetaFst vl vr -> case rel of
    SimFst (SimPair sl sr) -> MkLeg (MP.BetaFst (simValue sl vl) (simValue sr vr)) sl
  MP.BetaSnd vl vr -> case rel of
    SimSnd (SimPair sl sr) -> MkLeg (MP.BetaSnd (simValue sl vl) (simValue sr vr)) sr

  MP.XiInl stX -> case rel of
    SimInl sx -> case sim sc sx stX of
      MkLeg stX' sx' -> MkLeg (MP.XiInl stX') (SimInl sx')
  MP.XiInr stY -> case rel of
    SimInr sy -> case sim sc sy stY of
      MkLeg stY' sy' -> MkLeg (MP.XiInr stY') (SimInr sy')
  MP.XiCaseSum stS -> case rel of
    SimCaseSum ss sl sr -> case sim sc ss stS of
      MkLeg stS' ss' -> MkLeg (MP.XiCaseSum stS') (SimCaseSum ss' sl sr)
  MP.BetaInl vx -> case rel of
    SimCaseSum (SimInl sx) sl _ -> MkLeg (MP.BetaInl (simValue sx vx)) (sc1 sl sx)
  MP.BetaInr vy -> case rel of
    SimCaseSum (SimInr sy) _ sr -> MkLeg (MP.BetaInr (simValue sy vy)) (sc1 sr sy)
  MP.XiAbsurd stM -> case rel of
    SimAbsurd sm -> case sim sc sm stM of
      MkLeg stM' sm' -> MkLeg (MP.XiAbsurd stM') (SimAbsurd sm')

  MP.XiCons1 stX -> case rel of
    SimCons sx sxs -> case sim sc sx stX of
      MkLeg stX' sx' -> MkLeg (MP.XiCons1 stX') (SimCons sx' sxs)
  MP.XiCons2 vx stXs -> case rel of
    SimCons sx sxs -> case sim sc sxs stXs of
      MkLeg stXs' sxs' -> MkLeg (MP.XiCons2 (simValue sx vx) stXs') (SimCons sx sxs')
  MP.XiCaseLst stS -> case rel of
    SimCaseLst ss sn scons -> case sim sc ss stS of
      MkLeg stS' ss' -> MkLeg (MP.XiCaseLst stS') (SimCaseLst ss' sn scons)
  MP.BetaNil -> case rel of
    SimCaseLst SimNil sn _ -> MkLeg MP.BetaNil sn
  MP.BetaCons vx vxs -> case rel of
    SimCaseLst (SimCons sx sxs) _ scons ->
      MkLeg (MP.BetaCons (simValue sx vx) (simValue sxs vxs)) (sc2 scons sx sxs)

-- | Complete backward lock-step simulation (`sim⁻¹`) across all 27 rules!
simInv :: SubstCompat -> SimRel m m' -> MP.Step m' n' -> LegInv MP.Step m n'
simInv sc@(MkSubstCompat sc1 sc2) rel st = case st of
  MP.XiApp1 stL' -> case rel of
    SimApp sl sm -> case simInv sc sl stL' of
      MkLegInv stL sl' -> MkLegInv (MP.XiApp1 stL) (SimApp sl' sm)
    SimLetApp _ _ -> absurd (valNoStep M.VLam stL')
  MP.XiApp2 vl' stM' -> case rel of
    SimApp sl sm -> case simInv sc sm stM' of
      MkLegInv stM sm' -> MkLegInv (MP.XiApp2 (simValueInv sl vl') stM) (SimApp sl sm')
    SimLetApp sm sn -> case simInv sc sm stM' of
      MkLegInv stM sm' -> MkLegInv (MP.XiLet stM) (SimLetApp sm' sn)
  MP.BetaLam vm' -> case rel of
    SimApp (SimLam sn) sm -> MkLegInv (MP.BetaLam (simValueInv sm vm')) (sc1 sn sm)
    SimLetApp sm sn       -> MkLegInv (MP.BetaLet (simValueInv sm vm')) (sc1 sn sm)

  MP.XiSuc stM' -> case rel of
    SimSuc sm -> case simInv sc sm stM' of
      MkLegInv stM sm' -> MkLegInv (MP.XiSuc stM) (SimSuc sm')
  MP.XiCaseNat stN' -> case rel of
    SimCaseNat sn sz ss -> case simInv sc sn stN' of
      MkLegInv stN sn' -> MkLegInv (MP.XiCaseNat stN) (SimCaseNat sn' sz ss)
  MP.BetaZero -> case rel of
    SimCaseNat SimZero sz _ -> MkLegInv MP.BetaZero sz
  MP.BetaSuc vv' -> case rel of
    SimCaseNat (SimSuc sv) _ ss -> MkLegInv (MP.BetaSuc (simValueInv sv vv')) (sc1 ss sv)
  MP.BetaMu -> case rel of
    SimMu sn -> MkLegInv MP.BetaMu (sc1 sn (SimMu sn))

  MP.XiLet stM' -> case rel of
    SimLet sm sn -> case simInv sc sm stM' of
      MkLegInv stM sm' -> MkLegInv (MP.XiLet stM) (SimLet sm' sn)
  MP.BetaLet vm' -> case rel of
    SimLet sm sn -> MkLegInv (MP.BetaLet (simValueInv sm vm')) (sc1 sn sm)

  MP.XiPair1 stL' -> case rel of
    SimPair sl sr -> case simInv sc sl stL' of
      MkLegInv stL sl' -> MkLegInv (MP.XiPair1 stL) (SimPair sl' sr)
  MP.XiPair2 vl' stR' -> case rel of
    SimPair sl sr -> case simInv sc sr stR' of
      MkLegInv stR sr' -> MkLegInv (MP.XiPair2 (simValueInv sl vl') stR) (SimPair sl sr')
  MP.XiFst stP' -> case rel of
    SimFst sp -> case simInv sc sp stP' of
      MkLegInv stP sp' -> MkLegInv (MP.XiFst stP) (SimFst sp')
  MP.XiSnd stP' -> case rel of
    SimSnd sp -> case simInv sc sp stP' of
      MkLegInv stP sp' -> MkLegInv (MP.XiSnd stP) (SimSnd sp')
  MP.BetaFst vl' vr' -> case rel of
    SimFst (SimPair sl sr) -> MkLegInv (MP.BetaFst (simValueInv sl vl') (simValueInv sr vr')) sl
  MP.BetaSnd vl' vr' -> case rel of
    SimSnd (SimPair sl sr) -> MkLegInv (MP.BetaSnd (simValueInv sl vl') (simValueInv sr vr')) sr

  MP.XiInl stX' -> case rel of
    SimInl sx -> case simInv sc sx stX' of
      MkLegInv stX sx' -> MkLegInv (MP.XiInl stX) (SimInl sx')
  MP.XiInr stY' -> case rel of
    SimInr sy -> case simInv sc sy stY' of
      MkLegInv stY sy' -> MkLegInv (MP.XiInr stY) (SimInr sy')
  MP.XiCaseSum stS' -> case rel of
    SimCaseSum ss sl sr -> case simInv sc ss stS' of
      MkLegInv stS ss' -> MkLegInv (MP.XiCaseSum stS) (SimCaseSum ss' sl sr)
  MP.BetaInl vx' -> case rel of
    SimCaseSum (SimInl sx) sl _ -> MkLegInv (MP.BetaInl (simValueInv sx vx')) (sc1 sl sx)
  MP.BetaInr vy' -> case rel of
    SimCaseSum (SimInr sy) _ sr -> MkLegInv (MP.BetaInr (simValueInv sy vy')) (sc1 sr sy)
  MP.XiAbsurd stM' -> case rel of
    SimAbsurd sm -> case simInv sc sm stM' of
      MkLegInv stM sm' -> MkLegInv (MP.XiAbsurd stM) (SimAbsurd sm')

  MP.XiCons1 stX' -> case rel of
    SimCons sx sxs -> case simInv sc sx stX' of
      MkLegInv stX sx' -> MkLegInv (MP.XiCons1 stX) (SimCons sx' sxs)
  MP.XiCons2 vx' stXs' -> case rel of
    SimCons sx sxs -> case simInv sc sxs stXs' of
      MkLegInv stXs sxs' -> MkLegInv (MP.XiCons2 (simValueInv sx vx') stXs) (SimCons sx sxs')
  MP.XiCaseLst stS' -> case rel of
    SimCaseLst ss sn scons -> case simInv sc ss stS' of
      MkLegInv stS ss' -> MkLegInv (MP.XiCaseLst stS) (SimCaseLst ss' sn scons)
  MP.BetaNil -> case rel of
    SimCaseLst SimNil sn _ -> MkLegInv MP.BetaNil sn
  MP.BetaCons vx' vxs' -> case rel of
    SimCaseLst (SimCons sx sxs) _ scons ->
      MkLegInv (MP.BetaCons (simValueInv sx vx') (simValueInv sxs vxs')) (sc2 scons sx sxs)

{-# LINE 480 "content/part2/Bisimulation.md" #-}
-- | Multi-step forward simulation (`—↠`).
simSteps :: SubstCompat -> SimRel m m' -> MP.Steps m n -> Leg MP.Steps m' n
simSteps _  rel MP.StepsRefl        = MkLeg MP.StepsRefl rel
simSteps sc rel (MP.StepsCons s ss) = case sim sc rel s of
  MkLeg s' rel1 -> case simSteps sc rel1 ss of
    MkLeg ss' rel2 -> MkLeg (MP.StepsCons s' ss') rel2

-- | Multi-step backward simulation (`—↠`).
simStepsInv :: SubstCompat -> SimRel m m' -> MP.Steps m' n' -> LegInv MP.Steps m n'
simStepsInv _  rel MP.StepsRefl        = MkLegInv MP.StepsRefl rel
simStepsInv sc rel (MP.StepsCons s ss) = case simInv sc rel s of
  MkLegInv s' rel1 -> case simStepsInv sc rel1 ss of
    MkLegInv ss' rel2 -> MkLegInv (MP.StepsCons s' ss') rel2

-- | Concrete closed lock-step bisimulation witnesses (zero assumptions!):
-- `let x = fst (0, 1) in suc x` simulates `(λx. suc x) (fst (0, 1))`
-- through both `XiLet` ↔ `XiApp2 VLam` and `BetaLet` ↔ `BetaLam`!
letDesugarSim
  :: SimRel @M.CEmpty @M.TNat
            (M.Let (M.Fst (M.Pair M.Zero (M.Suc M.Zero))) (M.Suc (M.Var M.Z)))
            (M.App (M.Lam (M.Suc (M.Var M.Z))) (M.Fst (M.Pair M.Zero (M.Suc M.Zero))))
letDesugarSim = SimLetApp (SimFst (SimPair SimZero (SimSuc SimZero))) (SimSuc SimVar)

letDesugarSteps
  :: Leg @M.CEmpty @M.TNat MP.Steps
         (M.App (M.Lam (M.Suc (M.Var M.Z))) (M.Fst (M.Pair M.Zero (M.Suc M.Zero))))
         (M.Suc M.Zero)
letDesugarSteps =
  MkLeg
    (MP.StepsCons (MP.XiApp2 M.VLam (MP.BetaFst M.VZero (M.VSuc M.VZero)))
      (MP.StepsCons (MP.BetaLam M.VZero) MP.StepsRefl))
    (SimSuc SimZero)

letDesugarStepsInv
  :: LegInv @M.CEmpty @M.TNat MP.Steps
            (M.Let (M.Fst (M.Pair M.Zero (M.Suc M.Zero))) (M.Suc (M.Var M.Z)))
            (M.Suc M.Zero)
letDesugarStepsInv =
  MkLegInv
    (MP.StepsCons (MP.XiLet (MP.BetaFst M.VZero (M.VSuc M.VZero)))
      (MP.StepsCons (MP.BetaLet M.VZero) MP.StepsRefl))
    (SimSuc SimZero)
