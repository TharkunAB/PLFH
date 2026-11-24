{-# LANGUAGE DependentTypes #-}
-- | Cross-module client exercising `PLFH.Part2.Bisimulation.simRename` under
-- both binders of `CaseLst` and `simSubst` across `SimLetApp`.
module PLFH.Part2.BisimulationRenaming
  ( renamedListBody
  , observeRenamedListBody
  , checkSubstRefl
  , observeSubstLet
  ) where

import GHC.Exts (U)
import PLFH.Part2.Bisimulation (Compatible, SimRel (..), simRefl, simRename, simSubst)
import qualified PLFH.Part2.More as M

type Source = M.CExt M.CEmpty M.TNat
type Target = M.CExt Source M.TNat
type Shift :: forall (a :: M.Ty). @U M.Lookup Source a %U -> M.Lookup Target a
type Shift x = M.S x

type Body = M.CaseLst (M.Nil :: M.Term Source (M.TList M.TNat)) M.Zero
                      (M.Var (M.S (M.S M.Z)))
type RenamedBody = M.CaseLst (M.Nil :: M.Term Target (M.TList M.TNat)) M.Zero
                             (M.Var (M.S (M.S (M.S M.Z))))

-- | Shift an outer lookup through both binders of a list alternative.
renamedListBody :: SimRel RenamedBody RenamedBody
renamedListBody =
  simRename @Source @Target @M.TNat @Shift
    (SimCaseLst SimNil SimZero SimVar :: SimRel Body Body)

-- | Observe the proof for the renamed list alternative.
observeRenamedListBody :: Bool
observeRenamedListBody = case renamedListBody of
  SimCaseLst SimNil SimZero SimVar -> True

type IdSub :: forall (a :: M.Ty). @U M.Lookup Source a %U -> M.Term Source a
type IdSub x = M.Var x

idCompat :: Compatible @Source @Source IdSub IdSub
idCompat _ = SimVar

-- | Exercise 20-constructor `simSubst` across `M.Let` under a binder (`M.exts`).
substRefl :: foreach (m :: M.Term Source M.TNat)
          -> SimRel (M.subst IdSub m) (M.subst IdSub m)
substRefl m = simSubst @Source @Source @M.TNat @IdSub @IdSub @m m idCompat (simRefl m)

checkSubstRefl :: M.Term Source M.TNat -> Bool
checkSubstRefl term = case substRefl term of
  SimLet SimVar (SimSuc SimVar) -> True
  _                             -> False

observeSubstLet :: Bool
observeSubstLet = checkSubstRefl (M.Let (M.Var M.Z) (M.Suc (M.Var M.Z)))
