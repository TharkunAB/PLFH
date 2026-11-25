{-# LANGUAGE DependentTypes #-}
-- | Cross-module client exercising `PLFH.Part2.Bisimulation.simRename` under
-- both binders of `CaseLst` and unconditional `simSubst` across `SimLetApp`.
module PLFH.Part2.BisimulationRenaming
  ( renamedListBody
  , observeRenamedListBody
  , checkSubstRefl
  , observeSubstLet
  ) where

import PLFH.Part2.Bisimulation (Compatible, SimRel (..), simRefl, simSubst, simWeaken)
import qualified PLFH.Part2.More as M

type Source = M.CExt M.CEmpty M.TNat
type Target = M.CExt Source M.TNat

type Body = M.CaseLst (M.Nil :: M.Term Source (M.TList M.TNat)) M.Zero
                      (M.Var (M.S (M.S M.Z)))
type RenamedBody = M.CaseLst (M.Nil :: M.Term Target (M.TList M.TNat)) M.Zero
                             (M.Var (M.S (M.S (M.S M.Z))))

-- | Shift an outer lookup through both binders of a list alternative.
renamedListBody :: SimRel RenamedBody RenamedBody
renamedListBody =
  simWeaken @Source @M.TNat
    (SimCaseLst SimNil SimZero
       (SimVar (M.S (M.S M.Z) :: M.Lookup (M.CExt (M.CExt Source M.TNat) (M.TList M.TNat)) M.TNat))
      :: SimRel Body Body)

-- | Observe the proof for the renamed list alternative.
observeRenamedListBody :: Bool
observeRenamedListBody = case renamedListBody of
  SimCaseLst SimNil SimZero (SimVar _) -> True

idSub :: forall a. M.Lookup Source a -> M.Term Source a
idSub x = M.Var x

idCompat :: Compatible @Source @Source idSub idSub
idCompat x = SimVar x

-- | Exercise unconditional 20-constructor `simSubst` across `M.Let` under a binder (`M.exts`).
substRefl :: foreach (m :: M.Term Source M.TNat)
          -> SimRel (M.subst idSub m) (M.subst idSub m)
substRefl m = simSubst @Source @Source @M.TNat @idSub @idSub @m @m idCompat (simRefl m)

checkSubstRefl :: M.Term Source M.TNat -> Bool
checkSubstRefl term = case substRefl term of
  SimLet (SimVar _) (SimSuc (SimVar _)) -> True
  _                                     -> False

observeSubstLet :: Bool
observeSubstLet = checkSubstRefl (M.Let (M.Var M.Z) (M.Suc (M.Var M.Z)))
