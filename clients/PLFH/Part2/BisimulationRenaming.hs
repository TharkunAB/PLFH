{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, Modifiers #-}
{-# LANGUAGE PolyKinds, StandaloneKindSignatures, TypeApplications #-}
-- | Cross-module client exercising `PLFH.Part2.Bisimulation.simRename` under
-- both binders of `CaseLst`, shifting an outer variable cleanly past two binders.
module PLFH.Part2.BisimulationRenaming
  ( renamedListBody
  , observeRenamedListBody
  ) where

import GHC.Exts (U)
import PLFH.Part2.Bisimulation (SimRel (..), simRename)
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
