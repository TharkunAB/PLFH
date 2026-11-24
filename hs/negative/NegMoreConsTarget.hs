{-# LANGUAGE DependentTypes #-}
-- EXPECT-ERROR: GHC-83865
module NegMoreConsTarget (wrongHead) where

import qualified PLFH.Part2.More as M
import PLFH.Part2.MoreProgress (Step (..))

wrongHead :: Step @M.CEmpty @(M.TProd M.TNat (M.TList M.TNat))
                  (M.CaseLst (M.Cons (M.Suc M.Zero) (M.Cons M.Zero M.Nil))
                             (M.Pair M.Zero M.Nil)
                             (M.Pair (M.Var (M.S M.Z)) (M.Var M.Z)))
                  (M.Pair M.Zero (M.Cons M.Zero M.Nil))
wrongHead = BetaCons (M.VSuc M.VZero) (M.VCons M.VZero M.VNil)
