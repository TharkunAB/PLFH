{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, PolyKinds, RankNTypes, StandaloneKindSignatures #-}
-- | Minimal reproducer (Serokell R13/R16):
-- Proving structural compatibility of renaming (`simRename`) or simultaneous
-- substitution (`simSubst`) in PLFA Part 2 Bisimulation & Substitution requires
-- mentioning `rename r m` in a type where `r :: forall x. Lookup g x -> Lookup d x`
-- is an abstract renaming type variable.
--
-- Even though `ReproOpsDoubleSubst` enables `-fwrite-source-equations` and
-- exports checked closure equations for `substSingle` and `substDouble`,
-- mentioning `R.rename r m` with an abstract function variable `r` fails with:
--   GHC-70565: Cannot evaluate 'R.rename' in a type.
--              This argument is a type variable. Closed evaluation requires a known value.
module R16_AbstractRenamingInType (SimRel (..), simRename) where

import Data.Kind (Type)
import qualified ReproOpsDoubleSubst as R

type SimRel :: forall (g :: R.Ctx) (a :: R.Ty). R.Term g a -> R.Term g a -> Type
data SimRel m m' where
  SimVar  :: SimRel (R.Var x) (R.Var x)
  SimLam  :: SimRel n n' -> SimRel (R.Lam n) (R.Lam n')
  SimApp  :: SimRel l l' -> SimRel m m' -> SimRel (R.App l m) (R.App l' m')
  SimZero :: SimRel R.Zero R.Zero

simRename
  :: forall (g :: R.Ctx) (d :: R.Ctx) (a :: R.Ty)
            (r :: forall x. R.Lookup g x -> R.Lookup d x)
            (m :: R.Term g a) (m' :: R.Term g a).
     SimRel m m' -> SimRel (R.rename r m) (R.rename r m')
simRename SimVar       = SimVar
simRename (SimLam s)   = SimLam (simRename s)
simRename (SimApp l m) = SimApp (simRename l) (simRename m)
simRename SimZero      = SimZero
