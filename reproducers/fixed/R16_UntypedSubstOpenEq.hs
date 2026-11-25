{-# LANGUAGE AllowAmbiguousTypes, DependentTypes #-}
-- | Minimal reproducer (Serokell R03 / R16, Proposal #378):
-- Wave 5+6 (`91a63517fc`) certified 1-index `Fin n` / `UTerm n` open equations
-- (`subApp` below passes at `-O0` and `-O2`, unblocking `PLFH.Part2.Substitution`).
-- Remaining gap on lines 42-43 (`congExts _ U.FZ = Refl`): matching a retained
-- constructor pattern directly on a function LHS after an earlier non-retained
-- function wildcard fails with `GHC-83605` (whereas `congExts eq y = case y of ...`
-- checks cleanly). Tracked for Wave 7A (`elabGeneralRetainedMatrix`).
module R16_UntypedSubstOpenEq (SubstFn, subApp, congExts) where

import Data.Type.Equality ((:~:) (Refl))
import GHC.Exts (U)
import GHC.Types (Matchability)
import HaskLib.Nat (Nat (..))
import qualified ReproOpsUntypedSubst as U

type SubstFn (m :: Nat) (n :: Nat) = U.Fin m %U -> U.UTerm n

cong :: forall {a} {b} {m :: Matchability}.
        forall (f :: a %m -> b) -> forall (x :: a) (y :: a).
        x :~: y -> f x :~: f y
cong _ Refl = Refl

subApp :: forall m n (s :: SubstFn m n) (l :: U.UTerm m) (r :: U.UTerm m).
          U.substU s (U.UApp l r) :~: U.UApp (U.substU s l) (U.substU s r)
subApp = Refl

congExts :: forall m n (s1 :: SubstFn m n) (s2 :: SubstFn m n).
            (foreach (x :: U.Fin m) -> s1 x :~: s2 x)
         -> foreach (y :: U.Fin (Succ m)) -> U.extsU s1 y :~: U.extsU s2 y
congExts _  U.FZ     = Refl
congExts eq (U.FS x) = cong (U.renameU U.shiftFin) (eq x)
