{-# LANGUAGE AllowAmbiguousTypes, DependentTypes #-}
-- | Minimal reproducer (Serokell R13 / R16, Proposal #378):
-- Blocks proving PLFA Part 2 `PLFH.Part2.Substitution` (σ-calculus identities
-- and Barendregt's Substitution Lemma over `Untyped.renameU` / `Untyped.substU`,
-- using constructive pointwise equality `foreach (x :: Fin m) -> ...` with
-- zero function extensionality needed!).
--
-- Root cause (`GHC.Tc.Gen.SourceClosure`):
-- `publishWeakening`, `publishLookupExtension`, and `publishClosureTraversal`
-- hardcode 2-index `(Ctx, Ty)` rank-2 GADTs (`Lookup g a` / `Term g a`, as in
-- `PLFH.Part2.More` -> `PLFH.Part2.Bisimulation`). For 1-index `Nat`-scoped
-- rank-1 `Fin n` / `UTerm n` (`PLFH.Part2.Untyped`), `SourceClosure` publishes
-- open checked equations ONLY for the closed `substSingleU` closure, and NONE
-- for `shiftFin`, `extU`, `renameU`, `extsU`, or `substU`!
--
-- Expected behavior: `subApp = Refl` and `congExts` check directly against
-- `ReproOpsUntypedSubst`'s open checked equations for `substU`/`extsU`/`renameU`/`shiftFin`.
-- Actual behavior on Wave 4 Track A (`c5dbff62fb`): fails with `GHC-70566` on
-- `U.substU s (U.UApp l r)` and `GHC-68947` on `U.shiftFin`.
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
