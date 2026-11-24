{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, PolyKinds #-}
{-# LANGUAGE TypeApplications, TypeOperators #-}
-- | Minimal reproducer (Serokell R03; GHC Proposal #378; Eisenberg 2016 §6.6.1):
-- Passing an inline indexed-GADT constructor (`P.CHole`) directly as a
-- `foreach (c :: P.UCtx Zero Zero)` argument fails with `GHC-83605`, even
-- though passing it through a plain non-`foreach` wrapper (`wrap c = ...;
-- wrap P.CHole`) compiles cleanly. Hit in `RuntimeSmokeTest.hs`,
-- `BisimulationRenaming.hs`, and `CompositionalPlug.hs`.
module R03_InlineGadtCtorForEachArg where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..))
import qualified ReproOpsPlug as P

plugHoleId :: forall (t :: P.UTerm Zero).
              foreach (c :: P.UCtx Zero Zero) -> Maybe (P.plug c t :~: t)
plugHoleId P.CHole       = Just Refl
plugHoleId (P.CLam _)    = Nothing
plugHoleId (P.CAppL _ _) = Nothing
plugHoleId (P.CAppR _ _) = Nothing

checkDirect :: Maybe (P.plug (P.CHole :: P.UCtx Zero Zero) (P.ULam (P.UVar P.FZ) :: P.UTerm Zero) :~: (P.ULam (P.UVar P.FZ) :: P.UTerm Zero))
checkDirect = plugHoleId @(P.ULam (P.UVar P.FZ) :: P.UTerm Zero) (P.CHole :: P.UCtx Zero Zero)
