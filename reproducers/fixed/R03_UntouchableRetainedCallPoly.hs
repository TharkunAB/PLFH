{-# LANGUAGE AllowAmbiguousTypes, DataKinds, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, ScopedTypeVariables, TypeApplications #-}
-- | Minimal reproducer (Serokell R03 / R05; OutsideIn(X) JFP 2011;
-- Eisenberg 2016 Bake §§6.3-6.4; Quick Look ICFP 2020 / GHC Proposal #274):
-- Inside a `foreach (c :: P.UCtx m n)` equation, calling a polymorphic lemma
-- (`lamCong (comp c eq)`) fails with `GHC-83865` ("untouchable inside the
-- constraints: () bound by a retained application") unless every type argument
-- is supplied manually (`lamCong @n @(P.plug c t1) @(P.plug c t2)`).
-- Hit in `clients/PLFH/Part3/CompositionalPlug.hs` and `ContextualEquivalence.md`.
module R03_UntouchableRetainedCallPoly where

import Data.Kind (Type)
import HaskLib.Nat (Nat (..))
import qualified ReproOpsPlug as P

data Rel (n :: Nat) (t1 :: P.UTerm n) (t2 :: P.UTerm n) :: Type where
  MkRel :: Rel n t1 t2

lamCong :: forall n (b1 :: P.UTerm (Succ n)) (b2 :: P.UTerm (Succ n)).
           Rel (Succ n) b1 b2 -> Rel n (P.ULam b1) (P.ULam b2)
lamCong MkRel = MkRel

appCong :: forall n (l1 :: P.UTerm n) (l2 :: P.UTerm n) (r1 :: P.UTerm n) (r2 :: P.UTerm n).
           Rel n l1 l2 -> Rel n r1 r2 -> Rel n (P.UApp l1 r1) (P.UApp l2 r2)
appCong MkRel MkRel = MkRel

comp :: forall m n (t1 :: P.UTerm m) (t2 :: P.UTerm m).
        foreach (c :: P.UCtx m n) -> Rel m t1 t2 -> Rel n (P.plug c t1) (P.plug c t2)
comp P.CHole       = \eq -> eq
comp (P.CLam c)    = \eq -> lamCong (comp @m @(Succ n) @t1 @t2 c eq)
comp (P.CAppL c _) = \eq -> appCong (comp @m @n @t1 @t2 c eq) MkRel
comp (P.CAppR _ c) = \eq -> appCong MkRel (comp @m @n @t1 @t2 c eq)
