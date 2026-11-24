{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
-- | Minimal reproducer (Serokell R13 / R16):
-- On `PLFH.Part2.DeBruijn` (single-binder `ext r` / `exts s`), `-fwrite-source-equations`
-- publishes `$closure:substSingle` / `$apply:substSingle` cleanly into the interface.
-- However, adding a two-binder constructor (`CaseLst`, lifting via `ext (ext r)` and
-- `exts (exts s)` as in `PLFH.Part2.More`) suppresses source-closure publication even
-- for `substSingle` (emitting no `$closure:` / `$apply:` in `ReproOpsDoubleSubst.hi`
-- and failing below with `GHC-70565`), and `substDouble` (`Z -> w; S Z -> v; S (S x) -> Var x`)
-- is likewise not published as a checked closure even on single-binder terms.
-- Blocks `PLFH.Part2.More` intrinsically-typed `Step` and `progress`.
module R13_DoubleBinderSubstClosure where

import Data.Kind (Type)
import qualified ReproOpsDoubleSubst as M

type Step :: forall (g :: M.Ctx) (a :: M.Ty). M.Term g a -> M.Term g a -> Type
data Step m n where
  BetaSingle :: forall g a b (n :: M.Term (M.CExt g a) b) (w :: M.Term g a).
                Step (M.App (M.Lam n) w) (M.substSingle n w)
  BetaDouble :: forall g a b (xs :: M.Term g (M.TList a)) (n :: M.Term g b)
                       (c :: M.Term (M.CExt (M.CExt g a) (M.TList a)) b)
                       (v :: M.Term g a) (vs :: M.Term g (M.TList a)).
                Step (M.CaseLst xs n c) (M.substDouble c v vs)
