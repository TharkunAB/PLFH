{-# LANGUAGE AllowAmbiguousTypes, DataKinds, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, StandaloneKindSignatures, TypeOperators #-}
-- | Minimal reproducer (Serokell R13 / R16 / R21; GHC Proposals #378 & #509):
-- Cross-module `-fwrite-source-equations` publishes checked equations for the
-- two-index GADT traversal `plug :: UCtx m n -> UTerm m -> UTerm n` (verified
-- by `reproducers/fixed/R13_PlugOpenEq.hs`), but using `plug` in a type within
-- its *own* defining module fails with `GHC-68947`, forcing
-- `PLFH.Part3.Compositional` to split `compositionality` into a separate
-- client module (`clients/PLFH/Part3/CompositionalPlug.hs`).
module R13_SameModulePlugOpenEq where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..))

data Fin (n :: Nat) where
  FZ :: Fin (Succ n)
  FS :: Fin n -> Fin (Succ n)

data UTerm (n :: Nat) where
  UVar :: Fin n -> UTerm n
  ULam :: UTerm (Succ n) -> UTerm n
  UApp :: UTerm n -> UTerm n -> UTerm n

data UCtx (m :: Nat) (n :: Nat) where
  CHole :: UCtx n n
  CLam  :: UCtx m (Succ n) -> UCtx m n
  CAppL :: UCtx m n -> UTerm n -> UCtx m n
  CAppR :: UTerm n -> UCtx m n -> UCtx m n

plug :: UCtx m n -> UTerm m -> UTerm n
plug CHole       t = t
plug (CLam c)    t = ULam (plug c t)
plug (CAppL c r) t = UApp (plug c t) r
plug (CAppR l c) t = UApp l (plug c t)

plugLamEq :: forall m n (c :: UCtx m (Succ n)) (t :: UTerm m).
             plug (CLam c) t :~: ULam (plug c t)
plugLamEq = Refl
