{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, StandaloneKindSignatures, TypeOperators #-}
{-# OPTIONS_GHC -fwrite-source-equations #-}
-- | Minimal provider for `R13_PlugOpenEq.hs` (skipped as ReproOps*).
-- Models `PLFH.Part3.Compositional`'s one-hole context `UCtx m n` and `plug`.
module ReproOpsPlug where

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
