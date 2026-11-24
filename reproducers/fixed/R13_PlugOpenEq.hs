{-# LANGUAGE AllowAmbiguousTypes, DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, StandaloneKindSignatures, TypeOperators #-}
-- | Minimal reproducer (Serokell R13/R16):
-- `ReproOpsPlug` compiles with `-fwrite-source-equations`, yet GHC does not
-- publish checked equations for `plug :: UCtx m n -> UTerm m -> UTerm n`
-- (a two-index GADT traversal passing `t :: UTerm m` unchanged).
--
-- Downstream proof `compositionality` in PLFA Part 3 Compositional fails with:
--   GHC-70565: Cannot evaluate 'P.plug' in a type.
--              Each constructor field must be a closed literal.
module R13_PlugOpenEq (plugLamEq) where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..))
import qualified ReproOpsPlug as P

plugLamEq
  :: forall (m :: Nat) (n :: Nat) (t :: P.UTerm m).
     foreach (c :: P.UCtx m (Succ n)) ->
     P.plug (P.CLam c) t :~: P.ULam (P.plug c t)
plugLamEq _ = Refl
