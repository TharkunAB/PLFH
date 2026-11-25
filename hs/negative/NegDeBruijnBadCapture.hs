{-# LANGUAGE DependentTypes #-}
-- EXPECT-ERROR: GHC-83865
module NegDeBruijnBadCapture (badCapture) where

import qualified PLFH.Part2.DeBruijn as D

badCapture
  :: D.Step @(D.CExt D.CEmpty D.TNat)
            @(D.TArr D.TNat (D.TArr D.TNat D.TNat))
            (D.App (D.Lam (D.Lam (D.Var (D.S D.Z)))) (D.Lam (D.Var (D.S D.Z))))
            (D.Lam (D.Lam (D.Var (D.S D.Z))))
badCapture = D.BetaLam D.VLam
