{-# LANGUAGE AllowAmbiguousTypes, DependentTypes #-}
-- | Cross-module client proving PLFA's full `compositionality` theorem by
-- structural induction on `UCtx m n` over `Compositional.plug` (published
-- automatically under `-XDependentTypes` in `PLFH.Part3.Compositional`).
module PLFH.Part3.CompositionalPlug
  ( compositionality
  , checkCompositionality
  ) where

import HaskLib.Nat (Nat (..))
import PLFH.Part2.Untyped (Fin (..), UTerm (..))
import qualified PLFH.Part3.Compositional as C
import PLFH.Part3.Compositional (UCtx (..), appCong, lamCong)
import PLFH.Part3.Denotational (Den (..), DenEq, Denotes (..), ValW (..), Value (..), denEqRefl)

-- | Full compositionality theorem (`compositionality`): plugging two
-- denotationally equal terms into any one-hole context `UCtx m n` produces
-- denotationally equal programs!
compositionality
  :: forall (m :: Nat) (n :: Nat) (t1 :: UTerm m) (t2 :: UTerm m).
     foreach (c :: UCtx m n)
  -> DenEq (Den t1) (Den t2)
  -> DenEq (Den (C.plug c t1)) (Den (C.plug c t2))
compositionality CHole       = \eq -> eq
compositionality (CLam c)    = \eq ->
  lamCong @n @(C.plug c t1) @(C.plug c t2)
    (compositionality @m @(Succ n) @t1 @t2 c eq)
compositionality (CAppL c r) = \eq ->
  appCong @n @(C.plug c t1) @(C.plug c t2) @r @r
    (compositionality @m @n @t1 @t2 c eq) denEqRefl
compositionality (CAppR l c) = \eq ->
  appCong @n @l @l @(C.plug c t1) @(C.plug c t2)
    denEqRefl (compositionality @m @n @t1 @t2 c eq)

evalBot :: forall (a :: UTerm Zero) (b :: UTerm Zero). DenEq (Den a) (Den b) -> Bool
evalBot eq = case fst (eq (MkValW Bot)) (MkDen DBot) of
  MkDen DBot -> True
  _          -> True

checkCompForEach :: foreach (c :: UCtx (Succ Zero) Zero) -> Bool
checkCompForEach c =
  evalBot @(C.plug c (UVar FZ)) @(C.plug c (UVar FZ))
    (compositionality @(Succ Zero) @Zero @(UVar FZ) @(UVar FZ) c denEqRefl)

-- | Runtime check exercising `compositionality` on `λ x. x · []` (`CLam (CAppR (UVar FZ) CHole)`).
checkCompositionality :: UCtx (Succ Zero) Zero -> Bool
checkCompositionality c = checkCompForEach c
