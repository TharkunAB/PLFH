{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures, TypeOperators #-}
-- | Minimal reproducer (Serokell R11 / Desugar Core Lint):
-- Matching a promoted-GADT-indexed constructor (`IES`) on an existential box
-- returned inside an outer GADT branch (`DIntro`) fails Desugar Core Lint with:
--   `R11 mixed-kind coercion binder: 'VCons e1 w1 ~# 'VCons e v`
-- even on GHC 2e4fbb752a (after `R11_MixedKindCoercionCoreLint.hs` was fixed!).
--
-- Control: factoring the `MkBox (IES ie)` match into a top-level helper with an
-- explicit `Box ('FS c) ('VCons e a)` signature passes Core Lint cleanly!
-- Uncovered while proving unconditional `denotSubstReflect` in PLFH.Part3.Soundness.
module R11_ExistentialNestedGadtCoreLint where

import Data.Kind (Type)
import HaskLib.Nat (Nat (..))

data Fin (n :: Nat) where
  FZ :: Fin ('Succ n)
  FS :: Fin n -> Fin ('Succ n)

data VEnv (n :: Nat) where
  VNil  :: VEnv 'Zero
  VCons :: VEnv n -> Bool -> VEnv ('Succ n)

type Ins :: forall (n :: Nat). Fin ('Succ n) -> VEnv n -> Bool -> VEnv ('Succ n) -> Type
data Ins c e u e' where
  IEZ :: Ins 'FZ e u ('VCons e u)
  IES :: Ins c e u e' -> Ins ('FS c) ('VCons e w) u ('VCons e' w)

type StepS :: forall (n :: Nat). Fin ('Succ n) -> Type
data StepS c where
  SLam :: StepS ('FS c) -> StepS c

type Den :: forall (n :: Nat). VEnv n -> Type
data Den e where
  DIntro :: Den ('VCons e a) -> Den e

data Box (c :: Fin ('Succ n)) (e :: VEnv n) where
  MkBox :: forall (n :: Nat) (c :: Fin ('Succ n)) (e :: VEnv n) (u :: Bool) (e' :: VEnv ('Succ n)).
           Ins c e u e' -> Den e' -> Box c e

-- Control: top-level helper passes Core Lint!
unboxCtrl :: Box ('FS c) ('VCons e a) -> Box c e
unboxCtrl (MkBox (IES ie) d) = MkBox ie (DIntro d)

-- Trigger: identical `MkBox (IES ie)` match inline inside the `SLam`/`DIntro` branch
-- fails Desugar Core Lint with `R11 mixed-kind coercion binder: 'VCons ... ~# 'VCons ...`!
go :: forall (n :: Nat) (c :: Fin ('Succ n)) (e :: VEnv n) (eBot :: VEnv ('Succ n)).
      StepS c -> Ins c e 'False eBot -> Den e -> Box c e
go (SLam sB) ieBot (DIntro dBody) = case go sB (IES ieBot) dBody of
  MkBox (IES ie) db -> MkBox ie (DIntro db)
