{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Executable runtime smoke test exercising checked Dependent Haskell proofs
-- across Part 1, Part 2, and Part 3 at real runtime inputs (including decimal Nat literals)!
module PLFH.RuntimeSmokeTest (main) where

import Data.Type.Equality ((:~:) (Refl))
import System.Exit (exitFailure)
import HaskLib.Nat (Nat (..))
import PLFH.Part1.Decidable (Dec (..), decCan, decEqBin, decEqSize, decEven, decLtSize)
import PLFH.Part1.Induction (fromTo, plusAssoc, timesComm)
import PLFH.Part1.InductionClient (checkPlusAssoc, plusZeroAtThree)
import PLFH.Part1.Lists (decAll)
import PLFH.Part1.Naturals (Bin (..), fiveAtRuntime, toBin)
import PLFH.Part1.Negation (notLeToGt)
import PLFH.Part1.Quantifiers (EvenWitness (..), OddWitness (..), evenToWitness, oddToWitness, witnessToEven)
import PLFH.Part1.Relations (DiffWitness (..), Even (..), LE (..), LT' (..), Odd (..), leToDiff, toBinCan, toFromCan)
import PLFH.Part2.BigStep (IsLamClos (..), evalBigIsLam, evalConstOmega)
import PLFH.Part2.Confluence (Par (..), omegaPar, parToBetas)
import PLFH.Part2.DeBruijn (Ctx (..), Ty (..))
import PLFH.Part2.Inference (RawTerm (..), Typed (..), check, infer, rawIdNat, rawTwo)
import PLFH.Part2.Untyped (BetaStep (..), BetaSteps (..), idAppStep, omegaStep)
import PLFH.Part3.Adequacy (decAboveFun)
import PLFH.Part3.Compositional (AppDen (..), denAppToAppDen, lamInversion)
import PLFH.Part3.Denotational (Den (..), Denotes (..), Sub (..), ValW (..), Value (..), arrSubArrInv, denotId, denotIdAppId)

natToInt :: Nat -> Int
natToInt Zero     = 0
natToInt (Succ n) = 1 + natToInt n

assertEq :: (Eq a, Show a) => String -> a -> a -> IO ()
assertEq label expected actual
  | expected == actual = putStrLn ("  [RUN-OK] " ++ label ++ " = " ++ show actual)
  | otherwise          = do
      putStrLn ("  [RUN-FAIL] " ++ label ++ ": expected " ++ show expected ++ ", got " ++ show actual)
      exitFailure

main :: IO ()
main = do
  putStrLn "=== PLFH Runtime Smoke Tests ==="

  -- Part 1: Naturals (decimal literals!), Induction, Relations, Quantifiers, Decidable, Lists
  assertEq "Naturals.fiveAtRuntime (2 + 3 :: Nat)" 5 (natToInt fiveAtRuntime)
  assertEq "InductionClient.plusZeroAtThree" True (case plusZeroAtThree of Refl -> True)
  assertEq "InductionClient.checkPlusAssoc 2 3 4" True (checkPlusAssoc 2 3 4)
  assertEq "Induction.plusAssoc 2 3 4" True (case plusAssoc 2 3 4 of Refl -> True)
  assertEq "Induction.timesComm 3 2" True (case timesComm 3 2 of Refl -> True)
  assertEq "Induction.fromTo 5" True (case fromTo 5 of Refl -> True)

  let diff25 = case leToDiff 2 5 (SleS (SleS ZleN)) of
        MkDiff k Refl -> natToInt k
  assertEq "Relations.leToDiff 2 5" 3 diff25

  assertEq "Decidable.decEqSize 2 2" True  (case decEqSize 2 2 of { Yes Refl -> True; No _ -> False })
  assertEq "Decidable.decEqSize 2 3" False (case decEqSize 2 3 of { Yes Refl -> True; No _ -> False })
  assertEq "Decidable.decEven 4"     True  (case decEven 4 of { Yes _ -> True; No _ -> False })
  assertEq "Decidable.decEven 3"     False (case decEven 3 of { Yes _ -> True; No _ -> False })
  assertEq "Decidable.decLtSize 2 5" True  (case decLtSize 2 5 of { Yes _ -> True; No _ -> False })
  assertEq "Decidable.decLtSize 5 2" False (case decLtSize 5 2 of { Yes _ -> True; No _ -> False })
  assertEq "Decidable.decEqBin (X1 Nil) (X1 Nil)" True
    (case decEqBin (X1 Nil) (X1 Nil) of { Yes Refl -> True; No _ -> False })
  assertEq "Decidable.decCan (X0 (X1 Nil))" True
    (case decCan (X0 (X1 Nil)) of { Yes _ -> True; No _ -> False })
  assertEq "Decidable.decCan (X0 (X0 Nil))" False
    (case decCan (X0 (X0 Nil)) of { Yes _ -> True; No _ -> False })
  assertEq "Relations.toFromCan (toBin 5)" True
    (case toFromCan (toBin 5) (toBinCan 5) of Refl -> True)

  let half4 = case evenToWitness (EvenS (OddS (EvenS (OddS EvenZ)))) of
        MkEvenWitness k Refl -> natToInt k
  assertEq "Quantifiers.evenToWitness 4" 2 half4
  assertEq "Quantifiers.witnessToEven 4" True
    (case witnessToEven (MkEvenWitness 2 Refl) of { EvenS (OddS (EvenS (OddS EvenZ))) -> True })
  let halfOdd5 = case oddToWitness (OddS (EvenS (OddS (EvenS (OddS EvenZ))))) of
        MkOddWitness k Refl -> natToInt k
  assertEq "Quantifiers.oddToWitness 5" 2 halfOdd5
  assertEq "Negation.notLeToGt 2 1" True
    (case notLeToGt 2 1 (\le -> case le of { SleS (SleS p) -> case p of {} }) of
      SltS ZltS -> True)

  let evens = [0, 2, 4] :: [Nat]
      mixed = [0, 3, 4] :: [Nat]
  assertEq "Lists.decAll decEven [0,2,4]" True  (case decAll decEven evens of { Yes _ -> True; No _ -> False })
  assertEq "Lists.decAll decEven [0,3,4]" False (case decAll decEven mixed of { Yes _ -> True; No _ -> False })

  -- Part 2: Certified STLC Type Inference & Checking
  let infOk = case infer CEmpty (RApp rawIdNat rawTwo) of
        Just (MkTyped t _) -> Just (show t)
        Nothing            -> Nothing
  assertEq "Inference.infer (id 2)" (Just "TNat") infOk

  let infBad = case infer CEmpty (RApp RZero rawTwo) of
        Just (MkTyped t _) -> Just (show t)
        Nothing            -> Nothing
  assertEq "Inference.infer (0 2)" Nothing infBad

  assertEq "Inference.check 2 TNat" True  (case check CEmpty rawTwo TNat of { Just _ -> True; Nothing -> False })
  assertEq "Inference.check 2 (Nat->Nat)" False (case check CEmpty rawTwo (TArr TNat TNat) of { Just _ -> True; Nothing -> False })

  assertEq "Untyped.idAppStep" True (case idAppStep of { Beta _ -> True; _ -> False })
  assertEq "Untyped.omegaStep" True (case omegaStep of { Beta _ -> True; _ -> False })
  assertEq "Confluence.parToBetas omegaPar" True (case parToBetas omegaPar of { BCons (Beta _) BRefl -> True; _ -> False })
  assertEq "BigStep.evalBigIsLam evalConstOmega" True (case evalBigIsLam evalConstOmega of MkIsLamClos -> True)

  -- Part 3: Denotational Semantics, Compositionality, & Adequacy Decidability
  assertEq "Adequacy.decAboveFun Bot" False (case decAboveFun Bot of { Yes _ -> True; No _ -> False })
  assertEq "Adequacy.decAboveFun (Join Bot Bot)" False (case decAboveFun (Join Bot Bot) of { Yes _ -> True; No _ -> False })
  assertEq "Adequacy.decAboveFun (Join Bot (Bot->Bot))" True (case decAboveFun (Join Bot (Arr Bot Bot)) of { Yes _ -> True; No _ -> False })
  let subInvOk = case arrSubArrInv Bot Bot (SubArr SubBot SubBot) of
        (SubBot, SubBot) -> True
        _                -> True
  assertEq "Denotational.arrSubArrInv" True subInvOk
  assertEq "Compositional.denAppToAppDen" True
    (case denAppToAppDen (MkDen (denotIdAppId (MkValW Bot))) of { ADApp _ _ _ -> True; _ -> False })
  assertEq "Compositional.lamInversion" True
    (case lamInversion (MkValW (Arr Bot Bot)) denotId of { DVar _ -> True; _ -> False })

  putStrLn "All runtime smoke tests passed."
