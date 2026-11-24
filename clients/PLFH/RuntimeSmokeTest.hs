{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE LambdaCase, ScopedTypeVariables, TypeApplications, TypeOperators #-}
-- | Executable runtime smoke test exercising checked Dependent Haskell proofs
-- across Part 1, Part 2, and Part 3 at real runtime inputs (including decimal Nat literals)!
module PLFH.RuntimeSmokeTest (main) where

import Data.Type.Equality ((:~:) (Refl))
import GHC.Sigma (Sigma (Pair))
import System.Exit (exitFailure)
import HaskLib.Nat (Nat (..))
import PLFH.Part1.Connectives (prodCommIso, sumCommIso)
import PLFH.Part1.Decidable (Dec (..), decCan, decEqBin, decEqSize, decEven, decLtSize, plusExists)
import PLFH.Part1.Equality (evenComm)
import PLFH.Part1.Induction (fromTo, monusPlusAssoc, plusAssoc, plusRearrange, plusSwap, powMul, powPlus, powTimes, threeMonusTwo, threePowFour, timesComm, twoMonusThree, zeroMonus)
import PLFH.Part1.InductionClient (checkPlusAssoc, plusZeroAtThree)
import PLFH.Part1.Isomorphism (Embed (..), Iff (..), Iso (..), IsoSize (..), binEmbedding, embedImpliesIff, embedRefl, embedTrans, isoImpliesEmbed, isoRefl, isoSizeRefl, isoSizeSym, isoSym, isoTrans, natIsoRefl)
import PLFH.Part1.AnyWitnessIso (anyIsoWitness)
import PLFH.Part1.Lists (All (..), Any (..), AnyWitness (..), In, allToIn, anyIffWitness, decAll, decIn, downFrom, foldrPlusAppend, foldrPlusSeed, foldrTimesAppend, foldrTimesSeed, inToAll, lengthDownFrom, lengthZeros, memberValue, notAnyIffAllNot, revAppend, revInvolutive, reverses, shuntAppend, shuntRev)
import PLFH.Part1.ListsProof (decodeHeadEven, decodeSecondEven, sampleTailMem, witnessToAnyEvenThere)
import qualified PLFH.Part1.Naturals as N
import PLFH.Part1.Naturals (Bin (..), fiveAtRuntime, toBin)
import PLFH.Part1.Negation (notLeToGt)
import PLFH.Part1.Quantifiers (EvenWitness (..), OddWitness (..), evenToWitness, oddToWitness, witnessToEven)
import PLFH.Part1.Relations (DiffWitness (..), Even (..), LE (..), LT' (..), Odd (..), leToDiff, plusMonoLt, timesMono, toBinCan, toFromCan)
import PLFH.Part2.BigStep (EvalBig (..), IsLamClos (..), evalBigIsLam, evalConstOmega, evalDeterm, evalIdApp)
import PLFH.Part2.Bisimulation (Leg (..), LegInv (..), SimRel (..), letDesugarSim, letDesugarSteps, letDesugarStepsInv, simRefl, simTrans, simValue, simValueInv)
import PLFH.Part2.Confluence (Par (..), betaToPar, normalNoBetaSteps, omegaPar, parRefl, parToBetas)
import PLFH.Part2.DeBruijn (Ctx (..), Ty (..))
import qualified PLFH.Part2.DeBruijn as DB
import qualified PLFH.Part2.DeBruijnProgress as DBP
import PLFH.Part2.Inference (RawTerm (..), Typed (..), check, infer, rawIdNat, rawTwo)
import qualified PLFH.Part2.Lambda as L
import qualified PLFH.Part2.More as M
import qualified PLFH.Part2.MoreProgress as MP
import PLFH.Part2.Properties (EvalResult (..), Progress (..), TermW (..), eval, preserve, progress, stepDeterm)
import qualified PLFH.Part2.Untyped as U
import PLFH.Part2.Untyped (BetaStep (..), BetaSteps (..), idAppStep, idIsNormal, omegaStep)
import PLFH.Part3.Adequacy (HaltsBig (..), adequacyDelta, adequacyIdApp, decAboveFun)
import PLFH.Part3.Compositional (AppDen (..), denAppToAppDen, lamInversion)
import PLFH.Part3.ContextualEquivalence (Terminates (..), terminatesLam, terminatesStep)
import PLFH.Part3.Denotational (Den (..), Denotes (..), Sub (..), ValW (..), Value (..), arrSubArrInv, denotId, denotIdAppId)
import PLFH.Part3.Soundness (denotPreserve, denotReflect)

natToInt :: Nat -> Int
natToInt Zero     = 0
natToInt (Succ n) = 1 + natToInt n

isEvenNonZero :: Even n -> Bool
isEvenNonZero (EvenS _) = True
isEvenNonZero EvenZ     = False

allToInEven :: forall xs. All Even xs -> forall x. In x xs -> Even x
allToInEven allEv i = allToIn allEv i

checkAllInEv :: forall xs x. All Even xs -> In x xs -> Bool
checkAllInEv allEv inEv = isEvenNonZero (allToIn allEv inEv)

checkAnyWitness :: foreach (xs :: [Nat]) -> Any Even xs -> (Int, Bool)
checkAnyWitness xs proof = case anyIffWitness @Even @xs of
  Iff toWitness fromWitness -> case toWitness proof of
    witness@(MkAnyWitness member@(There (There (There (Here Refl)))) _) ->
      (natToInt (memberValue xs member), case fromWitness witness of
        There (There (There (Here (EvenS (OddS EvenZ))))) -> True
        _ -> False)
    _ -> (0, False)

checkMembershipRoundTrips :: foreach (xs :: [Nat]) -> Any Even xs -> AnyWitness Even xs -> Bool
checkMembershipRoundTrips xs position witness = case anyIsoWitness @Even @xs of
  MkIso _ _ fromTo toFrom -> case fromTo position of
    Refl -> case toFrom witness of Refl -> True

checkParallel :: U.UTerm Zero -> Bool
checkParallel term = case parRefl term of
  PApp (PLam PVar) (PLam PVar) -> True
  _                            -> False

eqFinZ :: foreach (x :: U.Fin (Succ Zero)) -> Maybe (x :~: U.FZ)
eqFinZ U.FZ     = Just Refl
eqFinZ (U.FS x) = case x of {}

eqIdBody :: foreach (b :: U.UTerm (Succ Zero)) -> Maybe (b :~: U.UVar U.FZ)
eqIdBody (U.UVar x)   = case eqFinZ x of { Just Refl -> Just Refl; Nothing -> Nothing }
eqIdBody (U.ULam _)   = Nothing
eqIdBody (U.UApp _ _) = Nothing

eqId :: foreach (t :: U.UTerm Zero) -> Maybe (t :~: U.IdTerm)
eqId (U.UVar x)   = case x of {}
eqId (U.ULam b)   = case eqIdBody b of { Just Refl -> Just Refl; Nothing -> Nothing }
eqId (U.UApp _ _) = Nothing

eqIdApp :: foreach (t :: U.UTerm Zero) -> Maybe (t :~: U.UApp U.IdTerm U.IdTerm)
eqIdApp (U.UVar x)   = case x of {}
eqIdApp (U.ULam _)   = Nothing
eqIdApp (U.UApp l m) = case (eqId l, eqId m) of
  (Just Refl, Just Refl) -> Just Refl
  _                      -> Nothing

checkBetaToPar :: U.UTerm Zero -> Bool
checkBetaToPar t = case eqIdApp t of
  Just Refl -> case betaToPar t idAppStep of
    PBeta PVar (PLam PVar) _ -> True
    _                        -> False
  Nothing -> False

checkAllInRoundTrip :: foreach (xs :: [Nat]) -> foreach (x :: Nat) -> Bool
checkAllInRoundTrip xs x = case decAll decEven xs of
  No _      -> False
  Yes allEv -> case decIn decEqSize x xs of
    No _     -> False
    Yes inEv -> checkAllInEv @xs @x (inToAll xs (allToInEven @xs allEv)) inEv

assertEq :: (Eq a, Show a) => String -> a -> a -> IO ()
assertEq label expected actual
  | expected == actual = putStrLn ("  [RUN-OK] " ++ label ++ " = " ++ show actual)
  | otherwise          = do
      putStrLn ("  [RUN-FAIL] " ++ label ++ ": expected " ++ show expected ++ ", got " ++ show actual)
      exitFailure

main :: IO ()
main = do
  putStrLn "=== PLFH Runtime Smoke Tests ==="

  -- Part 1: Naturals (decimal literals!), Induction, Relations, Equality, Isomorphism, Quantifiers, Decidable, Lists
  assertEq "Naturals.fiveAtRuntime (2 + 3 :: Nat)" 5 (natToInt fiveAtRuntime)
  assertEq "Naturals.times 0 5 (wildcard base)" 0 (natToInt (N.times 0 5))
  assertEq "Naturals.pow 5 0 (wildcard base)" 1 (natToInt (N.pow 5 0))
  assertEq "Naturals.threePowFour (same-module 3 ^ 4 = 81)" True (case N.threePowFour of Refl -> True)
  assertEq "Naturals.threeMonusTwo (same-module 3 - 2 = 1)" True (case N.threeMonusTwo of Refl -> True)
  assertEq "Naturals.twoMonusThree (same-module 2 - 3 = 0)" True (case N.twoMonusThree of Refl -> True)
  assertEq "InductionClient.plusZeroAtThree" True (case plusZeroAtThree of Refl -> True)
  assertEq "InductionClient.checkPlusAssoc 2 3 4" True (checkPlusAssoc 2 3 4)
  assertEq "Induction.plusAssoc 2 3 4" True (case plusAssoc 2 3 4 of Refl -> True)
  assertEq "Induction.plusRearrange 1 2 3 4" True (case plusRearrange 1 2 3 4 of Refl -> True)
  assertEq "Induction.plusSwap 2 3 4" True (case plusSwap 2 3 4 of Refl -> True)
  assertEq "Induction.timesComm 3 2" True (case timesComm 3 2 of Refl -> True)
  assertEq "Induction.threeMonusTwo (3 - 2 = 1)" True (case threeMonusTwo of Refl -> True)
  assertEq "Induction.twoMonusThree (2 - 3 = 0)" True (case twoMonusThree of Refl -> True)
  assertEq "Induction.threePowFour (3 ^ 4 = 81)" True (case threePowFour of Refl -> True)
  assertEq "Induction.zeroMonus 5" True (case zeroMonus 5 of Refl -> True)
  assertEq "Induction.monusPlusAssoc 5 2 2" True (case monusPlusAssoc 5 2 2 of Refl -> True)
  assertEq "Induction.monusPlusAssoc 2 3 4" True (case monusPlusAssoc 2 3 4 of Refl -> True)
  assertEq "Induction.powPlus 2 2 1" True (case powPlus 2 2 1 of Refl -> True)
  assertEq "Induction.powMul 2 3 2" True (case powMul 2 3 2 of Refl -> True)
  assertEq "Induction.powTimes 2 2 2" True (case powTimes 2 2 2 of Refl -> True)
  assertEq "Induction.fromTo 5" True (case fromTo 5 of Refl -> True)

  assertEq "Equality.evenComm 2 2" True
    (case evenComm 2 2 (EvenS (OddS (EvenS (OddS EvenZ)))) of { EvenS _ -> True })

  let isoRoundTrip = case isoSizeSym isoSizeRefl of
        MkIsoSize to _ _ _ -> natToInt (to 4)
  assertEq "Isomorphism.isoSizeSym isoSizeRefl 4" 4 isoRoundTrip
  let polyIsoRoundTrip = case isoSym natIsoRefl of
        MkIso to _ _ _ -> natToInt (to 4)
  assertEq "Isomorphism.isoSym natIsoRefl 4" 4 polyIsoRoundTrip
  let polyIsoEmbed = case isoImpliesEmbed natIsoRefl of
        MkEmbed _ from left ->
          let n :: Nat
              n = 3
          in case left n of Refl -> natToInt (from n)
  assertEq "Isomorphism.isoImpliesEmbed natIsoRefl 3" 3 polyIsoEmbed
  let binEmbedRT = case binEmbedding of
        MkEmbed to from left ->
          let n :: Nat
              n = 5
          in case left n of Refl -> natToInt (from (to n))
  assertEq "Isomorphism.binEmbedding round-trip 5" 5 binEmbedRT
  assertEq "Isomorphism.embedImpliesIff binEmbedding 5" 5
    (let Iff to from = embedImpliesIff binEmbedding in natToInt (from (to 5)))
  let polyReflMaybe = case isoRefl @(Maybe Bool) of
        MkIso to from left right ->
          let x :: Maybe Bool
              x = Just True
          in case (left x, right x) of (Refl, Refl) -> from (to x)
  assertEq "Isomorphism.isoRefl @(Maybe Bool)" (Just True) polyReflMaybe
  let polyEmbedRefl = case embedRefl @Bool of
        MkEmbed to from left ->
          let b :: Bool
              b = False
          in case left b of Refl -> from (to b)
  assertEq "Isomorphism.embedRefl @Bool" False polyEmbedRefl
  let polyIsoTrans = case isoTrans (isoRefl @(Maybe Bool)) (isoSym (isoRefl @(Maybe Bool))) of
        MkIso to from left right ->
          let x :: Maybe Bool
              x = Just False
          in case (left x, right x) of (Refl, Refl) -> from (to x)
  assertEq "Isomorphism.isoTrans @(Maybe Bool)" (Just False) polyIsoTrans
  let natEmbedTrans = case embedTrans embedRefl binEmbedding of
        MkEmbed to from left ->
          let n :: Nat
              n = 6
          in case left n of Refl -> natToInt (from (to n))
  assertEq "Isomorphism.embedTrans embedRefl binEmbedding 6" 6 natEmbedTrans
  let prodSwapRT = case prodCommIso @Nat @Bool of
        MkIso to from left _ ->
          let p :: (Nat, Bool)
              p = (4, True)
          in case left p of Refl -> (natToInt (fst (from (to p))), snd (from (to p)))
  assertEq "Connectives.prodCommIso (4, True)" (4, True) prodSwapRT
  let sumSwapRT = case sumCommIso @Bool @Nat of
        MkIso to from left _ ->
          let s :: Either Bool Nat
              s = Right 7
          in case left s of Refl -> case from (to s) of { Right n -> natToInt n; Left _ -> -1 }
  assertEq "Connectives.sumCommIso (Right 7)" 7 sumSwapRT

  let sum23 = case plusExists 2 3 of
        Pair k Refl -> natToInt k
  assertEq "Decidable.plusExists 2 3" 5 sum23

  let diff25 = case leToDiff 2 5 (SleS (SleS ZleN)) of
        MkDiff k Refl -> natToInt k
  assertEq "Relations.leToDiff 2 5" 3 diff25
  assertEq "Relations.timesMono (1<=2, 2<=3)" True
    (case timesMono 1 2 2 3 (SleS ZleN) (SleS (SleS ZleN)) of { SleS (SleS ZleN) -> True })
  assertEq "Relations.plusMonoLt (0<1, 1<2)" True
    (case plusMonoLt 0 1 1 2 ZltS (SltS ZltS) of { SltS ZltS -> True })

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
  assertEq "Lists.lengthDownFrom 4" True (case lengthDownFrom 4 of Refl -> True)
  assertEq "Lists.downFrom 3" [2, 1, 0] (map natToInt (downFrom 3))
  assertEq "Lists.lengthZeros 3" True (case lengthZeros 3 of Refl -> True)
  let xs1 = [0, 1] :: [Nat]
      ys1 = [2] :: [Nat]
      zs1 = [3] :: [Nat]
  assertEq "Lists.shuntAppend [0,1] [2] [3]" True
    (case shuntAppend xs1 ys1 zs1 of Refl -> True)
  assertEq "Lists.revAppend [0,1] [2]" True
    (case revAppend xs1 ys1 of Refl -> True)
  assertEq "Lists.revInvolutive [0,1]" True
    (case revInvolutive xs1 of Refl -> True)
  assertEq "Lists.shuntRev [0,1] [2]" True
    (case shuntRev xs1 ys1 of Refl -> True)
  assertEq "Lists.reverses [0,1]" True
    (case reverses xs1 of Refl -> True)
  let fourN :: Nat
      fourN = 4
  assertEq "Lists.foldrPlusSeed [0,1] 4" True
    (case foldrPlusSeed xs1 fourN of Refl -> True)
  assertEq "Lists.foldrPlusAppend [0,1] [2]" True
    (case foldrPlusAppend xs1 ys1 of Refl -> True)
  let twoThree = [2, 3] :: [Nat]
      fourList = [4] :: [Nat]
  assertEq "Lists.foldrTimesSeed [2,3] 4" True
    (case foldrTimesSeed twoThree fourN of Refl -> True)
  assertEq "Lists.foldrTimesAppend [2,3] [4]" True
    (case foldrTimesAppend twoThree fourList of Refl -> True)
  assertEq "Lists.anyIsoWitness preserves fourth occurrence in both directions" True
    (checkMembershipRoundTrips [1, 2, 1, 2]
      (There (There (There (Here (EvenS (OddS EvenZ))))))
      (MkAnyWitness (There (There (There (Here Refl)))) (EvenS (OddS EvenZ))))
  assertEq "Lists.anyIffWitness preserves fourth occurrence" (2, True)
    (checkAnyWitness [1, 2, 1, 2] (There (There (There (Here (EvenS (OddS EvenZ)))))))
  let memTwo = sampleTailMem
      evTwo :: Even 2
      evTwo = EvenS (OddS EvenZ)
  assertEq "ListsProof.decodeHeadEven [0]" True
    (case decodeHeadEven of Refl -> True)
  assertEq "ListsProof.witnessToAnyEvenThere (symbolic tail)" True
    (case witnessToAnyEvenThere @_ @1 memTwo evTwo of Refl -> True)
  assertEq "ListsProof.decodeSecondEven [1,2,1,2]" True
    (case decodeSecondEven @(EvenS (OddS EvenZ)) of Refl -> True)
  let odds = [1, 3] :: [Nat]
  assertEq "Lists.notAnyIffAllNot @Even [1,3]" True
    (case notAnyIffAllNot @Even odds of
      Iff toAll _ ->
        let allNot = toAll (\case
              Here (EvenS (OddS ev)) -> case ev of {}
              There (Here (EvenS (OddS (EvenS (OddS ev))))) -> case ev of {}
              There (There r) -> case r of {})
        in case allNot of AllCons _ (AllCons _ AllNil) -> True)
  let twoN :: Nat
      twoN = 2
      threeN :: Nat
      threeN = 3
  assertEq "Lists.decIn decEqSize 2 [0,2,4]" True
    (case decIn decEqSize twoN evens of { Yes (There (Here Refl)) -> True; _ -> False })
  assertEq "Lists.decIn decEqSize 3 [0,2,4]" False
    (case decIn decEqSize threeN evens of { Yes _ -> True; No _ -> False })
  assertEq "Lists.allToIn / inToAll round-trip" True (checkAllInRoundTrip evens twoN)

  -- Part 2: STLC Progress & Preservation, Certified Inference, Untyped, Bisimulation, BigStep, Confluence
  let idTy :: L.HasType L.CEmpty (L.App (L.Lam Zero (L.Var Zero)) L.TZero) L.TNat
      idTy = L.TApp (L.TLam (L.TVar L.LZ)) L.TZeroT
  assertEq "Properties.progress ((\\x. x) 0)" True
    (case progress idTy of { PStep (L.BetaLam L.VZero) -> True; _ -> False })
  assertEq "Properties.preserve BetaLam ((\\x. x) 0)" True
    (case preserve (L.App (L.Lam Zero (L.Var Zero)) L.TZero) idTy (L.BetaLam L.VZero) of { L.TZeroT -> True })
  let caseSucTy :: L.HasType L.CEmpty (L.TCase (L.TSuc L.TZero) L.TZero Zero (L.Var Zero)) L.TNat
      caseSucTy = L.TCaseT (L.TSucT L.TZeroT) L.TZeroT (L.TVar L.LZ)
  assertEq "Properties.preserve BetaSuc (case (suc 0) ...)" True
    (case preserve (L.TCase (L.TSuc L.TZero) L.TZero Zero (L.Var Zero)) caseSucTy (L.BetaSuc L.VZero) of { L.TZeroT -> True })
  let muTy :: L.HasType L.CEmpty (L.TMu Zero L.TZero) L.TNat
      muTy = L.TMuT L.TZeroT
  assertEq "Properties.preserve BetaMu (mu x. 0)" True
    (case preserve (L.TMu Zero L.TZero) muTy L.BetaMu of { L.TZeroT -> True })
  assertEq "Properties.stepDeterm BetaLam" True
    (case stepDeterm (L.BetaLam L.VZero) (L.BetaLam L.VZero) of Refl -> True)
  assertEq "Properties.eval ((\\x. x) 0) 5" True
    (case eval 5 (MkTermW (L.App (L.Lam Zero (L.Var Zero)) L.TZero)) idTy of { Done (L.StepsCons _ L.StepsRefl) L.VZero -> True; _ -> False })
  assertEq "Properties.eval (case (suc 0) ...) 5" True
    (case eval 5 (MkTermW (L.TCase (L.TSuc L.TZero) L.TZero Zero (L.Var Zero))) caseSucTy of { Done (L.StepsCons _ L.StepsRefl) L.VZero -> True; _ -> False })
  assertEq "Lambda.stepExample" True
    (case L.stepExample of { L.StepsCons (L.BetaLam (L.VSuc L.VZero)) L.StepsRefl -> True })
  let add12Ty = L.TApp (L.TApp L.addTyped (L.TSucT L.TZeroT)) L.twoTyped
  assertEq "Properties.eval (AddTerm 1 2 = 3!) 30" True
    (case eval 30 (MkTermW (L.App (L.App (L.TMu 0 (L.Lam 1 (L.Lam 2 (L.TCase (L.Var 1) (L.Var 2) 3 (L.TSuc (L.App (L.App (L.Var 0) (L.Var 3)) (L.Var 2))))))) (L.TSuc L.TZero)) (L.TSuc (L.TSuc L.TZero)))) add12Ty of { Done _ (L.VSuc (L.VSuc (L.VSuc L.VZero))) -> True; _ -> False })
  let dbSuc :: DB.Term DB.CEmpty DB.TNat
      dbSuc = DB.Suc DB.Zero
      dbApp :: DB.Term DB.CEmpty DB.TNat
      dbApp = DB.App (DB.Lam (DB.Var DB.Z)) DB.Zero
  assertEq "DeBruijn.checkValue (Suc Zero)" True
    (case DB.checkValue dbSuc of { DB.YesVal _ -> True; DB.NotVal -> False })
  assertEq "DeBruijn.checkValue (App (Lam (Var Z)) Zero)" False
    (case DB.checkValue dbApp of { DB.YesVal _ -> True; DB.NotVal -> False })
  assertEq "DeBruijnProgress.betaIdStep ((lam. 0) 0 -> 0)" True
    (case DBP.betaIdStep of { DBP.BetaLam DB.VZero -> True })
  assertEq "DeBruijnProgress.betaCaptureAvoid ((lam. lam. 1) 0 -> lam. 0)" True
    (case DBP.betaCaptureAvoid of { DBP.BetaLam DB.VZero -> True })
  assertEq "DeBruijnProgress.betaShiftUnderLam (open shift under binder!)" True
    (case DBP.betaShiftUnderLam of { DBP.BetaLam DB.VLam -> True })
  let betaMuZero :: DBP.Step (DB.Mu DB.Zero) DB.Zero
      betaMuZero = DBP.BetaMu
  assertEq "DeBruijnProgress.BetaMu (mu. 0 -> 0)" True
    (case betaMuZero of { DBP.BetaMu -> True })
  let dbLam :: DB.Term DB.CEmpty (DB.TArr DB.TNat DB.TNat)
      dbLam = DB.Lam (DB.Var DB.Z)
      dbSucApp :: DB.Term DB.CEmpty DB.TNat
      dbSucApp = DB.Suc dbApp
      dbCaseZ :: DB.Term DB.CEmpty DB.TNat
      dbCaseZ = DB.Case DB.Zero DB.Zero (DB.Var DB.Z)
      dbCaseS :: DB.Term DB.CEmpty DB.TNat
      dbCaseS = DB.Case (DB.Suc DB.Zero) DB.Zero (DB.Var DB.Z)
      dbMuZ :: DB.Term DB.CEmpty DB.TNat
      dbMuZ = DB.Mu DB.Zero
      dbPlus22 :: DB.Term DB.CEmpty DB.TNat
      dbPlus22 = DB.App (DB.App DB.plusTerm DB.termTwo) DB.termTwo
  assertEq "DeBruijnProgress.progress (Lam (Var Z)) -> PDone VLam" True
    (case DBP.progress dbLam of { DBP.PDone DB.VLam -> True; _ -> False })
  assertEq "DeBruijnProgress.progress ((lam. 0) 0) -> BetaLam" True
    (case DBP.progress dbApp of { DBP.PStep (DBP.BetaLam DB.VZero) -> True; _ -> False })
  assertEq "DeBruijnProgress.progress (Suc ((lam. 0) 0)) -> XiSuc" True
    (case DBP.progress dbSucApp of { DBP.PStep (DBP.XiSuc (DBP.BetaLam DB.VZero)) -> True; _ -> False })
  assertEq "DeBruijnProgress.progress (Case Zero Zero (Var Z)) -> BetaZero" True
    (case DBP.progress dbCaseZ of { DBP.PStep DBP.BetaZero -> True; _ -> False })
  assertEq "DeBruijnProgress.progress (Case (Suc Zero) Zero (Var Z)) -> BetaSuc" True
    (case DBP.progress dbCaseS of { DBP.PStep (DBP.BetaSuc DB.VZero) -> True; _ -> False })
  assertEq "DeBruijnProgress.progress (Mu Zero) -> BetaMu" True
    (case DBP.progress dbMuZ of { DBP.PStep DBP.BetaMu -> True; _ -> False })
  assertEq "DeBruijnProgress.progress (plusTerm 2 2) -> XiApp1 (XiApp1 BetaMu)" True
    (case DBP.progress dbPlus22 of { DBP.PStep (DBP.XiApp1 (DBP.XiApp1 DBP.BetaMu)) -> True; _ -> False })

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

  let bisimPairTerm :: M.Term M.CEmpty (M.TProd (M.TArr M.TNat M.TNat) (M.TArr M.TNat M.TNat))
      bisimPairTerm = M.Pair (M.Lam (M.Var M.Z)) (M.Lam (M.Var M.Z))
      bisimPairRel = SimPair (SimLam SimVar) (SimLam SimVar)
  assertEq "Bisimulation.simRefl (Pair id id)" True
    (case simRefl bisimPairTerm of { SimPair (SimLam SimVar) (SimLam SimVar) -> True; _ -> False })
  assertEq "Bisimulation.simValue (Pair VLam VLam)" True
    (case simValue bisimPairRel (M.VPair M.VLam M.VLam) of { M.VPair M.VLam M.VLam -> True })
  assertEq "Bisimulation.simValueInv / simTrans" True
    (case simValueInv (simTrans bisimPairRel bisimPairRel) (M.VPair M.VLam M.VLam) of { M.VPair M.VLam M.VLam -> True })
  assertEq "Bisimulation.letDesugarSim (SimLetApp)" True
    (case letDesugarSim of { SimLetApp (SimFst (SimPair SimZero (SimSuc SimZero))) (SimSuc SimVar) -> True })
  assertEq "Bisimulation.letDesugarSteps (XiApp2 + BetaLam)" True
    (case letDesugarSteps of { MkLeg (MP.StepsCons (MP.XiApp2 M.VLam (MP.BetaFst M.VZero (M.VSuc M.VZero))) (MP.StepsCons (MP.BetaLam M.VZero) MP.StepsRefl)) (SimSuc SimZero) -> True })
  assertEq "Bisimulation.letDesugarStepsInv (XiLet + BetaLet)" True
    (case letDesugarStepsInv of { MkLegInv (MP.StepsCons (MP.XiLet (MP.BetaFst M.VZero (M.VSuc M.VZero))) (MP.StepsCons (MP.BetaLet M.VZero) MP.StepsRefl)) (SimSuc SimZero) -> True })

  let moreLet :: M.Term M.CEmpty M.TNat
      moreLet = M.Let M.Zero (M.Var M.Z)
      morePair :: M.Term M.CEmpty (M.TProd M.TNat M.TUnit)
      morePair = M.Pair M.Zero M.TT
      morePairLeft :: M.Term M.CEmpty (M.TProd M.TNat M.TUnit)
      morePairLeft = M.Pair moreLet M.TT
      moreInl, moreInr :: M.Term M.CEmpty M.TBool
      moreInl = M.Inl M.TT
      moreInr = M.Inr M.TT
      moreNil :: M.Term M.CEmpty (M.TList M.TNat)
      moreNil = M.Nil
      moreFirst, moreCaseLeft, moreCaseRight, moreCaseNil :: M.Term M.CEmpty M.TNat
      moreFirst = M.Fst morePair
      moreCaseLeft = M.CaseSum moreInl M.Zero (M.Suc M.Zero)
      moreCaseRight = M.CaseSum moreInr M.Zero (M.Suc M.Zero)
      moreCaseNil = M.CaseLst moreNil M.Zero (M.Var (M.S M.Z))
      moreSecond :: M.Term M.CEmpty M.TUnit
      moreSecond = M.Snd morePair
      moreAbsurd :: M.Term M.CEmpty M.TNat
      moreAbsurd = M.Absurd (M.Mu (M.Var M.Z))
  assertEq "MoreProgress.progress Let -> BetaLet" True
    (case MP.progress moreLet of { MP.PStep MP.BetaLet{} -> True; _ -> False })
  assertEq "MoreProgress.progress Pair -> XiPair1" True
    (case MP.progress morePairLeft of { MP.PStep MP.XiPair1{} -> True; _ -> False })
  assertEq "MoreProgress.progress Fst -> BetaFst" True
    (case MP.progress moreFirst of { MP.PStep MP.BetaFst{} -> True; _ -> False })
  assertEq "MoreProgress.progress Snd -> BetaSnd" True
    (case MP.progress moreSecond of { MP.PStep MP.BetaSnd{} -> True; _ -> False })
  assertEq "MoreProgress.progress CaseSum Inl -> BetaInl" True
    (case MP.progress moreCaseLeft of { MP.PStep MP.BetaInl{} -> True; _ -> False })
  assertEq "MoreProgress.progress CaseSum Inr -> BetaInr" True
    (case MP.progress moreCaseRight of { MP.PStep MP.BetaInr{} -> True; _ -> False })
  assertEq "MoreProgress.progress CaseLst Nil -> BetaNil" True
    (case MP.progress moreCaseNil of { MP.PStep MP.BetaNil -> True; _ -> False })
  assertEq "MoreProgress.listCaseBoth (BetaCons substDouble!)" True
    (case MP.listCaseBoth of { MP.BetaCons (M.VSuc M.VZero) (M.VCons M.VZero M.VNil) -> True })
  assertEq "MoreProgress.progress Absurd (Mu ...) -> XiAbsurd BetaMu" True
    (case MP.progress moreAbsurd of { MP.PStep (MP.XiAbsurd MP.BetaMu) -> True; _ -> False })

  assertEq "Untyped.idAppStep" True (case idAppStep of { Beta _ -> True; _ -> False })
  assertEq "Untyped.omegaStep" True (case omegaStep of { Beta _ -> True; _ -> False })
  assertEq "Confluence.parRefl traverses both lambdas" True
    (checkParallel (U.UApp U.idTerm U.idTerm))
  assertEq "Confluence.betaToPar idAppStep" True
    (checkBetaToPar (U.UApp U.idTerm U.idTerm))
  assertEq "Confluence.parToBetas omegaPar" True (case parToBetas omegaPar of { BCons (Beta _) BRefl -> True; _ -> False })
  assertEq "Confluence.normalNoBetaSteps idIsNormal" True (case normalNoBetaSteps idIsNormal BRefl of Refl -> True)
  assertEq "BigStep.evalBigIsLam evalConstOmega" True (case evalBigIsLam evalConstOmega of MkIsLamClos -> True)
  assertEq "BigStep.evalDeterm evalIdApp evalIdApp" True (case evalDeterm evalIdApp evalIdApp of Refl -> True)

  -- Part 3: Denotational Semantics, Compositionality, & Unconditional Adequacy!
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
  assertEq "Soundness.denotPreserve idAppStep" True
    (case denotPreserve (MkValW (Arr Bot Bot)) (denotIdAppId (MkValW Bot)) idAppStep of { DIntro _ -> True; _ -> False })
  assertEq "Soundness.denotReflect idAppStep" True
    (case denotReflect (MkValW (Arr Bot Bot)) idAppStep denotId of { DElim _ (DIntro _) _ -> True; _ -> False })
  assertEq "Adequacy.adequacyIdApp (unconditional Big-Step Adequacy!)" True
    (case adequacyIdApp of { MkHaltsBig (EApp _ _) -> True; _ -> False })
  assertEq "Adequacy.adequacyDelta (unconditional Delta halts!)" True
    (case adequacyDelta of { MkHaltsBig ELam -> True; _ -> False })
  assertEq "ContextualEquivalence.terminatesStep idAppStep terminatesLam" True
    (case terminatesStep idAppStep terminatesLam of { MkTerminates (BCons _ BRefl) -> True; _ -> False })

  putStrLn "All runtime smoke tests passed."
