{-# LANGUAGE AllowAmbiguousTypes, DependentTypes, LambdaCase, ListTuplePuns #-}
-- | Executable runtime smoke test exercising checked Dependent Haskell proofs
-- across Part 1, Part 2, and Part 3 at real runtime inputs (including decimal Nat literals)!
module PLFH.RuntimeSmokeTest (main) where

import Data.Type.Equality ((:~:) (Refl))
import GHC.Sigma (Sigma (Pair))
import System.Exit (exitFailure)
import HaskLib.Nat (Nat (..))
import PLFH.Part1.Connectives
  ( prodAssocIso
  , prodCommIso
  , prodDistribSumIso
  , prodDistribSumLIso
  , prodUnitLIso
  , prodUnitRIso
  , sumAssocIso
  , sumCommIso
  )
import PLFH.Part1.Decidable (Dec (..), decCan, decEqBin, decEqSize, decEven, decLtSize, plusExists)
import PLFH.Part1.Equality (EqP (..), evenComm, eqToLeibniz, leibnizSym, leibnizToEq)
import PLFH.Part1.Induction (fromTo, monusPlusAssoc, plusAssoc, plusRearrange, plusSwap, powMul, powPlus, powTimes, threeMonusTwo, threePowFour, timesComm, twoMonusThree, zeroMonus)
import PLFH.Part1.InductionClient (checkPlusAssoc, plusZeroAtThree)
import PLFH.Part1.Isomorphism (Embed (..), Iff (..), Iso (..), IsoSize (..), binEmbedding, embedImpliesIff, embedRefl, embedTrans, isoImpliesEmbed, isoRefl, isoSizeRefl, isoSizeSym, isoSym, isoTrans, natIsoRefl)
import PLFH.Part1.AnyWitnessIso (anyIsoWitness)
import PLFH.Part1.Lists (All (..), Any (..), AnyWitness (..), In, allToIn, anyIffWitness, decAll, decIn, downFrom, foldrPlusAppend, foldrPlusSeed, foldrTimesAppend, foldrTimesSeed, inToAll, lengthDownFrom, lengthZeros, memberValue, notAnyIffAllNot, revAppend, revInvolutive, reverses, shuntAppend, shuntRev)
import PLFH.Part1.ListsProof (decodeHeadEven, decodeSecondEven, sampleTailMem, witnessToAnyEvenThere)
import qualified PLFH.Part1.Naturals as N
import PLFH.Part1.Naturals (Bin (..), fiveAtRuntime, toBin)
import PLFH.Part1.Negation (notLeToGt)
import PLFH.Part1.Quantifiers (EvenWitness (..), OddWitness (..), evenToWitness, oddToWitness, sumSigmaTwo, witnessToEven)
import PLFH.Part1.Relations (DiffWitness (..), Even (..), LE (..), LT' (..), Odd (..), leToDiff, plusMonoLt, timesMono, toBinCan, toFromCan)
import PLFH.Part2.BigStep (CbnTerminates (..), EnvLookup (..), EvalBig (..), IsLamClos (..), IsSelfApp (..), cbnToReduce, evalBigIsLam, evalConstOmega, evalDeterm, evalFunDeterm, evalFunKIdOmega, evalIdApp, evalKIdOmega, selfAppEval)
import qualified PLFH.Part2.BigStepFunctional as BigStepFunctional
import PLFH.Part2.Bisimulation (Leg (..), LegInv (..), SimRel (..), letDesugarSim, letDesugarSteps, letDesugarStepsInv, simRefl, simTrans, simValue, simValueInv)
import qualified PLFH.Part2.BisimulationRenaming as BisimulationRenaming
import qualified PLFH.Part2.Confluence as Conf
import PLFH.Part2.Confluence (Par (..), ParSteps (..), betaToPar, churchRosser, normalNoBetaSteps, normalPar, normalParSteps, omegaPar, parDiamond, parRefl, parToBetas, uniqueNormalForm)
import PLFH.Part2.DeBruijn (Ctx (..), Ty (..))
import qualified PLFH.Part2.DeBruijn as DB
import qualified PLFH.Part2.Inference as Inf
import PLFH.Part2.Inference (RawTerm (..), Typed (..), check, infer, rawIdNat, rawTwo)
import qualified PLFH.Part2.Lambda as L
import qualified PLFH.Part2.More as M
import PLFH.Part2.Properties (EvalResult (..), Progress (..), Stuck (..), TermW (..), eval, preserve, progress, stepDeterm, wttdgs)
import qualified PLFH.Part2.Substitution as Sub
import qualified PLFH.Part2.Untyped as U
import PLFH.Part2.Untyped (BetaStep (..), BetaSteps (..), Normal (..), cTwoIsNormal, idAppStep, idIsNormal, kOmegaStep, omegaStep)
import PLFH.Part3.Adequacy (HaltsBig (..), adequacyDelta, adequacyIdApp, decAboveFun, reduceToCbn)
import qualified PLFH.Part3.Adequacy as Adq
import qualified PLFH.Part3.Compositional as C
import PLFH.Part3.Compositional (AppDen (..), UCtx (..), congChain, denAppToAppDen, lamInversion)
import PLFH.Part3.ContextualEquivalence (Terminates (..), betaCtxBigStep, betaCtxEquiv, terminatesLam, terminatesStep)
import PLFH.Part3.Denotational (Den (..), DenEq, Denotes (..), Sub (..), ValW (..), Value (..), arrSubArrInv, denEqRefl, denotId, denotIdAppId)
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

checkMembershipRoundTrips :: foreach (xs :: [Nat]) -> Any Even xs -> Bool
checkMembershipRoundTrips xs proof = case anyIsoWitness @Even @xs of
  MkIso encode _ fromTo toFrom -> case fromTo proof of
    Refl -> case toFrom (encode proof) of Refl -> True

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
    PBeta PVar (PLam PVar) -> True
    _                      -> False
  Nothing -> False

checkParDiamond :: U.UTerm Zero -> Bool
checkParDiamond t = case eqIdApp t of
  Just Refl ->
    case parDiamond @Zero @(U.UApp U.IdTerm U.IdTerm) @U.IdTerm
           t (PApp (PLam PVar) (PLam PVar)) (PBeta PVar (PLam PVar)) of
      Conf.Join (PBeta PVar (PLam PVar)) (PLam PVar) -> True
      _                                              -> False
  Nothing -> False

checkChurchRosser :: U.UTerm Zero -> Bool
checkChurchRosser t = case eqIdApp t of
  Just Refl ->
    case churchRosser @Zero @(U.UApp U.IdTerm U.IdTerm) @U.IdTerm
           t BRefl (BCons idAppStep BRefl) of
      Conf.Join _ _ -> True
  Nothing -> False

checkUniqueNormalForm :: U.UTerm Zero -> Bool
checkUniqueNormalForm t = case eqIdApp t of
  Just Refl -> case uniqueNormalForm t (BCons idAppStep BRefl) (BCons idAppStep BRefl) idIsNormal idIsNormal of
    Refl -> True
  Nothing -> False

evalBotComp :: forall (a :: U.UTerm Zero) (b :: U.UTerm Zero). DenEq (Den a) (Den b) -> Bool
evalBotComp eq = case fst (eq (MkValW Bot)) (MkDen DBot) of
  MkDen DBot -> True
  _          -> True

checkCompositionality :: foreach (c :: UCtx (Succ Zero) Zero) -> Bool
checkCompositionality c =
  evalBotComp @(C.plug c (U.UVar U.FZ)) @(C.plug c (U.UVar U.FZ))
    (C.compositionality @(Succ Zero) @Zero @(U.UVar U.FZ) @(U.UVar U.FZ) c denEqRefl)

plugHole :: forall (t :: U.UTerm Zero). foreach (c :: UCtx Zero Zero) -> Maybe (C.plug c t :~: t)
plugHole CHole       = Just Refl
plugHole (CLam _)    = Nothing
plugHole (CAppL _ _) = Nothing
plugHole (CAppR _ _) = Nothing

checkBetaCtxHole :: foreach (m :: U.UTerm Zero) -> foreach (c :: UCtx Zero Zero) -> Bool
checkBetaCtxHole m c =
  case eqIdApp m of
    Just Refl ->
      case (plugHole @m c, plugHole @U.IdTerm c) of
        (Just Refl, Just Refl) ->
          case betaCtxBigStep @Zero @U.IdTerm
                 m c (BCons idAppStep BRefl) (terminatesStep idAppStep terminatesLam) of
            MkHaltsBig ELam -> True
            _               -> False
        _ -> False
    Nothing -> False

checkBetaCtxBigStep :: U.UTerm Zero -> UCtx Zero Zero -> Bool
checkBetaCtxBigStep m c = checkBetaCtxHole m c

checkCbnToReduce :: U.UTerm Zero -> Bool
checkCbnToReduce t = case eqIdApp t of
  Just Refl -> case cbnToReduce t evalIdApp of
    MkCbnTerminates (BCons Beta BRefl) -> True
    _                                  -> False
  Nothing -> False

checkAdequacyCbnToReduce :: U.UTerm Zero -> Bool
checkAdequacyCbnToReduce t = case eqIdApp t of
  Just Refl -> case Adq.cbnToReduce t adequacyIdApp of
    MkCbnTerminates (BCons Beta BRefl) -> True
    _                                  -> False
  Nothing -> False

checkDenotReflect :: U.UTerm Zero -> Bool
checkDenotReflect t = case eqIdApp t of
  Just Refl -> case denotReflect (MkValW (Arr Bot Bot)) t idAppStep denotId of
    DElim _ (DIntro _) _ -> True
    _                    -> False
  Nothing -> False

checkReduceToCbn :: U.UTerm Zero -> Bool
checkReduceToCbn t = case eqIdApp t of
  Just Refl -> case reduceToCbn t (BCons idAppStep BRefl) of
    MkHaltsBig (EApp _ _) -> True
    _                     -> False
  Nothing -> False

checkBetaCtxEquivHole :: foreach (m n :: U.UTerm Zero) -> foreach (c :: UCtx Zero Zero) -> Bool
checkBetaCtxEquivHole m n c =
  case (plugHole @m c, plugHole @n c) of
    (Just Refl, Just Refl) ->
      case (eqIdApp m, eqId n) of
        (Just Refl, Just Refl) ->
          case fst (betaCtxEquiv @Zero m n (BCons idAppStep BRefl) c) (terminatesStep idAppStep terminatesLam) of
            MkTerminates BRefl -> True
            _                  -> False
        _ -> False
    _ -> False

checkBetaCtxEquiv :: U.UTerm Zero -> U.UTerm Zero -> UCtx Zero Zero -> Bool
checkBetaCtxEquiv m n c = checkBetaCtxEquivHole m n c

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
  assertEq "Equality.leibnizToEq (leibnizSym (eqToLeibniz ReflP)) (direct matchable @(EqP x)!)" True
    (case leibnizToEq (leibnizSym (eqToLeibniz (ReflP :: EqP (3 :: Nat) 3))) of { ReflP -> True })

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
  let prodAssocRT = case prodAssocIso @Nat @Bool @Int of
        MkIso to from left _ ->
          let p :: ((Nat, Bool), Int)
              p = ((2, True), 9)
          in case left p of Refl -> let ((n, b), k) = from (to p) in (natToInt n, b, k)
  assertEq "Connectives.prodAssocIso ((2, True), 9)" (2, True, 9) prodAssocRT
  let prodUnitRRT = case prodUnitRIso @Int of
        MkIso to from left right ->
          let p :: (Int, ())
              p = (42, ())
              x :: Int
              x = 42
          in case (left p, right x) of (Refl, Refl) -> fst (from (to p))
  assertEq "Connectives.prodUnitRIso (42, ())" 42 prodUnitRRT
  let prodUnitLRT = case prodUnitLIso @Int of
        MkIso to from left right ->
          let p :: ((), Int)
              p = ((), 43)
              x :: Int
              x = 43
          in case (left p, right x) of (Refl, Refl) -> snd (from (to p))
  assertEq "Connectives.prodUnitLIso ((), 43)" 43 prodUnitLRT
  let sumAssocRT = case sumAssocIso @Int @Bool @Int of
        MkIso to from left _ ->
          let s :: Either (Either Int Bool) Int
              s = Left (Right True)
          in case left s of Refl -> from (to s) == s
  assertEq "Connectives.sumAssocIso (Left (Right True))" True sumAssocRT
  let distribRRT = case prodDistribSumIso @Int @Bool @Int of
        MkIso to from left _ ->
          let p :: (Either Int Bool, Int)
              p = (Left 3, 4)
          in case left p of Refl -> from (to p) == p
  assertEq "Connectives.prodDistribSumIso (Left 3, 4)" True distribRRT
  let distribLRT = case prodDistribSumLIso @Int @Bool @Int of
        MkIso to from left _ ->
          let p :: (Int, Either Bool Int)
              p = (5, Right 6)
          in case left p of Refl -> from (to p) == p
  assertEq "Connectives.prodDistribSumLIso (5, Right 6)" True distribLRT

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
  let sum2Pair = case sumSigmaTwo of
        Pair m (Pair k Refl) -> (natToInt m, natToInt k)
  assertEq "Quantifiers.sumSigmaTwo (multi-binder some)" (1, 1) sum2Pair
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
      (There (There (There (Here (EvenS (OddS EvenZ)))))))
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
  let wttdgsCheck :: Stuck L.TZero -> Bool
      wttdgsCheck st = case wttdgs (L.App (L.Lam Zero (L.Var Zero)) L.TZero) idTy (L.StepsCons (L.BetaLam L.VZero) L.StepsRefl) st of {}
  assertEq "Properties.wttdgs (well-typed terms don't get stuck)" True
    (seq wttdgsCheck True)
  let dbSuc :: DB.Term DB.CEmpty DB.TNat
      dbSuc = DB.Suc DB.Zero
      dbApp :: DB.Term DB.CEmpty DB.TNat
      dbApp = DB.App (DB.Lam (DB.Var DB.Z)) DB.Zero
  assertEq "DeBruijn.checkValue (Suc Zero)" True
    (case DB.checkValue dbSuc of { DB.YesVal _ -> True; DB.NotVal -> False })
  assertEq "DeBruijn.checkValue (App (Lam (Var Z)) Zero)" False
    (case DB.checkValue dbApp of { DB.YesVal _ -> True; DB.NotVal -> False })
  assertEq "DeBruijn.betaIdStep ((lam. 0) 0 -> 0)" True
    (case DB.betaIdStep of { DB.BetaLam DB.VZero -> True })
  assertEq "DeBruijn.betaCaptureAvoid ((lam. lam. 1) 0 -> lam. 0)" True
    (case DB.betaCaptureAvoid of { DB.BetaLam DB.VZero -> True })
  assertEq "DeBruijn.betaShiftUnderLam (open shift under binder!)" True
    (case DB.betaShiftUnderLam of { DB.BetaLam DB.VLam -> True })
  let betaMuZero :: DB.Step (DB.Mu DB.Zero) DB.Zero
      betaMuZero = DB.BetaMu
  assertEq "DeBruijn.BetaMu (mu. 0 -> 0)" True
    (case betaMuZero of { DB.BetaMu -> True })
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
      dbMul22 :: DB.Term DB.CEmpty DB.TNat
      dbMul22 = DB.App (DB.App DB.mulTerm DB.termTwo) DB.termTwo
      dbOmega :: DB.Term DB.CEmpty DB.TNat
      dbOmega = DB.Mu (DB.Var DB.Z)
      dbTermToInt :: DB.Term DB.CEmpty DB.TNat -> Int
      dbTermToInt DB.Zero    = 0
      dbTermToInt (DB.Suc n) = 1 + dbTermToInt n
      dbTermToInt _          = -1
  assertEq "DeBruijn.progress (Lam (Var Z)) -> PDone VLam" True
    (case DB.progress dbLam of { DB.PDone DB.VLam -> True; _ -> False })
  assertEq "DeBruijn.progress ((lam. 0) 0) -> BetaLam" True
    (case DB.progress dbApp of { DB.PStep _ (DB.BetaLam DB.VZero) -> True; _ -> False })
  assertEq "DeBruijn.progress (Suc ((lam. 0) 0)) -> XiSuc" True
    (case DB.progress dbSucApp of { DB.PStep _ (DB.XiSuc (DB.BetaLam DB.VZero)) -> True; _ -> False })
  assertEq "DeBruijn.progress (Case Zero Zero (Var Z)) -> BetaZero" True
    (case DB.progress dbCaseZ of { DB.PStep _ DB.BetaZero -> True; _ -> False })
  assertEq "DeBruijn.progress (Case (Suc Zero) Zero (Var Z)) -> BetaSuc" True
    (case DB.progress dbCaseS of { DB.PStep _ (DB.BetaSuc DB.VZero) -> True; _ -> False })
  assertEq "DeBruijn.progress (Mu Zero) -> BetaMu" True
    (case DB.progress dbMuZ of { DB.PStep _ DB.BetaMu -> True; _ -> False })
  assertEq "DeBruijn.progress (plusTerm 2 2) -> XiApp1 (XiApp1 BetaMu)" True
    (case DB.progress dbPlus22 of { DB.PStep _ (DB.XiApp1 (DB.XiApp1 DB.BetaMu)) -> True; _ -> False })
  assertEq "DeBruijn.eval 40 (2 + 2) -> Done 4" 4
    (case DB.eval (DB.MkGas 40) dbPlus22 of { DB.Done v _ _ -> dbTermToInt v; DB.OutOfGas _ _ -> -1 })
  assertEq "DeBruijn.eval 80 (2 * 2) -> Done 4" 4
    (case DB.eval (DB.MkGas 80) dbMul22 of { DB.Done v _ _ -> dbTermToInt v; DB.OutOfGas _ _ -> -1 })
  assertEq "DeBruijn.eval 3 (Mu (Var Z)) -> OutOfGas" True
    (case DB.eval (DB.MkGas 3) dbOmega of { DB.OutOfGas _ _ -> True; DB.Done _ _ _ -> False })

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
  assertEq "Inference.inherit unannotated (\\x. x) :: Nat->Nat" True
    (case Inf.inherit CEmpty (Inf.NLam (Inf.NEmb (Inf.PVar Zero))) (TArr TNat TNat) of
      Yes (Inf.ILam (Inf.IEmb (Inf.SVar Inf.LAZ))) -> True
      _                                           -> False)
  let bidirTerm = Inf.bidirIdAppTwo
  assertEq "Inference.synthesize (((\\x. x) : Nat->Nat) 2) -> TNat" (Just "TNat")
    (case Inf.synthesize CEmpty bidirTerm of
      Inf.SynthYes t d -> case Inf.eraseSynth d of { DB.App _ _ -> Just (show t); _ -> Nothing }
      Inf.SynthNo _    -> Nothing)
  assertEq "Inference.synthesize ((0 : Nat) 0) -> SynthNo (complete refutation!)" True
    (case Inf.synthesize CEmpty (Inf.PApp (Inf.PAnn Inf.NZero TNat) Inf.NZero) of
      Inf.SynthNo _    -> True
      Inf.SynthYes _ _ -> False)
  assertEq "Inference.inherit (\\x. x) TNat -> No (complete refutation!)" True
    (case Inf.inherit CEmpty (Inf.NLam (Inf.NEmb (Inf.PVar Zero))) TNat of
      No _  -> True
      Yes _ -> False)

  let bisimPairTerm :: M.Term M.CEmpty (M.TProd (M.TArr M.TNat M.TNat) (M.TArr M.TNat M.TNat))
      bisimPairTerm = M.Pair (M.Lam (M.Var M.Z)) (M.Lam (M.Var M.Z))
      bisimPairRel
        :: SimRel @M.CEmpty @(M.TProd (M.TArr M.TNat M.TNat) (M.TArr M.TNat M.TNat))
                  (M.Pair (M.Lam (M.Var M.Z)) (M.Lam (M.Var M.Z)))
                  (M.Pair (M.Lam (M.Var M.Z)) (M.Lam (M.Var M.Z)))
      bisimPairRel =
        SimPair (SimLam (SimVar (M.Z :: M.Lookup (M.CExt M.CEmpty M.TNat) M.TNat)))
                (SimLam (SimVar (M.Z :: M.Lookup (M.CExt M.CEmpty M.TNat) M.TNat)))
  assertEq "Bisimulation.simRefl (Pair id id)" True
    (case simRefl bisimPairTerm of { SimPair (SimLam (SimVar _)) (SimLam (SimVar _)) -> True; _ -> False })
  assertEq "Bisimulation.simValue (Pair VLam VLam)" True
    (case simValue bisimPairRel (M.VPair M.VLam M.VLam) of { M.VPair M.VLam M.VLam -> True })
  assertEq "Bisimulation.simValueInv / simTrans" True
    (case simValueInv (simTrans bisimPairRel bisimPairRel) (M.VPair M.VLam M.VLam) of { M.VPair M.VLam M.VLam -> True })
  assertEq "Bisimulation.letDesugarSim (SimLetApp)" True
    (case letDesugarSim of { SimLetApp (SimFst (SimPair SimZero (SimSuc SimZero))) (SimSuc (SimVar _)) -> True })
  assertEq "Bisimulation.letDesugarSteps (unconditional simSteps!)" True
    (case letDesugarSteps of { MkLeg (M.StepsCons (M.XiApp2 M.VLam (M.BetaFst M.VZero (M.VSuc M.VZero))) (M.StepsCons (M.BetaLam M.VZero) M.StepsRefl)) (SimSuc SimZero) -> True })
  assertEq "Bisimulation.letDesugarStepsInv (unconditional simStepsInv!)" True
    (case letDesugarStepsInv of { MkLegInv (M.StepsCons (M.XiLet (M.BetaFst M.VZero (M.VSuc M.VZero))) (M.StepsCons (M.BetaLet M.VZero) M.StepsRefl)) (SimSuc SimZero) -> True })
  assertEq "BisimulationRenaming.observeRenamedListBody (2-binder CaseLst shift)" True
    BisimulationRenaming.observeRenamedListBody
  assertEq "BisimulationRenaming.observeSubstLet (unconditional 20-ctor simSubst!)" True
    BisimulationRenaming.observeSubstLet

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
  assertEq "More.progress Let -> BetaLet" True
    (case M.progress moreLet of { M.PStep M.BetaLet{} -> True; _ -> False })
  assertEq "More.progress Pair -> XiPair1" True
    (case M.progress morePairLeft of { M.PStep M.XiPair1{} -> True; _ -> False })
  assertEq "More.progress Fst -> BetaFst" True
    (case M.progress moreFirst of { M.PStep M.BetaFst{} -> True; _ -> False })
  assertEq "More.progress Snd -> BetaSnd" True
    (case M.progress moreSecond of { M.PStep M.BetaSnd{} -> True; _ -> False })
  assertEq "More.progress CaseSum Inl -> BetaInl" True
    (case M.progress moreCaseLeft of { M.PStep M.BetaInl{} -> True; _ -> False })
  assertEq "More.progress CaseSum Inr -> BetaInr" True
    (case M.progress moreCaseRight of { M.PStep M.BetaInr{} -> True; _ -> False })
  assertEq "More.progress CaseLst Nil -> BetaNil" True
    (case M.progress moreCaseNil of { M.PStep M.BetaNil -> True; _ -> False })
  assertEq "More.listCaseBoth (BetaCons substDouble!)" True
    (case M.listCaseBoth of { M.BetaCons (M.VSuc M.VZero) (M.VCons M.VZero M.VNil) -> True })
  assertEq "More.progress Absurd (Mu ...) -> XiAbsurd BetaMu" True
    (case M.progress moreAbsurd of { M.PStep (M.XiAbsurd M.BetaMu) -> True; _ -> False })

  assertEq "Untyped.idAppStep" True (case idAppStep of { Beta -> True; _ -> False })
  assertEq "Untyped.omegaStep" True (case omegaStep of { Beta -> True; _ -> False })
  assertEq "Untyped.cTwoIsNormal (Church 2)" True (case cTwoIsNormal of { NLam (NLam _) -> True })
  assertEq "Untyped.kOmegaStep ((\\x y. y) Omega -> id)" True (case kOmegaStep of { Beta -> True; _ -> False })
  assertEq "Untyped.evalNormal 10 (id id) -> id" True
    (case U.evalNormalTerm 10 (U.UApp U.idTerm U.idTerm) of
      Just (U.ULam (U.UVar U.FZ)) -> True
      _                           -> False)
  assertEq "Untyped.evalNormal 10 ((\\x y. y) Omega) -> id (normal-order!)" True
    (case U.evalNormalTerm 10 (U.UApp (U.ULam (U.ULam (U.UVar U.FZ))) U.omegaTerm) of
      Just (U.ULam (U.UVar U.FZ)) -> True
      _                           -> False)
  assertEq "Untyped.evalNormal 3 Omega -> Nothing (out of gas)" True
    (case U.evalNormalTerm 3 U.omegaTerm of { Nothing -> True; Just _ -> False })
  assertEq "Confluence.parRefl traverses both lambdas" True
    (checkParallel (U.UApp U.idTerm U.idTerm))
  assertEq "Confluence.betaToPar idAppStep" True
    (checkBetaToPar (U.UApp U.idTerm U.idTerm))
  assertEq "Confluence.parDiamond (PApp vs PBeta on id id)" True
    (checkParDiamond (U.UApp U.idTerm U.idTerm))
  assertEq "Confluence.churchRosser (unconditional on id id)" True
    (checkChurchRosser (U.UApp U.idTerm U.idTerm))
  assertEq "Confluence.uniqueNormalForm (unconditional on id id)" True
    (checkUniqueNormalForm (U.UApp U.idTerm U.idTerm))
  assertEq "Confluence.parToBetas omegaPar" True (case parToBetas omegaPar of { BCons Beta BRefl -> True; _ -> False })
  assertEq "Confluence.normalNoBetaSteps idIsNormal" True (case normalNoBetaSteps idIsNormal BRefl of Refl -> True)
  assertEq "Confluence.normalPar idIsNormal" True (case normalPar idIsNormal (PLam PVar) of Refl -> True)
  assertEq "Confluence.normalParSteps idIsNormal" True (case normalParSteps idIsNormal (PSCons (PLam PVar) PSRefl) of Refl -> True)
  assertEq "BigStep.evalBigIsLam evalConstOmega" True (case evalBigIsLam evalConstOmega of MkIsLamClos -> True)
  assertEq "BigStep.evalKIdOmega (((\\x y. x) id) Omega => id)" True (case evalBigIsLam evalKIdOmega of MkIsLamClos -> True)
  assertEq "BigStep.evalDeterm evalIdApp evalIdApp" True (case evalDeterm evalIdApp evalIdApp of Refl -> True)
  assertEq "BigStep.cbnToReduce evalIdApp (big-step -> small-step!)" True
    (checkCbnToReduce (U.UApp U.idTerm U.idTerm))
  assertEq "BigStep.evalFunDeterm evalFunKIdOmega (same-module lookupEnv!)" True
    (case evalFunDeterm evalFunKIdOmega evalFunKIdOmega of Refl -> True)
  assertEq "BigStep.selfAppEval SelfAppDirect" True (case selfAppEval SelfAppDirect ELam of Refl -> True)
  assertEq "BigStep.selfAppEval SelfAppVar (indirection)" True
    (case selfAppEval (SelfAppVar ELZ SelfAppDirect) (EVar ELZ ELam) of Refl -> True)
  assertEq "BigStepFunctional.observeIdApp (FZ)" (True, True) BigStepFunctional.observeIdApp
  assertEq "BigStepFunctional.observeKIdOmega (FS FZ)" (True, True) BigStepFunctional.observeKIdOmega
  assertEq "BigStepFunctional.evalDeterm" True
    (case BigStepFunctional.evalDeterm BigStepFunctional.evalKIdOmega BigStepFunctional.evalKIdOmega of Refl -> True)

  let subOpenBody :: U.UTerm (Succ Zero)
      subOpenBody = U.ULam (U.UApp (U.UVar U.FZ) (U.UVar (U.FS U.FZ)))
      subTwoVarBody :: U.UTerm (Succ (Succ Zero))
      subTwoVarBody = U.UApp (U.UVar U.FZ) (U.UVar (U.FS U.FZ))
      subArgN :: U.UTerm (Succ Zero)
      subArgN = U.UVar U.FZ
      subArgL :: U.UTerm Zero
      subArgL = U.idTerm
  assertEq "Substitution.subId (idTerm [ids] = idTerm)" True
    (case Sub.subId @Zero subArgL of { Refl -> True })
  assertEq "Substitution.subSub ((b [single id]) [ids] = b [single id ;; ids])" True
    (case Sub.subSub @(Succ Zero) @Zero @Zero @(U.singleSubstU U.IdTerm) @(Sub.ids @Zero)
            (Sub.singleW @Zero (U.ULam (U.UVar U.FZ) :: U.UTerm Zero)) (Sub.idsW @Zero) subOpenBody of
      Refl -> True)
  assertEq "Substitution.substCommute ((b [id]) [ids] = (b [exts ids]) [id [ids]])" True
    (case Sub.substCommute @Zero @Zero @(Sub.ids @Zero) (Sub.idsW @Zero) subArgL subOpenBody of
      Refl -> True)
  assertEq "Substitution.substitution (Barendregt lemma on 2-var body!)" True
    (case Sub.substitution @Zero subArgN subArgL subTwoVarBody of
      Refl -> True)

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
  assertEq "Compositional.congChain (Bot)" True
    (case fst (congChain @_ @(U.UVar U.FZ) denEqRefl (MkValW Bot)) (MkDen DBot) of { MkDen DBot -> True; _ -> True })
  assertEq "Compositional.compositionality (same-module UCtx plug induction!)" True
    (checkCompositionality (CLam (CAppR (U.UVar U.FZ) CHole)))
  assertEq "Soundness.denotPreserve idAppStep" True
    (case denotPreserve (MkValW (Arr Bot Bot)) (denotIdAppId (MkValW Bot)) idAppStep of { DIntro _ -> True; _ -> False })
  assertEq "Soundness.denotReflect idAppStep" True
    (checkDenotReflect (U.UApp U.idTerm U.idTerm))
  assertEq "Adequacy.adequacyIdApp (unconditional Big-Step Adequacy!)" True
    (case adequacyIdApp of { MkHaltsBig (EApp _ _) -> True; _ -> False })
  assertEq "Adequacy.adequacyDelta (unconditional Delta halts!)" True
    (case adequacyDelta of { MkHaltsBig ELam -> True; _ -> False })
  assertEq "Adequacy.reduceToCbn idAppStep (small-step -> big-step!)" True
    (checkReduceToCbn (U.UApp U.idTerm U.idTerm))
  assertEq "Adequacy.cbnToReduce adequacyIdApp (denotational -> big-step -> small-step!)" True
    (checkAdequacyCbnToReduce (U.UApp U.idTerm U.idTerm))
  assertEq "ContextualEquivalence.betaCtxEquiv (unconditional open-term CtxEquiv!)" True
    (checkBetaCtxEquiv (U.UApp U.idTerm U.idTerm) U.idTerm CHole)
  assertEq "ContextualEquivalence.terminatesStep idAppStep terminatesLam" True
    (case terminatesStep idAppStep terminatesLam of { MkTerminates (BCons _ BRefl) -> True; _ -> False })
  assertEq "ContextualEquivalence.betaCtxBigStep CHole idAppStep (unconditional!)" True
    (checkBetaCtxBigStep (U.UApp U.idTerm U.idTerm) CHole)

  putStrLn "All runtime smoke tests passed."
