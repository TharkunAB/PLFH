-- Generated from content/part1/Decidable.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DependentTypes, ListTuplePuns #-}
{-# LINE 31 "content/part1/Decidable.md" #-}
module PLFH.Part1.Decidable
  ( Not
  , leBool
  , tBool
  , leBoolToLE
  , leToLeBool
  , Dec (..)
  , eraseDec
  , toWitness
  , fromWitness
  , decNot
  , decAnd
  , decOr
  , decImp
  , decIff
  , zeroNeqSucc
  , decEqNat
  , decLeNat
  , decLtNat
  , decEven
  , decOdd
  , decEqBin
  , decOne
  , decCan
  , Reflects (..)
  , reflectsToDec
  , Sigma (..)
  , NatWitness
  , mkNatWitness
  , plusExists
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void, absurd)
import GHC.Sigma (Sigma (Pair))
import Data.Nat.Dependent (Nat (..), minus, plus)
import PLFH.Part1.Induction (cong)
import PLFH.Part1.Isomorphism (Iff (..))
import PLFH.Part1.Naturals (Bin (..))
import PLFH.Part1.Negation (Not)
import PLFH.Part1.Relations (Can (..), Even (..), LE (..), LT' (..), Odd (..), One (..), invSleS)

{-# LINE 85 "content/part1/Decidable.md" #-}
-- | Test whether a natural number is zero.
isZeroNat :: Nat -> Bool
isZeroNat Zero     = True
isZeroNat (Succ _) = False

-- | Boolean less-than-or-equal test (`_≤ᵇ_`), defined via truncated subtraction.
leBool :: Nat -> Nat -> Bool
leBool Zero     _ = True
leBool (Succ m) n = isZeroNat (minus (Succ m) n)

-- | Lift a `Bool` to a proposition (`T` in PLFA) via term-to-`Type` large elimination.
tBool :: Bool -> Type
tBool True  = type ()
tBool False = type Void

-- | Soundness helper over `isZeroNat (minus m n)`.
minusZeroToLE :: foreach (m n :: Nat) -> tBool (isZeroNat (minus m n)) -> LE m n
minusZeroToLE Zero     _        () = ZleN
minusZeroToLE (Succ _) Zero     v  = absurd v
minusZeroToLE (Succ m) (Succ n) t  = SleS (minusZeroToLE m n t)

-- | Soundness of `leBool`: if `leBool m n` is `True`, then `LE m n` holds (`≤ᵇ→≤`).
leBoolToLE :: foreach (m n :: Nat) -> tBool (leBool m n) -> LE m n
leBoolToLE Zero     _ () = ZleN
leBoolToLE (Succ m) n t  = minusZeroToLE (Succ m) n t

-- | Completeness helper over `isZeroNat (minus m n)`.
leToMinusZero :: foreach (m n :: Nat) -> LE m n -> tBool (isZeroNat (minus m n))
leToMinusZero Zero     _        ZleN     = ()
leToMinusZero (Succ m) (Succ n) (SleS p) = leToMinusZero m n p

-- | Completeness of `leBool`: if `LE m n` holds, then `leBool m n` is `True` (`≤→≤ᵇ`).
leToLeBool :: foreach (m n :: Nat) -> LE m n -> tBool (leBool m n)
leToLeBool Zero     _ ZleN = ()
leToLeBool (Succ m) n p    = leToMinusZero (Succ m) n p

{-# LINE 132 "content/part1/Decidable.md" #-}
-- | Peano's postulate: Zero is never equal to any successor.
zeroNeqSucc :: Not (Zero :~: Succ n)
zeroNeqSucc eq = case eq of {}

{-# LINE 145 "content/part1/Decidable.md" #-}
-- | Evidence that a proposition `p` is decidable.
data Dec (p :: Type) where
  Yes :: p     -> Dec p
  No  :: Not p -> Dec p

-- | Erase a decision to its underlying `Bool` (`⌊_⌋`).
eraseDec :: Dec p -> Bool
eraseDec (Yes _) = True
eraseDec (No  _) = False

-- | Extract evidence `p` when `eraseDec d` computes to `True` (`toWitness`).
toWitness :: foreach (d :: Dec p) -> tBool (eraseDec d) -> p
toWitness d = case d of
  Yes p -> \_ -> p
  No  _ -> \v -> absurd v

-- | Witness that `eraseDec d` is `True` whenever `p` holds (`fromWitness`).
fromWitness :: foreach (d :: Dec p) -> p -> tBool (eraseDec d)
fromWitness d = case d of
  Yes _  -> \_ -> ()
  No  np -> \p -> np p

{-# LINE 179 "content/part1/Decidable.md" #-}
-- | Decidable propositions are closed under negation, conjunction, disjunction,
-- implication, and bi-implication.
decNot :: Dec p -> Dec (Not p)
decNot (Yes p)  = No (\np -> np p)
decNot (No  np) = Yes np

decAnd :: Dec p -> Dec q -> Dec (p, q)
decAnd (Yes p) (Yes q) = Yes (p, q)
decAnd (No np) _       = No (\(p, _) -> np p)
decAnd _       (No nq) = No (\(_, q) -> nq q)

decOr :: Dec p -> Dec q -> Dec (Either p q)
decOr (Yes p) _       = Yes (Left p)
decOr _       (Yes q) = Yes (Right q)
decOr (No np) (No nq) = No (either np nq)

decImp :: Dec p -> Dec q -> Dec (p -> q)
decImp (No np) _       = Yes (\p -> absurd (np p))
decImp _       (Yes q) = Yes (const q)
decImp (Yes p) (No nq) = No (\f -> nq (f p))

decIff :: Dec p -> Dec q -> Dec (Iff p q)
decIff dp dq = case decAnd (decImp dp dq) (decImp dq dp) of
  Yes (f, g) -> Yes (Iff f g)
  No nfg     -> No (\(Iff f g) -> nfg (f, g))

{-# LINE 218 "content/part1/Decidable.md" #-}
-- | Decidable propositional equality on Nat (`_≡ℕ?_`).
decEqNat :: foreach (m n :: Nat) -> Dec (m :~: n)
decEqNat Zero     Zero     = Yes Refl
decEqNat Zero     (Succ _) = No (\case {})
decEqNat (Succ _) Zero     = No (\case {})
decEqNat (Succ m) (Succ n) = case decEqNat m n of
  Yes eq -> Yes (cong Succ eq)
  No neq -> No (\Refl -> neq Refl)

-- | Decidable less-than-or-equal relation on Nat (`_≤?_`).
decLeNat :: foreach (m n :: Nat) -> Dec (LE m n)
decLeNat Zero     _        = Yes ZleN
decLeNat (Succ _) Zero     = No (\case {})
decLeNat (Succ m) (Succ n) = case decLeNat m n of
  Yes p -> Yes (SleS p)
  No np -> No (\p -> np (invSleS p))

-- | Decidable strict less-than relation on Nat (`_<?_`).
decLtNat :: foreach (m n :: Nat) -> Dec (LT' m n)
decLtNat Zero     Zero     = No (\case {})
decLtNat Zero     (Succ _) = Yes ZltS
decLtNat (Succ _) Zero     = No (\case {})
decLtNat (Succ m) (Succ n) = case decLtNat m n of
  Yes p -> Yes (SltS p)
  No np -> No (\case SltS q -> np q)

{-# LINE 260 "content/part1/Decidable.md" #-}
-- | Decidable evenness predicate on Nat.
decEven :: foreach (n :: Nat) -> Dec (Even n)
decEven Zero            = Yes EvenZ
decEven (Succ Zero)     = No (\case EvenS o -> case o of {})
decEven (Succ (Succ n)) = case decEven n of
  Yes ev  -> Yes (EvenS (OddS ev))
  No  nev -> No (\case EvenS (OddS ev) -> nev ev)

-- | Decidable oddness predicate on Nat.
decOdd :: foreach (n :: Nat) -> Dec (Odd n)
decOdd Zero            = No (\case {})
decOdd (Succ Zero)     = Yes (OddS EvenZ)
decOdd (Succ (Succ n)) = case decOdd n of
  Yes od  -> Yes (OddS (EvenS od))
  No  nod -> No (\case OddS (EvenS od) -> nod od)

-- | Boolean reflection: ties a proposition `p` to a promoted `Bool` `b`.
data Reflects (p :: Type) (b :: Bool) where
  OfTrue  :: p -> Reflects p True
  OfFalse :: Not p -> Reflects p False

-- | Reflecting a Boolean yields a decision procedure.
reflectsToDec :: foreach (b :: Bool) -> Reflects p b -> Dec p
reflectsToDec True  (OfTrue p)   = Yes p
reflectsToDec False (OfFalse np) = No np

-- | Decidable equality on binary numbers (`Bin`).
decEqBin :: foreach (a b :: Bin) -> Dec (a :~: b)
decEqBin Nil    Nil    = Yes Refl
decEqBin Nil    (X0 _) = No (\case {})
decEqBin Nil    (X1 _) = No (\case {})
decEqBin (X0 _) Nil    = No (\case {})
decEqBin (X0 _) (X1 _) = No (\case {})
decEqBin (X0 a) (X0 b) = case decEqBin a b of
  Yes Refl -> Yes Refl
  No  neq  -> No (\Refl -> neq Refl)
decEqBin (X1 _) Nil    = No (\case {})
decEqBin (X1 _) (X0 _) = No (\case {})
decEqBin (X1 a) (X1 b) = case decEqBin a b of
  Yes Refl -> Yes Refl
  No  neq  -> No (\Refl -> neq Refl)

-- | Decidable `One` predicate (`One?`).
decOne :: foreach (b :: Bin) -> Dec (One b)
decOne Nil         = No (\case {})
decOne (X0 b)      = case decOne b of
  Yes o  -> Yes (OneX0 o)
  No  no -> No (\case OneX0 o -> no o)
decOne (X1 Nil)    = Yes OneX1
decOne (X1 (X0 b)) = case decOne (X0 b) of
  Yes o  -> Yes (OneX1' o)
  No  no -> No (\case OneX1' o -> no o)
decOne (X1 (X1 b)) = case decOne (X1 b) of
  Yes o  -> Yes (OneX1' o)
  No  no -> No (\case OneX1' o -> no o)

-- | Decidable canonical-form predicate (`Can?`).
decCan :: foreach (b :: Bin) -> Dec (Can b)
decCan Nil         = No (\case CanOne o -> case o of {})
decCan (X0 Nil)    = Yes CanZ
decCan (X0 (X0 b)) = case decOne (X0 b) of
  Yes o  -> Yes (CanOne (OneX0 o))
  No  no -> No (\case CanOne (OneX0 o) -> no o)
decCan (X0 (X1 b)) = case decOne (X1 b) of
  Yes o  -> Yes (CanOne (OneX0 o))
  No  no -> No (\case CanOne (OneX0 o) -> no o)
decCan (X1 b)      = case decOne (X1 b) of
  Yes o  -> Yes (CanOne o)
  No  no -> No (\case CanOne o -> no o)

{-# LINE 343 "content/part1/Decidable.md" #-}
-- | A dependent pair carrying a runtime natural `k` and evidence that Zero <= k.
type NatWitness = some (k :: Nat) | LE Zero k

-- | Package any runtime natural with its proof of Zero <= k.
mkNatWitness :: Nat -> NatWitness
mkNatWitness k = Pair k ZleN

-- | Inline retained dependent sum returned directly from a `foreach` function.
plusExists :: foreach (m n :: Nat)
           -> some (k :: Nat) | k :~: plus m n
plusExists m n = Pair (plus m n) Refl
