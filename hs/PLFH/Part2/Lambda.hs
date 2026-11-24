-- Generated from content/part2/Lambda.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, ExplicitForAll, GADTs, TypeOperators #-}
{-# LINE 12 "content/part2/Lambda.md" #-}
module PLFH.Part2.Lambda
  ( Id
  , eqId
  , Term (..)
  , Ty (..)
  , Ctx (..)
  , Value (..)
  , substTerm
  , Step (..)
  , Steps (..)
  , Lookup (..)
  , HasType (..)
  , termTwo
  , twoTyped
  ) where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..))
import PLFH.Part1.Decidable (Not)

{-# LINE 53 "content/part2/Lambda.md" #-}
-- | Variable identifiers represented structurally as Peano naturals.
type Id = Nat

-- | Structural equality on variable identifiers.
eqId :: Id -> Id -> Bool
eqId Zero     Zero     = True
eqId Zero     (Succ _) = False
eqId (Succ _) Zero     = False
eqId (Succ m) (Succ n) = eqId m n

-- | Untyped lambda calculus terms with naturals, case, and μ-recursion.
data Term
  = Var Id
  | Lam Id Term
  | App Term Term
  | TZero
  | TSuc Term
  | TCase Term Term Id Term
  | TMu Id Term
  deriving (Show)

-- | Simple types: natural numbers and functions.
data Ty
  = TNat
  | TArr Ty Ty
  deriving (Show)

-- | Typing contexts associating variable identifiers with types.
data Ctx
  = CEmpty
  | CExt Ctx Id Ty
  deriving (Show)

{-# LINE 93 "content/part2/Lambda.md" #-}
-- | Evidence that a term is a call-by-value value.
data Value (t :: Term) where
  VLam  :: Value ('Lam x n)
  VZero :: Value 'TZero
  VSuc  :: Value v -> Value ('TSuc v)

{-# LINE 106 "content/part2/Lambda.md" #-}
-- | Substitute a closed term `v` for free occurrences of `y` in `m`.
substTerm :: Term -> Id -> Term -> Term
substTerm (Var x) y v = case eqId x y of
  True  -> v
  False -> Var x
substTerm (Lam x n) y v = case eqId x y of
  True  -> Lam x n
  False -> Lam x (substTerm n y v)
substTerm (App l m) y v = App (substTerm l y v) (substTerm m y v)
substTerm TZero _ _ = TZero
substTerm (TSuc m) y v = TSuc (substTerm m y v)
substTerm (TCase l m x n) y v = case eqId x y of
  True  -> TCase (substTerm l y v) (substTerm m y v) x n
  False -> TCase (substTerm l y v) (substTerm m y v) x (substTerm n y v)
substTerm (TMu x n) y v = case eqId x y of
  True  -> TMu x n
  False -> TMu x (substTerm n y v)

{-# LINE 132 "content/part2/Lambda.md" #-}
-- | Call-by-value one-step reduction relation (M —→ N).
data Step (m :: Term) (n :: Term) where
  XiApp1   :: Step l l' -> Step ('App l m) ('App l' m)
  XiApp2   :: Value v -> Step m m' -> Step ('App v m) ('App v m')
  BetaLam  :: forall v x n. Value v -> Step ('App ('Lam x n) v) (substTerm n x v)
  XiSuc    :: Step m m' -> Step ('TSuc m) ('TSuc m')
  XiCase   :: Step l l' -> Step ('TCase l m x n) ('TCase l' m x n)
  BetaZero :: Step ('TCase 'TZero m x n) m
  BetaSuc  :: forall v m x n. Value v -> Step ('TCase ('TSuc v) m x n) (substTerm n x v)
  BetaMu   :: forall x m. Step ('TMu x m) (substTerm m x ('TMu x m))

-- | Reflexive-transitive closure of one-step reduction (M —↠ N).
data Steps (m :: Term) (n :: Term) where
  StepsRefl :: Steps m m
  StepsCons :: Step l m -> Steps m n -> Steps l n

{-# LINE 163 "content/part2/Lambda.md" #-}
-- | Evidence that variable `x` has type `a` in context `g` (Γ ∋ x ⦂ A).
data Lookup (g :: Ctx) (x :: Id) (a :: Ty) where
  LZ :: Lookup ('CExt g x a) x a
  LS :: Not (x :~: y) -> Lookup g x a -> Lookup ('CExt g y b) x a

-- | Extrinsic typing derivation (Γ ⊢ M ⦂ A).
data HasType (g :: Ctx) (m :: Term) (a :: Ty) where
  TVar   :: Lookup g x a -> HasType g ('Var x) a
  TLam   :: HasType ('CExt g x a) n b -> HasType g ('Lam x n) ('TArr a b)
  TApp   :: HasType g l ('TArr a b) -> HasType g m a -> HasType g ('App l m) b
  TZeroT :: HasType g 'TZero 'TNat
  TSucT  :: HasType g m 'TNat -> HasType g ('TSuc m) 'TNat
  TCaseT :: HasType g l 'TNat -> HasType g m a -> HasType ('CExt g x 'TNat) n a
         -> HasType g ('TCase l m x n) a
  TMuT   :: HasType ('CExt g x a) m a -> HasType g ('TMu x m) a

{-# LINE 183 "content/part2/Lambda.md" #-}
-- | The term representing natural number 2.
termTwo :: Term
termTwo = TSuc (TSuc TZero)

-- | Typing derivation showing ∅ ⊢ suc (suc zero) : Nat.
twoTyped :: HasType 'CEmpty ('TSuc ('TSuc 'TZero)) 'TNat
twoTyped = TSucT (TSucT TZeroT)
