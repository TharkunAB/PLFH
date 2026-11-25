-- Generated from content/part2/DeBruijn.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DependentTypes #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
{-# LINE 41 "content/part2/DeBruijn.md" #-}
module PLFH.Part2.DeBruijn
  ( Ty (..)
  , Ctx (..)
  , Lookup (..)
  , Term (..)
  , ext
  , rename
  , exts
  , subst
  , substSingle
  , termTwo
  , plusTerm
  , mulTerm
  , Value (..)
  , valZero
  , IsVal (..)
  , checkValue
  , Step (..)
  , Steps (..)
  , Progress (..)
  , progress
  , appProgress
  , betaIdStep
  , betaCaptureAvoid
  , betaShiftUnderLam
  ) where

import Data.Kind (Type)

{-# LINE 88 "content/part2/DeBruijn.md" #-}
-- | Simple types: natural numbers and functions.
data Ty = TNat | TArr Ty Ty
  deriving (Show)

-- | Nameless typing contexts.
data Ctx = CEmpty | CExt Ctx Ty

-- | Intrinsically typed de Bruijn indices (Γ ∋ A).
data Lookup (g :: Ctx) (a :: Ty) where
  Z :: Lookup (CExt g a) a
  S :: Lookup g a -> Lookup (CExt g b) a

{-# LINE 108 "content/part2/DeBruijn.md" #-}
-- | Intrinsically typed STLC terms with naturals, case, and μ-recursion.
data Term (g :: Ctx) (a :: Ty) where
  Var  :: Lookup g a -> Term g a
  Lam  :: Term (CExt g a) b -> Term g (TArr a b)
  App  :: Term g (TArr a b) -> Term g a -> Term g b
  Zero :: Term g TNat
  Suc  :: Term g TNat -> Term g TNat
  Case :: Term g TNat -> Term g a -> Term (CExt g TNat) a -> Term g a
  Mu   :: Term (CExt g a) a -> Term g a

-- | Closed intrinsically-typed numeral 2.
termTwo :: Term g TNat
termTwo = Suc (Suc Zero)

-- | Intrinsically-typed recursive addition (`two+two`): Nat -> Nat -> Nat.
-- μ "+". λ m. λ n. case m [ zero => n | suc m' => suc ("+" m' n) ]
plusTerm :: Term g (TArr TNat (TArr TNat TNat))
plusTerm =
  Mu (Lam (Lam
    (Case (Var (S Z))
      (Var Z)
      (Suc (App (App (Var (S (S (S Z)))) (Var Z)) (Var (S Z)))))))

-- | Intrinsically-typed recursive multiplication (`mul`): Nat -> Nat -> Nat.
-- μ "*". λ m. λ n. case m [ zero => zero | suc m' => plus n ("*" m' n) ]
mulTerm :: Term g (TArr TNat (TArr TNat TNat))
mulTerm =
  Mu (Lam (Lam
    (Case (Var (S Z))
      Zero
      (App (App plusTerm (Var (S Z)))
           (App (App (Var (S (S (S Z)))) (Var Z)) (Var (S Z)))))))

{-# LINE 175 "content/part2/DeBruijn.md" #-}
-- | Extend a variable renaming under a binder.
ext :: (forall a. Lookup g a -> Lookup d a)
    -> (forall a. Lookup (CExt g b) a -> Lookup (CExt d b) a)
ext _   Z     = Z
ext rho (S x) = S (rho x)

-- | Simultaneous renaming on intrinsically typed terms.
rename :: (forall a. Lookup g a -> Lookup d a) -> Term g b -> Term d b
rename rho (Var x)      = Var (rho x)
rename rho (Lam n)      = Lam (rename (ext rho) n)
rename rho (App l m)    = App (rename rho l) (rename rho m)
rename _   Zero         = Zero
rename rho (Suc m)      = Suc (rename rho m)
rename rho (Case l m n) = Case (rename rho l) (rename rho m) (rename (ext rho) n)
rename rho (Mu n)       = Mu (rename (ext rho) n)

-- | Extend a simultaneous substitution under a binder.
exts :: (forall a. Lookup g a -> Term d a)
     -> (forall a. Lookup (CExt g b) a -> Term (CExt d b) a)
exts _     Z     = Var Z
exts sigma (S x) = rename S (sigma x)

-- | Simultaneous substitution on intrinsically typed terms.
subst :: (forall a. Lookup g a -> Term d a) -> Term g b -> Term d b
subst sigma (Var x)      = sigma x
subst sigma (Lam n)      = Lam (subst (exts sigma) n)
subst sigma (App l m)    = App (subst sigma l) (subst sigma m)
subst _     Zero         = Zero
subst sigma (Suc m)      = Suc (subst sigma m)
subst sigma (Case l m n) = Case (subst sigma l) (subst sigma m) (subst (exts sigma) n)
subst sigma (Mu n)       = Mu (subst (exts sigma) n)

-- | Substitute a single closed/open term `w` for variable `Z` in `n` (N [ W ]).
substSingle :: Term (CExt g a) b -> Term g a -> Term g b
substSingle n w = subst (\case { Z -> w; S x -> Var x }) n

{-# LINE 224 "content/part2/DeBruijn.md" #-}
-- | Values indexed by promoted intrinsically-typed terms!
type Value :: forall (g :: Ctx) (a :: Ty). Term g a -> Type
data Value m where
  VLam  :: Value (Lam n)
  VZero :: Value Zero
  VSuc  :: Value v -> Value (Suc v)

-- | Concrete witness that `Zero` is already a value.
valZero :: Value (Zero :: Term CEmpty TNat)
valZero = VZero

-- | Classification of a closed intrinsically-typed term as a value or non-value.
type IsVal :: forall (a :: Ty). Term CEmpty a -> Type
data IsVal m where
  YesVal :: Value m -> IsVal m
  NotVal :: IsVal m

-- | Equation-style value classification over retained intrinsically-typed `Term CEmpty a`!
checkValue :: forall (a :: Ty). foreach (m :: Term CEmpty a) -> IsVal m
checkValue (Var x)      = case x of {}
checkValue (Lam _)      = YesVal VLam
checkValue (App _ _)    = NotVal
checkValue Zero         = YesVal VZero
checkValue (Suc n)      = case checkValue n of
  YesVal v -> YesVal (VSuc v)
  NotVal   -> NotVal
checkValue (Case _ _ _) = NotVal
checkValue (Mu _)       = NotVal

{-# LINE 284 "content/part2/DeBruijn.md" #-}
-- | Intrinsically type-preserving call-by-value reduction (`M —→ N`).
-- Preservation holds automatically by the kind of `Step`!
type Step :: forall (g :: Ctx) (a :: Ty). Term g a -> Term g a -> Type
data Step m n where
  XiApp1   :: Step l l' -> Step (App l m) (App l' m)
  XiApp2   :: Value l -> Step m m' -> Step (App l m) (App l m')
  XiSuc    :: Step m m' -> Step (Suc m) (Suc m')
  XiCase   :: Step l l' -> Step (Case l m n) (Case l' m n)
  BetaLam  :: forall g a b (n :: Term (CExt g a) b) (w :: Term g a).
              Value w -> Step (App (Lam n) w) (substSingle n w)
  BetaZero :: forall g a (m :: Term g a) (n :: Term (CExt g TNat) a).
              Step (Case Zero m n) m
  BetaSuc  :: forall g a (m :: Term g a) (n :: Term (CExt g TNat) a)
                         (v :: Term g TNat).
              Value v -> Step (Case (Suc v) m n) (substSingle n v)
  BetaMu   :: forall g a (n :: Term (CExt g a) a).
              Step (Mu n) (substSingle n (Mu n))

-- | Reflexive-transitive closure of intrinsically-typed reduction (`M —↠ N`).
type Steps :: forall (g :: Ctx) (a :: Ty). Term g a -> Term g a -> Type
data Steps m n where
  StepsRefl :: Steps m m
  StepsCons :: Step l m -> Steps m n -> Steps l n

-- | Intrinsically-typed progress witness for closed terms.
type Progress :: forall (a :: Ty). Term CEmpty a -> Type
data Progress m where
  PStep :: Step m n -> Progress m
  PDone :: Value m -> Progress m

-- | Complete, unconditional Progress theorem for intrinsically-typed STLC:
-- every closed well-typed term is either a value or takes a type-preserving step!
progress :: forall (a :: Ty). foreach (m :: Term CEmpty a) -> Progress m
progress t = case t of
  Var x -> case x of {}
  Lam _ -> PDone VLam
  App l m -> case progress l of
    PStep s -> appLeft s
    PDone v -> case progress m of
      PStep s -> appRight v s
      PDone w -> appBeta v w
  Zero -> PDone VZero
  Suc n -> case progress n of
    PStep s -> sucStep s
    PDone v -> PDone (VSuc v)
  Case l m n -> case progress l of
    PStep s -> caseStep @a @l @_ @m @n s
    PDone v -> caseBeta @a @l @m @n v
  Mu n -> muStep @a @n

-- | Application case factored out as a standalone helper given subterm progress.
appProgress
  :: forall (a :: Ty).
     (forall (b :: Ty). foreach (m :: Term CEmpty b) -> Progress m)
  -> foreach (t :: Term CEmpty a) -> Maybe (Progress t)
appProgress recProg t = case t of
  App l m -> case recProg l of
    PStep s -> Just (appLeft s)
    PDone v -> case recProg m of
      PStep s -> Just (appRight v s)
      PDone w -> Just (appBeta v w)
  _ -> Nothing

appLeft :: forall a b (l :: Term CEmpty (TArr a b))
                      (l' :: Term CEmpty (TArr a b)) (m :: Term CEmpty a).
           Step l l' -> Progress (App l m)
appLeft s = PStep (XiApp1 s)

appRight :: forall a b (l :: Term CEmpty (TArr a b))
                       (m :: Term CEmpty a) (m' :: Term CEmpty a).
            Value l -> Step m m' -> Progress (App l m)
appRight v s = PStep (XiApp2 v s)

appBeta :: forall a b (l :: Term CEmpty (TArr a b)) (m :: Term CEmpty a).
           Value l -> Value m -> Progress (App l m)
appBeta (VLam @n) w = PStep (BetaLam @CEmpty @a @b @n @m w)

sucStep :: forall (n :: Term CEmpty TNat) (n' :: Term CEmpty TNat).
           Step n n' -> Progress (Suc n)
sucStep s = PStep (XiSuc s)

caseStep :: forall a (l :: Term CEmpty TNat) (l' :: Term CEmpty TNat)
                     (m :: Term CEmpty a) (n :: Term (CExt CEmpty TNat) a).
            Step l l' -> Progress (Case l m n)
caseStep s = PStep (XiCase s)

caseBeta :: forall a (l :: Term CEmpty TNat) (m :: Term CEmpty a)
                     (n :: Term (CExt CEmpty TNat) a).
            Value l -> Progress (Case l m n)
caseBeta VZero       = PStep (BetaZero @CEmpty @a @m @n)
caseBeta (VSuc @v w) = PStep (BetaSuc @CEmpty @a @m @n @v w)

muStep :: forall a (n :: Term (CExt CEmpty a) a). Progress (Mu n)
muStep = PStep (BetaMu @CEmpty @a @n)

-- | Concrete β-reduction: (λ. 0) 0 —→ 0.
betaIdStep :: Step (App (Lam (Var Z)) Zero) Zero
betaIdStep = BetaLam VZero

-- | Concrete substitution under a binder: (λ. λ. 1) 0 —→ λ. 0.
betaCaptureAvoid :: Step (App (Lam (Lam (Var (S Z)))) Zero) (Lam Zero)
betaCaptureAvoid = BetaLam VZero

-- | Capture-avoiding substitution of an open value under a binder:
-- in context (∅, Nat), substituting `w = λ. Var (S Z)` (which references the
-- free outer Nat) into `λ. Var (S Z)` shifts `w`'s free variable to `S (S Z)`!
betaShiftUnderLam
  :: Step @(CExt CEmpty TNat)
          @(TArr TNat (TArr TNat TNat))
          (App (Lam (Lam (Var (S Z)))) (Lam (Var (S Z))))
          (Lam (Lam (Var (S (S Z)))))
betaShiftUnderLam = BetaLam VLam
