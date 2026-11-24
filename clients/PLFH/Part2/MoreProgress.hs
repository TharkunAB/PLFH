{-# LANGUAGE DependentTypes #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
-- | Complete call-by-value reduction (`Step`, `Steps`) with real functional
-- `M.substSingle` and `M.substDouble`, plus unconditional full `progress`
-- across all 19 constructors of `PLFH.Part2.More.Term` (`Let`, `Unit`, `Prod`,
-- `Sum`, `Void`, `List`).
module PLFH.Part2.MoreProgress
  ( Step (..)
  , Steps (..)
  , Progress (..)
  , progress
  , listCaseBoth
  ) where

import Data.Kind (Type)
import qualified PLFH.Part2.More as M

-- | Intrinsically type-preserving call-by-value reduction for extended STLC (27 rules!).
type Step :: forall (g :: M.Ctx) (a :: M.Ty). M.Term g a -> M.Term g a -> Type
data Step before after where
  XiApp1    :: Step f f' -> Step (M.App f x) (M.App f' x)
  XiApp2    :: M.Value f -> Step x x' -> Step (M.App f x) (M.App f x')
  BetaLam   :: forall g a b (body :: M.Term (M.CExt g a) b) (v :: M.Term g a).
               M.Value v -> Step (M.App (M.Lam body) v) (M.substSingle body v)

  XiSuc     :: Step n n' -> Step (M.Suc n) (M.Suc n')
  XiCaseNat :: Step n n' -> Step (M.CaseNat n z s) (M.CaseNat n' z s)
  BetaZero  :: Step (M.CaseNat M.Zero z s) z
  BetaSuc   :: forall g a (z :: M.Term g a) (s :: M.Term (M.CExt g M.TNat) a)
                      (v :: M.Term g M.TNat).
               M.Value v -> Step (M.CaseNat (M.Suc v) z s) (M.substSingle s v)
  BetaMu    :: forall g a (body :: M.Term (M.CExt g a) a).
               Step (M.Mu body) (M.substSingle body (M.Mu body))

  XiLet     :: Step m m' -> Step (M.Let m body) (M.Let m' body)
  BetaLet   :: forall g a b (m :: M.Term g a) (body :: M.Term (M.CExt g a) b).
               M.Value m -> Step (M.Let m body) (M.substSingle body m)

  XiPair1   :: Step l l' -> Step (M.Pair l r) (M.Pair l' r)
  XiPair2   :: M.Value l -> Step r r' -> Step (M.Pair l r) (M.Pair l r')
  XiFst     :: Step p p' -> Step (M.Fst p) (M.Fst p')
  XiSnd     :: Step p p' -> Step (M.Snd p) (M.Snd p')
  BetaFst   :: M.Value l -> M.Value r -> Step (M.Fst (M.Pair l r)) l
  BetaSnd   :: M.Value l -> M.Value r -> Step (M.Snd (M.Pair l r)) r

  XiInl     :: Step x x' -> Step (M.Inl x) (M.Inl x')
  XiInr     :: Step y y' -> Step (M.Inr y) (M.Inr y')
  XiCaseSum :: Step s s' -> Step (M.CaseSum s l r) (M.CaseSum s' l r)
  BetaInl   :: forall g a b c (l :: M.Term (M.CExt g a) c)
                      (r :: M.Term (M.CExt g b) c) (x :: M.Term g a).
               M.Value x -> Step (M.CaseSum (M.Inl x) l r) (M.substSingle l x)
  BetaInr   :: forall g a b c (l :: M.Term (M.CExt g a) c)
                      (r :: M.Term (M.CExt g b) c) (y :: M.Term g b).
               M.Value y -> Step (M.CaseSum (M.Inr y) l r) (M.substSingle r y)
  XiAbsurd  :: Step m m' -> Step (M.Absurd m) (M.Absurd m')

  XiCons1   :: Step x x' -> Step (M.Cons x xs) (M.Cons x' xs)
  XiCons2   :: M.Value x -> Step xs xs' -> Step (M.Cons x xs) (M.Cons x xs')
  XiCaseLst :: Step s s' -> Step (M.CaseLst s n c) (M.CaseLst s' n c)
  BetaNil   :: Step (M.CaseLst M.Nil n c) n
  BetaCons  :: forall g a b (n :: M.Term g b)
                      (c :: M.Term (M.CExt (M.CExt g a) (M.TList a)) b)
                      (x :: M.Term g a) (xs :: M.Term g (M.TList a)).
               M.Value x -> M.Value xs
            -> Step (M.CaseLst (M.Cons x xs) n c) (M.substDouble c x xs)

-- | Reflexive-transitive closure of extended STLC reduction (`M —↠ N`).
type Steps :: forall (g :: M.Ctx) (a :: M.Ty). M.Term g a -> M.Term g a -> Type
data Steps m n where
  StepsRefl :: Steps m m
  StepsCons :: Step l m -> Steps m n -> Steps l n

-- | A closed term in the extended language either steps or is a value.
type Progress :: forall (a :: M.Ty). M.Term M.CEmpty a -> Type
data Progress m where
  PStep :: Step m n -> Progress m
  PDone :: M.Value m -> Progress m

-- | Complete, unconditional Progress theorem across all 19 constructors of `More.Term`!
progress :: forall (a :: M.Ty). foreach (m :: M.Term M.CEmpty a) -> Progress m
progress t = case t of
  M.Var x         -> case x of {}
  M.Lam _         -> PDone M.VLam
  M.App f x       -> appProgress (progress f) (progress x)
  M.Zero          -> PDone M.VZero
  M.Suc n         -> sucProgress (progress n)
  M.CaseNat n z s -> natCaseProgress @a @n @z @s (progress n)
  M.Mu body       -> PStep (BetaMu @M.CEmpty @a @body)
  M.Let m body    -> letProgress @_ @a @m @body (progress m)
  M.TT            -> PDone M.VTT
  M.Pair l r      -> pairProgress (progress l) (progress r)
  M.Fst p         -> fstProgress (progress p)
  M.Snd p         -> sndProgress (progress p)
  M.Inl x         -> inlProgress (progress x)
  M.Inr y         -> inrProgress (progress y)
  M.CaseSum s l r -> sumCaseProgress @_ @_ @a @s @l @r (progress s)
  M.Absurd m      -> absurdProgress (progress m)
  M.Nil           -> PDone M.VNil
  M.Cons x xs     -> consProgress (progress x) (progress xs)
  M.CaseLst s n c -> listCaseProgress @_ @a @s @n @c (progress s)

appProgress :: forall a b (f :: M.Term M.CEmpty (M.TArr a b)) (x :: M.Term M.CEmpty a).
               Progress f -> Progress x -> Progress (M.App f x)
appProgress (PStep s) _                      = PStep (XiApp1 s)
appProgress (PDone v) (PStep s)              = PStep (XiApp2 v s)
appProgress (PDone (M.VLam @body)) (PDone v) = PStep (BetaLam @M.CEmpty @a @b @body @x v)

sucProgress :: Progress n -> Progress (M.Suc n)
sucProgress (PStep s) = PStep (XiSuc s)
sucProgress (PDone v) = PDone (M.VSuc v)

natCaseProgress :: forall a (n :: M.Term M.CEmpty M.TNat) (z :: M.Term M.CEmpty a)
                          (s :: M.Term (M.CExt M.CEmpty M.TNat) a).
                   Progress n -> Progress (M.CaseNat n z s)
natCaseProgress (PStep step)            = PStep (XiCaseNat step)
natCaseProgress (PDone M.VZero)         = PStep BetaZero
natCaseProgress (PDone (M.VSuc @v val)) = PStep (BetaSuc @M.CEmpty @a @z @s @v val)

letProgress :: forall a b (m :: M.Term M.CEmpty a) (body :: M.Term (M.CExt M.CEmpty a) b).
               Progress m -> Progress (M.Let m body)
letProgress (PStep s) = PStep (XiLet s)
letProgress (PDone v) = PStep (BetaLet @M.CEmpty @a @b @m @body v)

pairProgress :: Progress l -> Progress r -> Progress (M.Pair l r)
pairProgress (PStep s) _         = PStep (XiPair1 s)
pairProgress (PDone v) (PStep s) = PStep (XiPair2 v s)
pairProgress (PDone v) (PDone w) = PDone (M.VPair v w)

fstProgress :: Progress p -> Progress (M.Fst p)
fstProgress (PStep s)              = PStep (XiFst s)
fstProgress (PDone (M.VPair v w))  = PStep (BetaFst v w)

sndProgress :: Progress p -> Progress (M.Snd p)
sndProgress (PStep s)              = PStep (XiSnd s)
sndProgress (PDone (M.VPair v w))  = PStep (BetaSnd v w)

inlProgress :: Progress x -> Progress (M.Inl x)
inlProgress (PStep s) = PStep (XiInl s)
inlProgress (PDone v) = PDone (M.VInl v)

inrProgress :: Progress y -> Progress (M.Inr y)
inrProgress (PStep s) = PStep (XiInr s)
inrProgress (PDone v) = PDone (M.VInr v)

sumCaseProgress :: forall a b c (s :: M.Term M.CEmpty (M.TSum a b))
                          (l :: M.Term (M.CExt M.CEmpty a) c)
                          (r :: M.Term (M.CExt M.CEmpty b) c).
                   Progress s -> Progress (M.CaseSum s l r)
sumCaseProgress (PStep step)        = PStep (XiCaseSum step)
sumCaseProgress (PDone (M.VInl @x v)) = PStep (BetaInl @M.CEmpty @a @b @c @l @r @x v)
sumCaseProgress (PDone (M.VInr @y v)) = PStep (BetaInr @M.CEmpty @a @b @c @l @r @y v)

absurdProgress :: Progress m -> Progress (M.Absurd m)
absurdProgress (PStep s) = PStep (XiAbsurd s)
absurdProgress (PDone v) = case v of {}

consProgress :: Progress x -> Progress xs -> Progress (M.Cons x xs)
consProgress (PStep s) _          = PStep (XiCons1 s)
consProgress (PDone v) (PStep s)  = PStep (XiCons2 v s)
consProgress (PDone v) (PDone vs) = PDone (M.VCons v vs)

listCaseProgress :: forall a b (s :: M.Term M.CEmpty (M.TList a)) (n :: M.Term M.CEmpty b)
                           (c :: M.Term (M.CExt (M.CExt M.CEmpty a) (M.TList a)) b).
                    Progress s -> Progress (M.CaseLst s n c)
listCaseProgress (PStep step)               = PStep (XiCaseLst step)
listCaseProgress (PDone M.VNil)             = PStep BetaNil
listCaseProgress (PDone (M.VCons @x @xs v vs)) = PStep (BetaCons @M.CEmpty @a @b @n @c @x @xs v vs)

-- | Concrete `BetaCons` witness exercising `M.substDouble`:
-- `S Z` receives the head (`Suc Zero`) and `Z` receives the tail (`Cons Zero Nil`)!
listCaseBoth
  :: Step @M.CEmpty @(M.TProd M.TNat (M.TList M.TNat))
          (M.CaseLst (M.Cons (M.Suc M.Zero) (M.Cons M.Zero M.Nil))
                     (M.Pair M.Zero M.Nil)
                     (M.Pair (M.Var (M.S M.Z)) (M.Var M.Z)))
          (M.Pair (M.Suc M.Zero) (M.Cons M.Zero M.Nil))
listCaseBoth = BetaCons (M.VSuc M.VZero) (M.VCons M.VZero M.VNil)
