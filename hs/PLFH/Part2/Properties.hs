-- Generated from content/part2/Properties.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, TypeAbstractions, TypeApplications, TypeOperators #-}
{-# LINE 41 "content/part2/Properties.md" #-}
module PLFH.Part2.Properties
  ( Canonical (..)
  , canonical
  , Progress (..)
  , progress
  , valueCannotStep
  , stepDeterm
  , extCtx
  , renameTyping
  , weakenTyping
  , dropTyping
  , swapTyping
  , NameDecision (..)
  , decide
  , substTyping
  , preserve
  , TermW (..)
  , stepTarget
  , preserveSteps
  , EvalResult (..)
  , eval
  ) where

import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void, absurd)
import HaskLib.Nat (Nat (..))
import PLFH.Part1.Decidable (Not)
import PLFH.Part2.Lambda
  ( Ctx (..)
  , HasType (..)
  , Id
  , Lookup (..)
  , Step (..)
  , Steps (..)
  , Term (..)
  , Ty (..)
  , Value (..)
  , eqId
  , substTerm
  )

{-# LINE 94 "content/part2/Properties.md" #-}
-- | Canonical form of a closed well-typed value.
data Canonical (m :: Term) (a :: Ty) where
  CLam  :: HasType (CExt CEmpty x a) n b -> Canonical (Lam x n) (TArr a b)
  CZero :: Canonical TZero TNat
  CSuc  :: Value v -> HasType CEmpty v TNat -> Canonical (TSuc v) TNat

-- | Every closed well-typed value has a canonical form matching its type.
canonical :: HasType CEmpty v a -> Value v -> Canonical v a
canonical (TLam tn)  VLam      = CLam tn
canonical TZeroT     VZero     = CZero
canonical (TSucT tv) (VSuc vv) = CSuc vv tv

{-# LINE 117 "content/part2/Properties.md" #-}
-- | Evidence that a closed term either steps or is already a value.
data Progress (m :: Term) where
  PStep :: Step m n -> Progress m
  PDone :: Value m  -> Progress m

-- | Progress theorem: every closed well-typed term either steps or is a value.
progress :: HasType CEmpty m a -> Progress m
progress (TVar x) = case x of {}
progress (TLam _) = PDone VLam
progress (TApp tl tm) = case progress tl of
  PStep s  -> PStep (XiApp1 s)
  PDone vl -> case progress tm of
    PStep s  -> PStep (XiApp2 vl s)
    PDone vm -> case canonical tl vl of
      CLam _ -> PStep (BetaLam vm)
progress TZeroT = PDone VZero
progress (TSucT tm) = case progress tm of
  PStep s  -> PStep (XiSuc s)
  PDone vm -> PDone (VSuc vm)
progress (TCaseT tl _ _) = case progress tl of
  PStep s  -> PStep (XiCase s)
  PDone vl -> case canonical tl vl of
    CZero    -> PStep BetaZero
    CSuc v _ -> PStep (BetaSuc v)
progress (TMuT _) = PStep BetaMu

{-# LINE 179 "content/part2/Properties.md" #-}
-- | Extend a context inclusion under a newly bound variable `x : a`.
extCtx :: (forall y b. Lookup g y b -> Lookup d y b)
       -> Lookup (CExt g x a) y b
       -> Lookup (CExt d x a) y b
extCtx _   LZ         = LZ
extCtx rho (LS neq p) = LS neq (rho p)

-- | Rename (or map) variable lookups throughout a typing derivation.
renameTyping :: (forall y b. Lookup g y b -> Lookup d y b)
             -> HasType g m a
             -> HasType d m a
renameTyping rho (TVar p)          = TVar (rho p)
renameTyping rho (TLam tn)         = TLam (renameTyping (extCtx rho) tn)
renameTyping rho (TApp tl tm)      = TApp (renameTyping rho tl) (renameTyping rho tm)
renameTyping _   TZeroT            = TZeroT
renameTyping rho (TSucT tm)        = TSucT (renameTyping rho tm)
renameTyping rho (TCaseT tl tm tn) =
  TCaseT (renameTyping rho tl) (renameTyping rho tm) (renameTyping (extCtx rho) tn)
renameTyping rho (TMuT tm)         = TMuT (renameTyping (extCtx rho) tm)

-- | A closed term is well-typed in any context `g`.
weakenTyping :: HasType CEmpty m a -> HasType g m a
weakenTyping = renameTyping (\case {})

-- | Drop a shadowed duplicate binding for `x` from the context.
dropTyping :: HasType (CExt (CExt g x a) x b) m c
           -> HasType (CExt g x b) m c
dropTyping = renameTyping dropLookup
  where
    dropLookup :: Lookup (CExt (CExt g x a) x b) y c -> Lookup (CExt g x b) y c
    dropLookup LZ                = LZ
    dropLookup (LS neq LZ)       = absurd (neq Refl)
    dropLookup (LS neq (LS _ p)) = LS neq p

-- | Swap two distinct adjacent bindings `x /= y` in the context.
swapTyping :: forall g x y a b m c.
              Not (x :~: y)
           -> HasType (CExt (CExt g x a) y b) m c
           -> HasType (CExt (CExt g y b) x a) m c
swapTyping xNeqY = renameTyping swapLookup
  where
    swapLookup :: Lookup (CExt (CExt g x a) y b) z d
               -> Lookup (CExt (CExt g y b) x a) z d
    swapLookup LZ                         = LS (\Refl -> xNeqY Refl) LZ
    swapLookup (LS _ LZ)                  = LZ
    swapLookup (LS zNeqY (LS zNeqX rest)) = LS zNeqX (LS zNeqY rest)

{-# LINE 246 "content/part2/Properties.md" #-}
-- | Decidable identifier equality paired with the Boolean result of `eqId`.
data NameDecision (x :: Id) (y :: Id) where
    Same :: x :~: y -> eqId x y :~: True -> NameDecision x y
    Different :: (x :~: y -> Void) -> eqId x y :~: False -> NameDecision x y

-- | Decide whether two variable identifiers are equal, reflecting `eqId`.
decide :: foreach (x :: Id) -> foreach (y :: Id) -> NameDecision x y
decide Zero Zero = Same Refl Refl
decide Zero (Succ _) = Different (\case {}) Refl
decide (Succ _) Zero = Different (\case {}) Refl
decide (Succ x) (Succ y) = case decide x y of
    Same Refl Refl -> Same Refl Refl
    Different neq Refl -> Different (\Refl -> neq Refl) Refl

-- | Substitute a closed well-typed term for the last context entry.
substTyping :: forall g a b v. foreach (y :: Id) -> foreach (t :: Term)
      -> HasType CEmpty v a -> HasType (CExt g y a) t b -> HasType g (substTerm t y v) b
substTyping y term replacement typed = case term of
    Var x -> case typed of
      TVar LZ -> case decide x y of
        Same Refl Refl -> weakenTyping replacement
        Different neq _ -> absurd (neq Refl)
      TVar (LS neq p) -> case decide x y of
        Same Refl _ -> absurd (neq Refl)
        Different _ Refl -> TVar p
    Lam x t -> case typed of
      TLam tt -> case decide x y of
        Same Refl Refl -> TLam (dropTyping tt)
        Different neq Refl -> TLam (substTyping y t replacement (swapTyping (\Refl -> neq Refl) tt))
    App l r -> case typed of
      TApp tl tr -> TApp (substTyping y l replacement tl) (substTyping y r replacement tr)
    TZero -> case typed of
      TZeroT -> TZeroT
    TSuc t -> case typed of
      TSucT tt -> TSucT (substTyping y t replacement tt)
    TCase l z x s -> case typed of
      TCaseT tl tz ts -> case decide x y of
        Same Refl Refl -> TCaseT (substTyping y l replacement tl) (substTyping y z replacement tz) (dropTyping ts)
        Different neq Refl ->
          TCaseT (substTyping y l replacement tl) (substTyping y z replacement tz)
                 (substTyping y s replacement (swapTyping (\Refl -> neq Refl) ts))
    TMu x t -> case typed of
      TMuT tt -> case decide x y of
        Same Refl Refl -> TMuT (dropTyping tt)
        Different neq Refl -> TMuT (substTyping y t replacement (swapTyping (\Refl -> neq Refl) tt))

{-# LINE 306 "content/part2/Properties.md" #-}
-- | Shape witness recording that a term is a lambda abstraction.
data IsLam (m :: Term) where
    IsLam :: IsLam (Lam x body)

-- | Shape witness recording that a term is a successor.
data IsSuc (m :: Term) where
    IsSuc :: IsSuc (TSuc v)

-- | Preservation theorem: a step preserves the type of a closed term.
preserve :: foreach (m :: Term) -> HasType CEmpty m a -> Step m n -> HasType CEmpty n a
preserve source typed step = case source of
    Var _ -> case step of {}
    Lam _ _ -> case step of {}
    TZero -> case step of {}
    App l r -> case typed of
      TApp tl tr -> case step of
        XiApp1 sl -> TApp (preserve l tl sl) tr
        XiApp2 _ sr -> TApp tl (preserve r tr sr)
        BetaLam @_ @binder @bodyIndex _ ->
          let shape :: IsLam l
              shape = IsLam @binder @bodyIndex
          in case l of
            Lam x body -> substLam x body tr tl
            Var _ -> case shape of {}
            App _ _ -> case shape of {}
            TZero -> case shape of {}
            TSuc _ -> case shape of {}
            TCase _ _ _ _ -> case shape of {}
            TMu _ _ -> case shape of {}
    TSuc m -> case typed of
      TSucT tm -> case step of
        XiSuc sm -> TSucT (preserve m tm sm)
    TCase l z x n -> case typed of
      TCaseT tl tz tn -> case step of
        XiCase sl -> TCaseT (preserve l tl sl) tz tn
        BetaZero -> tz
        BetaSuc @value _ ->
          let shape :: IsSuc l
              shape = IsSuc @value
          in case l of
            TSuc v -> substSuc v x n tl tn
            Var _ -> case shape of {}
            Lam _ _ -> case shape of {}
            App _ _ -> case shape of {}
            TZero -> case shape of {}
            TCase _ _ _ _ -> case shape of {}
            TMu _ _ -> case shape of {}
    TMu x m -> case typed of
      TMuT tm -> case step of
        BetaMu -> substTyping x m typed tm

substLam :: foreach (x :: Id) -> foreach (body :: Term)
         -> HasType CEmpty v a
         -> HasType CEmpty (Lam x body) (TArr a b)
         -> HasType CEmpty (substTerm body x v) b
substLam x body replacement (TLam tb) = substTyping x body replacement tb

substSuc :: foreach (v :: Term) -> foreach (x :: Id) -> foreach (body :: Term)
         -> HasType CEmpty (TSuc v) TNat
         -> HasType (CExt CEmpty x TNat) body a
         -> HasType CEmpty (substTerm body x v) a
substSuc _ x body (TSucT tv) tn = substTyping x body tv tn

{-# LINE 379 "content/part2/Properties.md" #-}
-- | Values do not reduce (`V-¬—→`).
valueCannotStep :: Value m -> Not (Step m n)
valueCannotStep VLam     s         = case s of {}
valueCannotStep VZero    s         = case s of {}
valueCannotStep (VSuc v) (XiSuc s) = valueCannotStep v s

-- | Determinism of call-by-value one-step reduction (`det`).
stepDeterm :: Step m n1 -> Step m n2 -> n1 :~: n2
stepDeterm (XiApp1 s1)  (XiApp1 s2)  = case stepDeterm s1 s2 of Refl -> Refl
stepDeterm (XiApp1 s1)  (XiApp2 v _) = absurd (valueCannotStep v s1)
stepDeterm (XiApp1 s1)  (BetaLam _)  = absurd (valueCannotStep VLam s1)
stepDeterm (XiApp2 v _) (XiApp1 s2)  = absurd (valueCannotStep v s2)
stepDeterm (XiApp2 _ s1) (XiApp2 _ s2) = case stepDeterm s1 s2 of Refl -> Refl
stepDeterm (XiApp2 _ s1) (BetaLam v) = absurd (valueCannotStep v s1)
stepDeterm (BetaLam _)  (XiApp1 s2)  = absurd (valueCannotStep VLam s2)
stepDeterm (BetaLam v)  (XiApp2 _ s2) = absurd (valueCannotStep v s2)
stepDeterm (BetaLam _)  (BetaLam _)  = Refl
stepDeterm (XiSuc s1)   (XiSuc s2)   = case stepDeterm s1 s2 of Refl -> Refl
stepDeterm (XiCase s1)  (XiCase s2)  = case stepDeterm s1 s2 of Refl -> Refl
stepDeterm (XiCase s1)  BetaZero     = absurd (valueCannotStep VZero s1)
stepDeterm (XiCase s1)  (BetaSuc v)  = absurd (valueCannotStep (VSuc v) s1)
stepDeterm BetaZero     (XiCase s2)  = absurd (valueCannotStep VZero s2)
stepDeterm BetaZero     BetaZero     = Refl
stepDeterm (BetaSuc v)  (XiCase s2)  = absurd (valueCannotStep (VSuc v) s2)
stepDeterm (BetaSuc _)  (BetaSuc _)  = Refl
stepDeterm BetaMu       BetaMu       = Refl

{-# LINE 422 "content/part2/Properties.md" #-}
-- | Retained runtime witness for a promoted `Term`.
data TermW (t :: Term) where
  MkTermW :: foreach (t :: Term) -> TermW t

-- | Compute the retained target term of any one-step reduction.
stepTarget :: foreach (m :: Term) -> Step m n -> TermW n
stepTarget source step = case source of
  Var _   -> case step of {}
  Lam _ _ -> case step of {}
  TZero   -> case step of {}
  App l r -> case step of
    XiApp1 sl -> case stepTarget l sl of
      MkTermW l' -> MkTermW (App l' r)
    XiApp2 _ sr -> case stepTarget r sr of
      MkTermW r' -> MkTermW (App l r')
    BetaLam @_ @binder @bodyIndex _ ->
      let shape :: IsLam l
          shape = IsLam @binder @bodyIndex
      in case l of
        Lam x body    -> MkTermW (substTerm body x r)
        Var _         -> case shape of {}
        App _ _       -> case shape of {}
        TZero         -> case shape of {}
        TSuc _        -> case shape of {}
        TCase _ _ _ _ -> case shape of {}
        TMu _ _       -> case shape of {}
  TSuc m -> case step of
    XiSuc sm -> case stepTarget m sm of
      MkTermW m' -> MkTermW (TSuc m')
  TCase l z x n -> case step of
    XiCase sl -> case stepTarget l sl of
      MkTermW l' -> MkTermW (TCase l' z x n)
    BetaZero -> MkTermW z
    BetaSuc @value _ ->
      let shape :: IsSuc l
          shape = IsSuc @value
      in case l of
        TSuc v        -> MkTermW (substTerm n x v)
        Var _         -> case shape of {}
        Lam _ _       -> case shape of {}
        App _ _       -> case shape of {}
        TZero         -> case shape of {}
        TCase _ _ _ _ -> case shape of {}
        TMu _ _       -> case shape of {}
  TMu x m -> case step of
    BetaMu -> MkTermW (substTerm m x (TMu x m))

-- | Multi-step preservation (`preserve*`): `M —↠ N` preserves closed typing.
preserveSteps :: foreach (m :: Term) -> HasType CEmpty m a -> Steps m n -> HasType CEmpty n a
preserveSteps m tm steps = case steps of
  StepsRefl     -> tm
  StepsCons s r -> case stepTarget m s of
    MkTermW m' -> preserveSteps m' (preserve m tm s) r

-- | Result of gas-bounded evaluation (`Finished`): either a value or out-of-gas trace.
data EvalResult (m :: Term) where
  Done     :: Steps m v -> Value v -> EvalResult m
  OutOfGas :: Steps m n -> EvalResult m

-- | PLFA's verified gas-bounded evaluator built directly from `progress` and `preserve`!
eval :: Nat -> TermW m -> HasType CEmpty m a -> EvalResult m
eval Zero     _           _  = OutOfGas StepsRefl
eval (Succ g) (MkTermW m) tm = case progress tm of
  PDone v -> Done StepsRefl v
  PStep s -> case stepTarget m s of
    wm' -> case eval g wm' (preserve m tm s) of
      Done ss v   -> Done (StepsCons s ss) v
      OutOfGas ss -> OutOfGas (StepsCons s ss)
