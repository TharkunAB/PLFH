---
title: "Properties: Progress and Preservation"
prev: /Lambda/
next: /DeBruijn/
src: content/part2/Properties.md
module: PLFH.Part2.Properties
plfaChapter: https://plfa.inf.ed.ac.uk/Properties/
---

```haskell
{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, TypeAbstractions, TypeApplications, TypeOperators #-}
module PLFH.Part2.Properties
  ( Canonical (..)
  , canonical
  , Progress (..)
  , progress
  , extCtx
  , renameTyping
  , weakenTyping
  , dropTyping
  , swapTyping
  , substTyping
  , preserve
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
  , Term (..)
  , Ty (..)
  , Value (..)
  , eqId
  , substTerm
  )
```

Type safety for the simply-typed lambda calculus rests on two classic
theorems due to Wright and Felleisen:

1. **Progress:** Every closed, well-typed term is either already a value or
   can take a step (`progress`).
2. **Preservation (Subject Reduction):** If a closed, well-typed term takes
   a step, the resulting term has the same type (`preserve`).

We prove canonical forms and progress first. The context lemmas then let
us carry a typing derivation under binders. We use them to prove
substitution and preservation.

## Canonical forms

A closed value of function type must be a lambda abstraction, and a closed
value of natural-number type must be `TZero` or `TSuc v`:

```haskell
-- | Canonical form of a closed well-typed value.
data Canonical (m :: Term) (a :: Ty) where
  CLam  :: HasType ('CExt 'CEmpty x a) n b -> Canonical ('Lam x n) ('TArr a b)
  CZero :: Canonical 'TZero 'TNat
  CSuc  :: Value v -> HasType 'CEmpty v 'TNat -> Canonical ('TSuc v) 'TNat

-- | Every closed well-typed value has a canonical form matching its type.
canonical :: HasType 'CEmpty v a -> Value v -> Canonical v a
canonical (TLam tn)  VLam      = CLam tn
canonical TZeroT     VZero     = CZero
canonical (TSucT tv) (VSuc vv) = CSuc vv tv
```

## Progress

A closed term `m` makes *progress* if either there exists `n` such that
`Step m n`, or `Value m`:

```haskell
-- | Evidence that a closed term either steps or is already a value.
data Progress (m :: Term) where
  PStep :: Step m n -> Progress m
  PDone :: Value m  -> Progress m

-- | Progress theorem: every closed well-typed term either steps or is a value.
progress :: HasType 'CEmpty m a -> Progress m
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
```

Look how clean that is: `progress` has the **exact same statement, hypotheses,
and proof structure** as PLFA—no singletons, no type families, no
coercions—and passes GHC's Core Lint and STG Lint!

## Structural context lemmas for Preservation (`ext`, `rename`, `weaken`, `drop`, `swap`)

Before proving substitution and preservation, PLFA develops context renaming
and its corollaries. Every single one of these structural lemmas ports
directly to Dependent Haskell:

```haskell
-- | Extend a context inclusion under a newly bound variable `x : a`.
extCtx :: (forall y b. Lookup g y b -> Lookup d y b)
       -> Lookup ('CExt g x a) y b
       -> Lookup ('CExt d x a) y b
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
weakenTyping :: HasType 'CEmpty m a -> HasType g m a
weakenTyping = renameTyping (\case {})

-- | Drop a shadowed duplicate binding for `x` from the context.
dropTyping :: HasType ('CExt ('CExt g x a) x b) m c
           -> HasType ('CExt g x b) m c
dropTyping = renameTyping dropLookup
  where
    dropLookup :: Lookup ('CExt ('CExt g x a) x b) y c -> Lookup ('CExt g x b) y c
    dropLookup LZ                = LZ
    dropLookup (LS neq LZ)       = absurd (neq Refl)
    dropLookup (LS neq (LS _ p)) = LS neq p

-- | Swap two distinct adjacent bindings `x /= y` in the context.
swapTyping :: forall g x y a b m c.
              Not (x :~: y)
           -> HasType ('CExt ('CExt g x a) y b) m c
           -> HasType ('CExt ('CExt g y b) x a) m c
swapTyping xNeqY = renameTyping swapLookup
  where
    swapLookup :: Lookup ('CExt ('CExt g x a) y b) z d
               -> Lookup ('CExt ('CExt g y b) x a) z d
    swapLookup LZ                         = LS (\Refl -> xNeqY Refl) LZ
    swapLookup (LS _ LZ)                  = LZ
    swapLookup (LS zNeqY (LS zNeqX rest)) = LS zNeqX (LS zNeqY rest)
```

## Substitution and Preservation

The substitution lemma takes a typing derivation for the closed
replacement and one for the original term in a context ending in
`y : a`. The proof checks the same identifier comparison as `substTerm`.
A matching binder shadows `y`. Under a different binder, the proof uses
`swapTyping` to move the substituted binding to the end of the context.

```haskell
data NameDecision (x :: Id) (y :: Id) where
    Same :: x :~: y -> eqId x y :~: 'True -> NameDecision x y
    Different :: (x :~: y -> Void) -> eqId x y :~: 'False -> NameDecision x y

decide :: foreach (x :: Id) -> foreach (y :: Id) -> NameDecision x y
decide Zero Zero = Same Refl Refl
decide Zero (Succ _) = Different (\case {}) Refl
decide (Succ _) Zero = Different (\case {}) Refl
decide (Succ x) (Succ y) = case decide x y of
    Same Refl Refl -> Same Refl Refl
    Different neq Refl -> Different (\Refl -> neq Refl) Refl

-- | Substitute a closed well-typed term for the last context entry.
substTyping :: forall g a b v. foreach (y :: Id) -> foreach (t :: Term)
      -> HasType 'CEmpty v a -> HasType ('CExt g y a) t b -> HasType g (substTerm t y v) b
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
```

Preservation takes the source term, its closed typing derivation, and the
step. The retained source term supplies the raw syntax for recursive
calls and substitution. In the two beta cases with an inner constructor
pattern, `IsLam` and `IsSuc` record the shape imposed by the step. Each
impossible alternative eliminates that shape witness.

```haskell
data IsLam (m :: Term) where
    IsLam :: IsLam ('Lam x body)

data IsSuc (m :: Term) where
    IsSuc :: IsSuc ('TSuc v)

-- | A step preserves the type of a closed term.
preserve :: foreach (m :: Term) -> HasType 'CEmpty m a -> Step m n -> HasType 'CEmpty n a
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
         -> HasType 'CEmpty v a
         -> HasType 'CEmpty ('Lam x body) ('TArr a b)
         -> HasType 'CEmpty (substTerm body x v) b
substLam x body replacement (TLam tb) = substTyping x body replacement tb

substSuc :: foreach (v :: Term) -> foreach (x :: Id) -> foreach (body :: Term)
         -> HasType 'CEmpty ('TSuc v) 'TNat
         -> HasType ('CExt 'CEmpty x 'TNat) body a
         -> HasType 'CEmpty (substTerm body x v) a
substSuc _ x body (TSucT tv) tn = substTyping x body tv tn
```

## Changes from PLFA

- Adapted from [Properties](https://plfa.inf.ed.ac.uk/Properties/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/Properties.lagda.md)).
- `Canonical`, `canonical`, `Progress`, `progress` (full closed well-typed
  progress theorem!), `extCtx`, `renameTyping`, `weakenTyping`, `dropTyping`,
  and `swapTyping` are all **checked direct ports** passing `-dcore-lint -dstg-lint`.
- `substTyping` uses the equations of the ordinary `substTerm` function.
  `preserve` checks all eight one-step constructors.
