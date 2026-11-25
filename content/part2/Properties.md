---
title: "Properties: Progress and Preservation"
prev: /Lambda/
next: /DeBruijn/
src: content/part2/Properties.md
module: PLFH.Part2.Properties
plfaChapter: https://plfa.inf.ed.ac.uk/Properties/
---

Robin Milner famously summarized the guarantee of a sound type system as:

> *"Well-typed programs cannot go wrong."*

In 1994, Andrew Wright and Matthias Felleisen gave a remarkably clean,
syntactic method for proving Milner's slogan directly from small-step
operational semantics. Their recipe splits **type safety** into two theorems:

1. **Progress (`progress`)**: Every closed, well-typed term is either already a
   value or can take a reduction step. It can never get *stuck* in an
   unrecognized non-value state (such as trying to apply `zero` to an argument).
2. **Preservation (`preserve`)**, also called *subject reduction*: If a closed,
   well-typed term takes a reduction step, the resulting term still has the
   exact same type.

Together, Progress and Preservation tell us by induction that a well-typed
program can reduce step after step without ever losing its type or getting
stuck: either it eventually reaches a value of the expected type, or it runs
forever. Even better, because our proofs are constructive Dependent Haskell
functions, combining `progress` and `preserve` directly yields a **verified
interpreter** (`eval`) that computes reduction traces up to a given gas limit!

## Imports

We import equality `(:~:)`, `Void`/`absurd`, Peano naturals `Nat` (for gas and
variable identifiers), `Not`, and all of the syntax, reduction, and typing
relations from [Lambda](/Lambda/).

```haskell
{-# LANGUAGE DependentTypes #-}
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
  , Normal
  , Stuck (..)
  , unstuck
  , wttdgs
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
```

## Canonical Forms

Before proving Progress, we need to know what *shape* a closed value of a given
type must have—this is the **Canonical Forms Lemma** (`canonical`):

- A closed value of function type `TArr a b` *must* be a lambda abstraction
  `Lam x n`, whose body `n` has type `b` in `CExt CEmpty x a`.
- A closed value of natural-number type `TNat` *must* be either `TZero` or
  `TSuc v`, where `v` is itself a closed value of type `TNat`.

```haskell
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
```

Because `Value` only has constructors for `Lam`, `TZero`, and `TSuc`, GHC's
pattern-match exhaustiveness checker immediately rules out every mismatched
pair (like `TZeroT` with `VLam`, or `TApp` with any `Value`).

## Progress

A closed term `m` makes **progress** (`Progress m`) if either there exists some
term `n` such that `Step m n` (`PStep`), or `m` is already a value (`PDone`):

```haskell
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
```

Walk through the `TApp tl tm` case to see how cleanly `progress` works:
1. By induction on `tl`, either `l` steps (`PStep s`), so `App l m` steps via
   `XiApp1 s`, or `l` is already a value (`PDone vl`).
2. If `l` is a value, then by induction on `tm`, either `m` steps (`XiApp2 vl s`)
   or `m` is also a value (`PDone vm`).
3. When *both* `l` and `m` are values, `canonical tl vl` proves that `l` must be
   `Lam x n`, unlocking `BetaLam vm`!

The `TVar x` case is impossible (`case x of {}`) because the context is empty
(`CEmpty`), so `Lookup CEmpty x a` has no constructors. Notice that `progress`
has the **exact same statement, hypotheses, and proof structure** as PLFA—with
no type families and no coercions—and passes GHC's Core Lint and STG Lint.
(Later in the chapter, `preserve` and `eval` take a small structural witness
`TermW m` so pattern matching can inspect the erased term index `m`.)

## Structural context lemmas (`extCtx`, `renameTyping`, `weakenTyping`, `dropTyping`, `swapTyping`)

To prove Preservation, we must show that β-reduction (`substTerm`) preserves
typing. Because `substTerm` descends underneath binders (`Lam`, `TCase`, `TMu`),
we first prove a general **renaming** (context-mapping) lemma: if every lookup
valid in context `g` can be mapped to a lookup in context `d`, then every
typing derivation in `g` transports to `d`.

From `renameTyping`, three essential structural properties follow in a few lines
each:

- **Weakening (`weakenTyping`)**: a closed term (`CEmpty`) is well-typed in *any*
  context `g` (needed when substituting a closed value at a variable occurrence).
- **Drop (`dropTyping`)**: when a variable `x` is bound twice in a row, the
  shadowed inner binding can be dropped (needed when substitution stops at a
  shadowing binder).
- **Swap (`swapTyping`)**: two adjacent bindings for *distinct* variables
  `x /= y` can be exchanged (needed to keep the substituted variable at the end
  of the context when descending under a different binder).

```haskell
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
```

## Substitution Typing Lemma (`substTyping`)

The **Substitution Lemma** says: if `v` is a closed term of type `a`
(`HasType CEmpty v a`) and `t` has type `b` in `CExt g y a`, then substituting
`v` for `y` in `t` yields a term `substTerm t y v` of type `b` in `g`.

Because `substTerm` branches on `eqId x y :: Bool`, we first package decidable
equality on `Id` together with the exact Boolean result of `eqId x y` in
`NameDecision x y`. Pattern matching on `decide x y` simultaneously refines
`x :~: y` (or `Not (x :~: y)`) *and* reduces `eqId x y` to `True` or `False` in
`substTerm`'s type!

- When `x` matches `y`, a `Lam`/`TCase`/`TMu` binder shadows `y`, so `substTerm`
  leaves the body alone and `dropTyping` removes the shadowed `y : a` entry.
- When `x` differs from `y`, `swapTyping` swaps `x` and `y` so that `y : a` is
  again the rightmost context entry, ready for the recursive call to
  `substTyping`.

```haskell
-- | Decidable identifier equality paired with the Boolean result of `eqId`.
data NameDecision (x :: Id) (y :: Id) where
    Same :: x :~: y -> eqId x y :~: True -> NameDecision x y
    Different :: (x :~: y -> Void) -> eqId x y :~: False -> NameDecision x y

-- | Decide whether two variable identifiers are equal, reflecting `eqId`.
decide :: foreach (x y :: Id) -> NameDecision x y
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
```

## Preservation (`preserve`)

Now we prove **Preservation**: if a closed term `m` has type `a` and reduces in
one step `Step m n`, then `n` also has type `a`.

We retain `foreach (m :: Term)` so that we have the runtime syntax of `m` in
hand for recursive calls and for `substTyping`. In the two beta cases whose
redexes constrain a subterm (`BetaLam` forces the function position `l` to be a
`Lam`; `BetaSuc` forces the scrutinee `l` to be a `TSuc`), the lightweight
shape witnesses `IsLam` and `IsSuc` carry that constraint across the runtime
pattern match on `l` so every impossible branch closes with an empty case.

```haskell
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
```

## Determinism (`valueCannotStep`, `stepDeterm`)

Our call-by-value operational semantics is **deterministic**: every term can
reduce in at most one way! First we show that no value can take a step
(`valueCannotStep`), and then structural induction on two steps `Step m n1` and
`Step m n2` proves `n1 :~: n2` (`stepDeterm`), using `valueCannotStep` to
eliminate every overlapping `ξ`/`β` pair:

```haskell
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
```

## Multi-Step Preservation (`preserveSteps`) and Verified Evaluation (`eval`)

Because our language includes general recursion `TMu`, a well-typed term need
not terminate! How can we write a total evaluator for a Turing-complete
language? PLFA borrows a well-known idea from smart-contract virtual machines
such as Ethereum: supply an explicit **gas** budget (`Nat`).

- At each step, if gas is `Zero`, evaluation stops cleanly with `OutOfGas`.
- If gas is `Succ g`, we call `progress tm`:
  - If `PDone v`, we have reached a value (`Done StepsRefl v`)!
  - If `PStep s`, we compute the retained target term `wm' = stepTarget m s`,
    transport the typing derivation via `preserve m tm s`, and recurse with `g`
    units of gas remaining!

```haskell
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
```

Notice the payoff: `eval` does not merely compute an answer—it returns a
machine-checked proof `Steps m v` that the source term `m` reduces to a value
`v`, built automatically from our Progress and Preservation theorems!

## Well-typed terms don't get stuck (`wttdgs`)

Progress and multi-step Preservation combine immediately into Robin Milner's
famous slogan: **well-typed terms don't get stuck**. A term is *normal* if it
cannot take any step, and *stuck* if it is normal yet not a value (for example,
applying `0` to `0`, or taking `case` of a lambda):

```haskell
-- | A term is in normal form if no reduction step leaves it (`Normal`).
type Normal (m :: Term) = forall (n :: Term). Step m n -> Void

-- | A term is stuck if it is in normal form yet is not a value (`Stuck`).
data Stuck (m :: Term) where
  MkStuck :: Normal m -> Not (Value m) -> Stuck m

-- | No closed well-typed term is stuck (`unstuck`).
unstuck :: HasType CEmpty m a -> Stuck m -> Void
unstuck tm (MkStuck norm notVal) = case progress tm of
  PDone v -> notVal v
  PStep s -> norm s

-- | Well-typed terms don't get stuck (`wttdgs`):
-- a closed well-typed term can never reduce to a stuck term!
wttdgs :: foreach (m :: Term) -> HasType CEmpty m a -> Steps m n -> Stuck n -> Void
wttdgs m tm steps stuck = unstuck (preserveSteps m tm steps) stuck
```

## Exercises

#### Exercise `Progress-¬` (practice)

Show that well-typedness is *not* necessary for progress: exhibit an ill-typed
closed term `m` that nevertheless satisfies `Progress m` (for instance,
`Lam Zero (App TZero TZero)` is already a value `VLam`, even though its body is
ill-typed!).

#### Exercise `Preservation-¬` (practice)

Show that a closed term can take a step to a well-typed term without itself
being well-typed (for instance, `TCase TZero TZero Zero (App TZero TZero)`
steps via `BetaZero` to `TZero`!).

#### Exercise `eval-example` (practice)

Using `eval` with gas `5`, evaluate `App (Lam Zero (Var Zero)) TZero` and
`TCase (TSuc TZero) TZero Zero (Var Zero)`, verifying both return `Done` with
`VZero`.

## Changes from PLFA

- Adapted from [Properties](https://plfa.inf.ed.ac.uk/Properties/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/Properties.lagda.md)),
  licensed under CC BY 4.0.
- `Canonical`, `canonical`, `Progress`, `progress`, `valueCannotStep`,
  `stepDeterm`, `extCtx`, `renameTyping`, `weakenTyping`, `dropTyping`,
  `swapTyping`, `substTyping`, `preserve`, `preserveSteps`, and the verified
  gas-bounded evaluator `eval` are all checked direct ports passing
  `-dcore-lint -dstg-lint`.
