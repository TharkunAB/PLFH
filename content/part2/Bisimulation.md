---
title: "Bisimulation: Relating reduction systems"
prev: /More/
next: /BigStep/
src: content/part2/Bisimulation.md
module: PLFH.Part2.Bisimulation
plfaChapter: https://plfa.inf.ed.ac.uk/Bisimulation/
---

Suppose you have a source language with syntactic sugar—such as local
`let`-bindings `let x = M in N` from [More](/More/)—and you want to prove
that desugaring `let x = M in N` into an immediately applied lambda
`(λ x. N) M` **preserves every observable step and final value**!

The classic tool from concurrency theory and programming-language metatheory
(introduced by David Park and Robin Milner) is **simulation** and
**bisimulation**. Given a relation `M ~ M'` connecting source terms to their
desugared counterparts:

```text
    M  ~  M'
    |     :
    v     v
    N  ~  N'
```

- `~` is a **lock-step forward simulation** (`sim`) if whenever `M ~ M'` and
  `M —→ N`, there exists `N'` such that `M' —→ N'` and `N ~ N'` (and values
  correspond to values via `simValue`).
- `~` is a **lock-step backward simulation** (`simInv`, PLFA's `sim⁻¹`) if
  whenever `M ~ M'` and `M' —→ N'`, there exists `N` such that `M —→ N` and
  `N ~ N'` (and values correspond in reverse via `simValueInv`).
- Together, forward and backward simulation make `~` a **bisimulation**:
  neither `let x = M in N` nor `(λ x. N) M` can take a step or reach a value
  that the other cannot match step for step!

In this chapter we define the full 20-constructor structural relation `SimRel`
(`_~_`) over all 19 term forms of [More](/More/) plus the desugaring rule
`SimLetApp :: SimRel m m' -> SimRel n n' -> SimRel (Let m n) (App (Lam n') m')`,
and prove with `-Werror=incomplete-patterns`:

1. **`simRefl`** (`~-refl`) and **`simTrans`** across all 19 term constructors;
2. **`simValue`** (`~-val`) and **`simValueInv`** (`~-val⁻¹`) across all 9 value forms;
3. **`valNoStep`** (no value can ever take a step in `MoreProgress.Step`);
4. Complete 27-rule **lock-step forward simulation `sim`** and **backward simulation `simInv`** (PLFA Exercise `sim⁻¹`), plus multi-step **`simSteps`** and **`simStepsInv`**;
5. Assumption-free concrete closed bisimulation witnesses (`letDesugarSim`, `letDesugarSteps`, `letDesugarStepsInv`) stepping `let x = fst (0, 1) in suc x` alongside `(λ x. suc x) (fst (0, 1))` through both `XiLet` ↔ `XiApp2 VLam` and `BetaLet` ↔ `BetaLam`!

## Imports

```haskell
{-# LANGUAGE AllowAmbiguousTypes, DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs, Modifiers #-}
{-# LANGUAGE PolyKinds, RankNTypes, ScopedTypeVariables, StandaloneKindSignatures, TypeAbstractions, TypeApplications #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
module PLFH.Part2.Bisimulation
  ( SimRel (..)
  , simRefl
  , simTrans
  , simValue
  , simValueInv
  , valNoStep
  , Renaming
  , simRename
  , Leg (..)
  , LegInv (..)
  , SubstCompat (..)
  , sim
  , simInv
  , simSteps
  , simStepsInv
  , letDesugarSim
  , letDesugarSteps
  , letDesugarStepsInv
  ) where

import Data.Kind (Type)
import Data.Void (Void, absurd)
import GHC.Exts (U)
import qualified PLFH.Part2.More as M
import qualified PLFH.Part2.MoreProgress as MP
```

## The bisimulation relation (`_~_`)

Rather than including a catch-all reflexivity constructor, we follow upstream
PLFA and define `SimRel` by structural congruence over every constructor of
`M.Term` **plus** the desugaring constructor **`SimLetApp`**:

- `SimLet sm sn` relates `Let m n` to `Let m' n'` (leaving a `let` untouched);
- `SimLetApp sm sn` relates `Let m n` to `App (Lam n') m'` (desugaring a `let`
  into an applied lambda!).

Keeping `SimRel` purely structural gives exact GADT inversion in every proof:
matching `SimRel (Let m n) t'` leaves *only* `SimLet` and `SimLetApp`, and
matching `SimRel t (App l' m')` leaves *only* `SimApp` and `SimLetApp`!

```haskell
-- | Structural bisimulation relation relating `let x = m in n` to `(λx. n') m'`
-- across all 19 constructors of `PLFH.Part2.More.Term`.
type SimRel :: forall (g :: M.Ctx) (a :: M.Ty). M.Term g a -> M.Term g a -> Type
data SimRel m m' where
  SimVar     :: SimRel (M.Var x) (M.Var x)
  SimLam     :: SimRel n n' -> SimRel (M.Lam n) (M.Lam n')
  SimApp     :: SimRel l l' -> SimRel m m' -> SimRel (M.App l m) (M.App l' m')
  SimZero    :: SimRel M.Zero M.Zero
  SimSuc     :: SimRel m m' -> SimRel (M.Suc m) (M.Suc m')
  SimCaseNat :: SimRel n n' -> SimRel z z' -> SimRel s s'
             -> SimRel (M.CaseNat n z s) (M.CaseNat n' z' s')
  SimMu      :: SimRel n n' -> SimRel (M.Mu n) (M.Mu n')
  SimLet     :: SimRel m m' -> SimRel n n' -> SimRel (M.Let m n) (M.Let m' n')
  SimLetApp  :: SimRel m m' -> SimRel n n' -> SimRel (M.Let m n) (M.App (M.Lam n') m')
  SimTT      :: SimRel M.TT M.TT
  SimPair    :: SimRel l l' -> SimRel r r' -> SimRel (M.Pair l r) (M.Pair l' r')
  SimFst     :: SimRel p p' -> SimRel (M.Fst p) (M.Fst p')
  SimSnd     :: SimRel p p' -> SimRel (M.Snd p) (M.Snd p')
  SimInl     :: SimRel x x' -> SimRel (M.Inl x) (M.Inl x')
  SimInr     :: SimRel y y' -> SimRel (M.Inr y) (M.Inr y')
  SimCaseSum :: SimRel s s' -> SimRel l l' -> SimRel r r'
             -> SimRel (M.CaseSum s l r) (M.CaseSum s' l' r')
  SimAbsurd  :: SimRel m m' -> SimRel (M.Absurd m) (M.Absurd m')
  SimNil     :: SimRel M.Nil M.Nil
  SimCons    :: SimRel x x' -> SimRel xs xs' -> SimRel (M.Cons x xs) (M.Cons x' xs')
  SimCaseLst :: SimRel s s' -> SimRel n n' -> SimRel c c'
             -> SimRel (M.CaseLst s n c) (M.CaseLst s' n' c')
```

### Reflexivity (`~-refl`) and transitivity

Every term is related to itself by structural induction over `foreach (m :: M.Term g a)`,
and `SimRel` is transitive (including when a `Let` desugars in either the first
or second step):

```haskell
-- | Reflexivity (`~-refl`): every extended STLC term is related to itself.
simRefl :: forall (g :: M.Ctx) (a :: M.Ty). foreach (m :: M.Term g a) -> SimRel m m
simRefl t = case t of
  M.Var _         -> SimVar
  M.Lam n         -> SimLam (simRefl n)
  M.App l m       -> SimApp (simRefl l) (simRefl m)
  M.Zero          -> SimZero
  M.Suc n         -> SimSuc (simRefl n)
  M.CaseNat n z s -> SimCaseNat (simRefl n) (simRefl z) (simRefl s)
  M.Mu n          -> SimMu (simRefl n)
  M.Let m n       -> SimLet (simRefl m) (simRefl n)
  M.TT            -> SimTT
  M.Pair l r      -> SimPair (simRefl l) (simRefl r)
  M.Fst p         -> SimFst (simRefl p)
  M.Snd p         -> SimSnd (simRefl p)
  M.Inl x         -> SimInl (simRefl x)
  M.Inr y         -> SimInr (simRefl y)
  M.CaseSum s l r -> SimCaseSum (simRefl s) (simRefl l) (simRefl r)
  M.Absurd m      -> SimAbsurd (simRefl m)
  M.Nil           -> SimNil
  M.Cons x xs     -> SimCons (simRefl x) (simRefl xs)
  M.CaseLst s n c -> SimCaseLst (simRefl s) (simRefl n) (simRefl c)

-- | Transitivity of `SimRel`: `l ~ m` and `m ~ n` implies `l ~ n`.
simTrans :: SimRel l m -> SimRel m n -> SimRel l n
simTrans SimVar                 SimVar                  = SimVar
simTrans (SimLam s1)            (SimLam s2)             = SimLam (simTrans s1 s2)
simTrans (SimApp l1 m1)         (SimApp l2 m2)          = SimApp (simTrans l1 l2) (simTrans m1 m2)
simTrans SimZero                SimZero                 = SimZero
simTrans (SimSuc s1)            (SimSuc s2)             = SimSuc (simTrans s1 s2)
simTrans (SimCaseNat n1 z1 s1)  (SimCaseNat n2 z2 s2)   = SimCaseNat (simTrans n1 n2) (simTrans z1 z2) (simTrans s1 s2)
simTrans (SimMu s1)             (SimMu s2)              = SimMu (simTrans s1 s2)
simTrans (SimLet m1 n1)         (SimLet m2 n2)          = SimLet (simTrans m1 m2) (simTrans n1 n2)
simTrans (SimLet m1 n1)         (SimLetApp m2 n2)       = SimLetApp (simTrans m1 m2) (simTrans n1 n2)
simTrans (SimLetApp m1 n1)      (SimApp (SimLam n2) m2) = SimLetApp (simTrans m1 m2) (simTrans n1 n2)
simTrans SimTT                  SimTT                   = SimTT
simTrans (SimPair l1 r1)        (SimPair l2 r2)         = SimPair (simTrans l1 l2) (simTrans r1 r2)
simTrans (SimFst p1)            (SimFst p2)             = SimFst (simTrans p1 p2)
simTrans (SimSnd p1)            (SimSnd p2)             = SimSnd (simTrans p1 p2)
simTrans (SimInl x1)            (SimInl x2)             = SimInl (simTrans x1 x2)
simTrans (SimInr y1)            (SimInr y2)             = SimInr (simTrans y1 y2)
simTrans (SimCaseSum s1 l1 r1)  (SimCaseSum s2 l2 r2)   = SimCaseSum (simTrans s1 s2) (simTrans l1 l2) (simTrans r1 r2)
simTrans (SimAbsurd m1)         (SimAbsurd m2)          = SimAbsurd (simTrans m1 m2)
simTrans SimNil                 SimNil                  = SimNil
simTrans (SimCons x1 xs1)       (SimCons x2 xs2)        = SimCons (simTrans x1 x2) (simTrans xs1 xs2)
simTrans (SimCaseLst s1 n1 c1)  (SimCaseLst s2 n2 c2)   = SimCaseLst (simTrans s1 s2) (simTrans n1 n2) (simTrans c1 c2)
```

## Value preservation (`~-val`, `~-val⁻¹`) and value irreducibility

Because neither `Let` nor `App` is a value, `SimLetApp` can never match a value
on either side! Matching on `M.Value` first lets GHC's `-Werror=incomplete-patterns`
verify that every value form corresponds bijectively across `SimRel`, and that
no value can take a step (`valNoStep`)—the key lemma that rules out `XiApp1`
on `App (Lam n') m'` in backward simulation `simInv`!

```haskell
-- | Forward value preservation (`~-val`): all 9 value constructors.
simValue :: SimRel m m' -> M.Value m -> M.Value m'
simValue rel val = case val of
  M.VLam        -> case rel of { SimLam _      -> M.VLam }
  M.VZero       -> case rel of { SimZero       -> M.VZero }
  M.VSuc v      -> case rel of { SimSuc s      -> M.VSuc (simValue s v) }
  M.VTT         -> case rel of { SimTT         -> M.VTT }
  M.VPair v1 v2 -> case rel of { SimPair s1 s2 -> M.VPair (simValue s1 v1) (simValue s2 v2) }
  M.VInl v      -> case rel of { SimInl s      -> M.VInl (simValue s v) }
  M.VInr v      -> case rel of { SimInr s      -> M.VInr (simValue s v) }
  M.VNil        -> case rel of { SimNil        -> M.VNil }
  M.VCons v1 v2 -> case rel of { SimCons s1 s2 -> M.VCons (simValue s1 v1) (simValue s2 v2) }

-- | Backward value preservation (`~-val⁻¹`): all 9 value constructors.
simValueInv :: SimRel m m' -> M.Value m' -> M.Value m
simValueInv rel val = case val of
  M.VLam        -> case rel of { SimLam _      -> M.VLam }
  M.VZero       -> case rel of { SimZero       -> M.VZero }
  M.VSuc v      -> case rel of { SimSuc s      -> M.VSuc (simValueInv s v) }
  M.VTT         -> case rel of { SimTT         -> M.VTT }
  M.VPair v1 v2 -> case rel of { SimPair s1 s2 -> M.VPair (simValueInv s1 v1) (simValueInv s2 v2) }
  M.VInl v      -> case rel of { SimInl s      -> M.VInl (simValueInv s v) }
  M.VInr v      -> case rel of { SimInr s      -> M.VInr (simValueInv s v) }
  M.VNil        -> case rel of { SimNil        -> M.VNil }
  M.VCons v1 v2 -> case rel of { SimCons s1 s2 -> M.VCons (simValueInv s1 v1) (simValueInv s2 v2) }

-- | Values never step in extended call-by-value STLC.
valNoStep :: M.Value m -> MP.Step m n -> Void
valNoStep val st = case val of
  M.VLam       -> case st of {}
  M.VZero      -> case st of {}
  M.VSuc v     -> case st of { MP.XiSuc s -> valNoStep v s }
  M.VTT        -> case st of {}
  M.VPair v w  -> case st of { MP.XiPair1 s -> valNoStep v s; MP.XiPair2 _ s -> valNoStep w s }
  M.VInl v     -> case st of { MP.XiInl s -> valNoStep v s }
  M.VInr v     -> case st of { MP.XiInr s -> valNoStep v s }
  M.VNil       -> case st of {}
  M.VCons v vs -> case st of { MP.XiCons1 s -> valNoStep v s; MP.XiCons2 _ s -> valNoStep vs s }
```

## Simulation commutes with renaming (`~-rename`)

A renaming maps each lookup in context `g` to a lookup of the same type in
context `d`. Because a renaming may send two distinct variables to the same
target variable, its arrow is **unmatchable** (`%U ->`)! With checked source
equations for `M.rename` and `M.ext` from [More](/More/), GHC verifies the
complete 20-constructor structural renaming theorem `simRename` directly—including
`SimLetApp`, `SimCaseSum`, and shifting through *two* simultaneous binders in
`SimCaseLst` (`@(M.ext (M.ext r))`)! (Verified across the module boundary in
`PLFH.Part2.BisimulationRenaming`, `clients/PLFH/Part2/BisimulationRenaming.hs`.)

```haskell
-- | A sort-preserving map between lookup contexts.
type Renaming g d = forall x. M.Lookup g x %U -> M.Lookup d x

-- | Renaming preserves the structural simulation relation across all 20 constructors!
simRename :: forall g d a (r :: Renaming g d) (m :: M.Term g a) (n :: M.Term g a).
             SimRel m n -> SimRel (M.rename r m) (M.rename r n)
simRename SimVar = SimVar
simRename (SimLam s) = SimLam (simRename @_ @_ @_ @(M.ext r) s)
simRename (SimApp l m) = SimApp (simRename @_ @_ @_ @r l) (simRename @_ @_ @_ @r m)
simRename SimZero = SimZero
simRename (SimSuc s) = SimSuc (simRename @_ @_ @_ @r s)
simRename (SimCaseNat n z s) =
  SimCaseNat (simRename @_ @_ @_ @r n) (simRename @_ @_ @_ @r z)
             (simRename @_ @_ @_ @(M.ext r) s)
simRename (SimMu s) = SimMu (simRename @_ @_ @_ @(M.ext r) s)
simRename (SimLet m n) = SimLet (simRename @_ @_ @_ @r m) (simRename @_ @_ @_ @(M.ext r) n)
simRename (SimLetApp m n) = SimLetApp (simRename @_ @_ @_ @r m) (simRename @_ @_ @_ @(M.ext r) n)
simRename SimTT = SimTT
simRename (SimPair l r') = SimPair (simRename @_ @_ @_ @r l) (simRename @_ @_ @_ @r r')
simRename (SimFst p) = SimFst (simRename @_ @_ @_ @r p)
simRename (SimSnd p) = SimSnd (simRename @_ @_ @_ @r p)
simRename (SimInl s) = SimInl (simRename @_ @_ @_ @r s)
simRename (SimInr s) = SimInr (simRename @_ @_ @_ @r s)
simRename (SimCaseSum s l r') =
  SimCaseSum (simRename @_ @_ @_ @r s) (simRename @_ @_ @_ @(M.ext r) l)
             (simRename @_ @_ @_ @(M.ext r) r')
simRename (SimAbsurd s) = SimAbsurd (simRename @_ @_ @_ @r s)
simRename SimNil = SimNil
simRename (SimCons x xs) = SimCons (simRename @_ @_ @_ @r x) (simRename @_ @_ @_ @r xs)
simRename (SimCaseLst xs n c) =
  SimCaseLst (simRename @_ @_ @_ @r xs) (simRename @_ @_ @_ @r n)
             (simRename @_ @_ @_ @(M.ext (M.ext r)) c)
```

## Simulation legs and substitution compatibility

Each leg packages the existential matching target term together with its step
and restored `SimRel` witness:

- `Leg step m' n` witnesses `∃ n'. step m' n' × SimRel n n'` (forward simulation);
- `LegInv step m n'` witnesses `∃ n. step m n × SimRel n n'` (backward simulation).

All 20 congruence and non-substituting β rules (`Xi*`, `BetaZero`, `BetaFst`,
`BetaSnd`, `BetaNil`) discharge directly by structural induction and `simValue`.
The 7 substituting β rules (`BetaLam`, `BetaSuc`, `BetaMu`, `BetaLet`,
`BetaInl`, `BetaInr`, `BetaCons`) rely on substitution compatibility (`~-subst`),
bundled cleanly in `SubstCompat`:

```haskell
-- | Forward simulation leg: `m' —→ n'` with `n ~ n'`.
type Leg :: forall (g :: M.Ctx) (a :: M.Ty).
            (M.Term g a -> M.Term g a -> Type) -> M.Term g a -> M.Term g a -> Type
data Leg step m' n where
  MkLeg :: step m' n' -> SimRel n n' -> Leg step m' n

-- | Backward simulation leg: `m —→ n` with `n ~ n'`.
type LegInv :: forall (g :: M.Ctx) (a :: M.Ty).
               (M.Term g a -> M.Term g a -> Type) -> M.Term g a -> M.Term g a -> Type
data LegInv step m n' where
  MkLegInv :: step m n -> SimRel n n' -> LegInv step m n'

-- | Substitution compatibility bundle for `M.substSingle` and `M.substDouble`.
data SubstCompat where
  MkSubstCompat
    :: (forall (g :: M.Ctx) (a :: M.Ty) (b :: M.Ty)
               (n :: M.Term (M.CExt g a) b) (n' :: M.Term (M.CExt g a) b)
               (v :: M.Term g a) (v' :: M.Term g a).
          SimRel n n' -> SimRel v v' -> SimRel (M.substSingle n v) (M.substSingle n' v'))
    -> (forall (g :: M.Ctx) (a :: M.Ty) (b :: M.Ty)
               (c :: M.Term (M.CExt (M.CExt g a) (M.TList a)) b)
               (c' :: M.Term (M.CExt (M.CExt g a) (M.TList a)) b)
               (x :: M.Term g a) (x' :: M.Term g a)
               (xs :: M.Term g (M.TList a)) (xs' :: M.Term g (M.TList a)).
          SimRel c c' -> SimRel x x' -> SimRel xs xs'
       -> SimRel (M.substDouble c x xs) (M.substDouble c' x' xs'))
    -> SubstCompat
```

<div class="wip-notice">
<strong>[WIP NOTICE — Proving simultaneous substitution compatibility internally (R16)]</strong>
With 20-constructor <code>simRename</code> now proved directly above using an
unmatchable callback (<code>%U -&gt;</code>), the remaining step to discharge
<code>SubstCompat</code> internally is proving <code>simSubst</code> over an
abstract simultaneous substitution callback and its binder extension
<code>M.exts</code>. Meanwhile, the original default-arrow and
implicit-application spelling of abstract renaming remains tracked in
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R16_AbstractRenamingInType.hs"><code>reproducers/R16_AbstractRenamingInType.hs</code></a>.
</div>

## Lock-step forward and backward bisimulation (`sim` and `simInv`)

Look at the `SimLetApp` cases—the centerpiece of PLFA's **Bisimulation** chapter:

1. **Forward (`sim`)**:
   - When `let x = m in n` steps via `MP.XiLet stM`, induction gives `m' —→ m1'`,
     so `(λ x. n') m'` matches lock-step via **`MP.XiApp2 M.VLam stM'`**!
   - When `let x = v in n` steps via `MP.BetaLet vm` to `M.substSingle n v`,
     `(λ x. n') v'` matches lock-step via **`MP.BetaLam (simValue sm vm)`** to
     `M.substSingle n' v'`!
2. **Backward (`simInv`, PLFA Exercise `sim⁻¹`)**:
   - Can `(λ x. n') m'` step via `MP.XiApp1 stLam`? **No!** `valNoStep M.VLam stLam`
     discharges the branch statically via `absurd`!
   - When `(λ x. n') m'` steps via `MP.XiApp2 _ stM'`, `let x = m in n` matches
     lock-step via **`MP.XiLet`**!
   - When `(λ x. n') v'` steps via `MP.BetaLam vm'`, `let x = v in n` matches
     lock-step via **`MP.BetaLet (simValueInv sm vm')`**!

Every single one of the **27 reduction rules** in both directions is checked
exhaustively under `-Werror=incomplete-patterns`:

```haskell
-- | Complete forward lock-step simulation across all 27 rules of `MoreProgress.Step`.
sim :: SubstCompat -> SimRel m m' -> MP.Step m n -> Leg MP.Step m' n
sim sc@(MkSubstCompat sc1 sc2) rel st = case st of
  MP.XiApp1 stL -> case rel of
    SimApp sl sm -> case sim sc sl stL of
      MkLeg stL' sl' -> MkLeg (MP.XiApp1 stL') (SimApp sl' sm)
  MP.XiApp2 vl stM -> case rel of
    SimApp sl sm -> case sim sc sm stM of
      MkLeg stM' sm' -> MkLeg (MP.XiApp2 (simValue sl vl) stM') (SimApp sl sm')
  MP.BetaLam vm -> case rel of
    SimApp (SimLam sn) sm -> MkLeg (MP.BetaLam (simValue sm vm)) (sc1 sn sm)

  MP.XiSuc stM -> case rel of
    SimSuc sm -> case sim sc sm stM of
      MkLeg stM' sm' -> MkLeg (MP.XiSuc stM') (SimSuc sm')
  MP.XiCaseNat stN -> case rel of
    SimCaseNat sn sz ss -> case sim sc sn stN of
      MkLeg stN' sn' -> MkLeg (MP.XiCaseNat stN') (SimCaseNat sn' sz ss)
  MP.BetaZero -> case rel of
    SimCaseNat SimZero sz _ -> MkLeg MP.BetaZero sz
  MP.BetaSuc vv -> case rel of
    SimCaseNat (SimSuc sv) _ ss -> MkLeg (MP.BetaSuc (simValue sv vv)) (sc1 ss sv)
  MP.BetaMu -> case rel of
    SimMu sn -> MkLeg MP.BetaMu (sc1 sn (SimMu sn))

  MP.XiLet stM -> case rel of
    SimLet sm sn -> case sim sc sm stM of
      MkLeg stM' sm' -> MkLeg (MP.XiLet stM') (SimLet sm' sn)
    SimLetApp sm sn -> case sim sc sm stM of
      MkLeg stM' sm' -> MkLeg (MP.XiApp2 M.VLam stM') (SimLetApp sm' sn)
  MP.BetaLet vm -> case rel of
    SimLet sm sn    -> MkLeg (MP.BetaLet (simValue sm vm)) (sc1 sn sm)
    SimLetApp sm sn -> MkLeg (MP.BetaLam (simValue sm vm)) (sc1 sn sm)

  MP.XiPair1 stL -> case rel of
    SimPair sl sr -> case sim sc sl stL of
      MkLeg stL' sl' -> MkLeg (MP.XiPair1 stL') (SimPair sl' sr)
  MP.XiPair2 vl stR -> case rel of
    SimPair sl sr -> case sim sc sr stR of
      MkLeg stR' sr' -> MkLeg (MP.XiPair2 (simValue sl vl) stR') (SimPair sl sr')
  MP.XiFst stP -> case rel of
    SimFst sp -> case sim sc sp stP of
      MkLeg stP' sp' -> MkLeg (MP.XiFst stP') (SimFst sp')
  MP.XiSnd stP -> case rel of
    SimSnd sp -> case sim sc sp stP of
      MkLeg stP' sp' -> MkLeg (MP.XiSnd stP') (SimSnd sp')
  MP.BetaFst vl vr -> case rel of
    SimFst (SimPair sl sr) -> MkLeg (MP.BetaFst (simValue sl vl) (simValue sr vr)) sl
  MP.BetaSnd vl vr -> case rel of
    SimSnd (SimPair sl sr) -> MkLeg (MP.BetaSnd (simValue sl vl) (simValue sr vr)) sr

  MP.XiInl stX -> case rel of
    SimInl sx -> case sim sc sx stX of
      MkLeg stX' sx' -> MkLeg (MP.XiInl stX') (SimInl sx')
  MP.XiInr stY -> case rel of
    SimInr sy -> case sim sc sy stY of
      MkLeg stY' sy' -> MkLeg (MP.XiInr stY') (SimInr sy')
  MP.XiCaseSum stS -> case rel of
    SimCaseSum ss sl sr -> case sim sc ss stS of
      MkLeg stS' ss' -> MkLeg (MP.XiCaseSum stS') (SimCaseSum ss' sl sr)
  MP.BetaInl vx -> case rel of
    SimCaseSum (SimInl sx) sl _ -> MkLeg (MP.BetaInl (simValue sx vx)) (sc1 sl sx)
  MP.BetaInr vy -> case rel of
    SimCaseSum (SimInr sy) _ sr -> MkLeg (MP.BetaInr (simValue sy vy)) (sc1 sr sy)
  MP.XiAbsurd stM -> case rel of
    SimAbsurd sm -> case sim sc sm stM of
      MkLeg stM' sm' -> MkLeg (MP.XiAbsurd stM') (SimAbsurd sm')

  MP.XiCons1 stX -> case rel of
    SimCons sx sxs -> case sim sc sx stX of
      MkLeg stX' sx' -> MkLeg (MP.XiCons1 stX') (SimCons sx' sxs)
  MP.XiCons2 vx stXs -> case rel of
    SimCons sx sxs -> case sim sc sxs stXs of
      MkLeg stXs' sxs' -> MkLeg (MP.XiCons2 (simValue sx vx) stXs') (SimCons sx sxs')
  MP.XiCaseLst stS -> case rel of
    SimCaseLst ss sn scons -> case sim sc ss stS of
      MkLeg stS' ss' -> MkLeg (MP.XiCaseLst stS') (SimCaseLst ss' sn scons)
  MP.BetaNil -> case rel of
    SimCaseLst SimNil sn _ -> MkLeg MP.BetaNil sn
  MP.BetaCons vx vxs -> case rel of
    SimCaseLst (SimCons sx sxs) _ scons ->
      MkLeg (MP.BetaCons (simValue sx vx) (simValue sxs vxs)) (sc2 scons sx sxs)

-- | Complete backward lock-step simulation (`sim⁻¹`) across all 27 rules!
simInv :: SubstCompat -> SimRel m m' -> MP.Step m' n' -> LegInv MP.Step m n'
simInv sc@(MkSubstCompat sc1 sc2) rel st = case st of
  MP.XiApp1 stL' -> case rel of
    SimApp sl sm -> case simInv sc sl stL' of
      MkLegInv stL sl' -> MkLegInv (MP.XiApp1 stL) (SimApp sl' sm)
    SimLetApp _ _ -> absurd (valNoStep M.VLam stL')
  MP.XiApp2 vl' stM' -> case rel of
    SimApp sl sm -> case simInv sc sm stM' of
      MkLegInv stM sm' -> MkLegInv (MP.XiApp2 (simValueInv sl vl') stM) (SimApp sl sm')
    SimLetApp sm sn -> case simInv sc sm stM' of
      MkLegInv stM sm' -> MkLegInv (MP.XiLet stM) (SimLetApp sm' sn)
  MP.BetaLam vm' -> case rel of
    SimApp (SimLam sn) sm -> MkLegInv (MP.BetaLam (simValueInv sm vm')) (sc1 sn sm)
    SimLetApp sm sn       -> MkLegInv (MP.BetaLet (simValueInv sm vm')) (sc1 sn sm)

  MP.XiSuc stM' -> case rel of
    SimSuc sm -> case simInv sc sm stM' of
      MkLegInv stM sm' -> MkLegInv (MP.XiSuc stM) (SimSuc sm')
  MP.XiCaseNat stN' -> case rel of
    SimCaseNat sn sz ss -> case simInv sc sn stN' of
      MkLegInv stN sn' -> MkLegInv (MP.XiCaseNat stN) (SimCaseNat sn' sz ss)
  MP.BetaZero -> case rel of
    SimCaseNat SimZero sz _ -> MkLegInv MP.BetaZero sz
  MP.BetaSuc vv' -> case rel of
    SimCaseNat (SimSuc sv) _ ss -> MkLegInv (MP.BetaSuc (simValueInv sv vv')) (sc1 ss sv)
  MP.BetaMu -> case rel of
    SimMu sn -> MkLegInv MP.BetaMu (sc1 sn (SimMu sn))

  MP.XiLet stM' -> case rel of
    SimLet sm sn -> case simInv sc sm stM' of
      MkLegInv stM sm' -> MkLegInv (MP.XiLet stM) (SimLet sm' sn)
  MP.BetaLet vm' -> case rel of
    SimLet sm sn -> MkLegInv (MP.BetaLet (simValueInv sm vm')) (sc1 sn sm)

  MP.XiPair1 stL' -> case rel of
    SimPair sl sr -> case simInv sc sl stL' of
      MkLegInv stL sl' -> MkLegInv (MP.XiPair1 stL) (SimPair sl' sr)
  MP.XiPair2 vl' stR' -> case rel of
    SimPair sl sr -> case simInv sc sr stR' of
      MkLegInv stR sr' -> MkLegInv (MP.XiPair2 (simValueInv sl vl') stR) (SimPair sl sr')
  MP.XiFst stP' -> case rel of
    SimFst sp -> case simInv sc sp stP' of
      MkLegInv stP sp' -> MkLegInv (MP.XiFst stP) (SimFst sp')
  MP.XiSnd stP' -> case rel of
    SimSnd sp -> case simInv sc sp stP' of
      MkLegInv stP sp' -> MkLegInv (MP.XiSnd stP) (SimSnd sp')
  MP.BetaFst vl' vr' -> case rel of
    SimFst (SimPair sl sr) -> MkLegInv (MP.BetaFst (simValueInv sl vl') (simValueInv sr vr')) sl
  MP.BetaSnd vl' vr' -> case rel of
    SimSnd (SimPair sl sr) -> MkLegInv (MP.BetaSnd (simValueInv sl vl') (simValueInv sr vr')) sr

  MP.XiInl stX' -> case rel of
    SimInl sx -> case simInv sc sx stX' of
      MkLegInv stX sx' -> MkLegInv (MP.XiInl stX) (SimInl sx')
  MP.XiInr stY' -> case rel of
    SimInr sy -> case simInv sc sy stY' of
      MkLegInv stY sy' -> MkLegInv (MP.XiInr stY) (SimInr sy')
  MP.XiCaseSum stS' -> case rel of
    SimCaseSum ss sl sr -> case simInv sc ss stS' of
      MkLegInv stS ss' -> MkLegInv (MP.XiCaseSum stS) (SimCaseSum ss' sl sr)
  MP.BetaInl vx' -> case rel of
    SimCaseSum (SimInl sx) sl _ -> MkLegInv (MP.BetaInl (simValueInv sx vx')) (sc1 sl sx)
  MP.BetaInr vy' -> case rel of
    SimCaseSum (SimInr sy) _ sr -> MkLegInv (MP.BetaInr (simValueInv sy vy')) (sc1 sr sy)
  MP.XiAbsurd stM' -> case rel of
    SimAbsurd sm -> case simInv sc sm stM' of
      MkLegInv stM sm' -> MkLegInv (MP.XiAbsurd stM) (SimAbsurd sm')

  MP.XiCons1 stX' -> case rel of
    SimCons sx sxs -> case simInv sc sx stX' of
      MkLegInv stX sx' -> MkLegInv (MP.XiCons1 stX) (SimCons sx' sxs)
  MP.XiCons2 vx' stXs' -> case rel of
    SimCons sx sxs -> case simInv sc sxs stXs' of
      MkLegInv stXs sxs' -> MkLegInv (MP.XiCons2 (simValueInv sx vx') stXs) (SimCons sx sxs')
  MP.XiCaseLst stS' -> case rel of
    SimCaseLst ss sn scons -> case simInv sc ss stS' of
      MkLegInv stS ss' -> MkLegInv (MP.XiCaseLst stS) (SimCaseLst ss' sn scons)
  MP.BetaNil -> case rel of
    SimCaseLst SimNil sn _ -> MkLegInv MP.BetaNil sn
  MP.BetaCons vx' vxs' -> case rel of
    SimCaseLst (SimCons sx sxs) _ scons ->
      MkLegInv (MP.BetaCons (simValueInv sx vx') (simValueInv sxs vxs')) (sc2 scons sx sxs)
```

### Multi-step bisimulation (`—↠`) and concrete `let`-desugaring witnesses

Composing one-step simulation lifts immediately to multi-step reduction
sequences (`MP.Steps`), and on concrete closed terms GHC evaluates
`M.substSingle` directly without needing `SubstCompat` at all:

```haskell
-- | Multi-step forward simulation (`—↠`).
simSteps :: SubstCompat -> SimRel m m' -> MP.Steps m n -> Leg MP.Steps m' n
simSteps _  rel MP.StepsRefl        = MkLeg MP.StepsRefl rel
simSteps sc rel (MP.StepsCons s ss) = case sim sc rel s of
  MkLeg s' rel1 -> case simSteps sc rel1 ss of
    MkLeg ss' rel2 -> MkLeg (MP.StepsCons s' ss') rel2

-- | Multi-step backward simulation (`—↠`).
simStepsInv :: SubstCompat -> SimRel m m' -> MP.Steps m' n' -> LegInv MP.Steps m n'
simStepsInv _  rel MP.StepsRefl        = MkLegInv MP.StepsRefl rel
simStepsInv sc rel (MP.StepsCons s ss) = case simInv sc rel s of
  MkLegInv s' rel1 -> case simStepsInv sc rel1 ss of
    MkLegInv ss' rel2 -> MkLegInv (MP.StepsCons s' ss') rel2

-- | Concrete closed lock-step bisimulation witnesses (zero assumptions!):
-- `let x = fst (0, 1) in suc x` simulates `(λx. suc x) (fst (0, 1))`
-- through both `XiLet` ↔ `XiApp2 VLam` and `BetaLet` ↔ `BetaLam`!
letDesugarSim
  :: SimRel @M.CEmpty @M.TNat
            (M.Let (M.Fst (M.Pair M.Zero (M.Suc M.Zero))) (M.Suc (M.Var M.Z)))
            (M.App (M.Lam (M.Suc (M.Var M.Z))) (M.Fst (M.Pair M.Zero (M.Suc M.Zero))))
letDesugarSim = SimLetApp (SimFst (SimPair SimZero (SimSuc SimZero))) (SimSuc SimVar)

letDesugarSteps
  :: Leg @M.CEmpty @M.TNat MP.Steps
         (M.App (M.Lam (M.Suc (M.Var M.Z))) (M.Fst (M.Pair M.Zero (M.Suc M.Zero))))
         (M.Suc M.Zero)
letDesugarSteps =
  MkLeg
    (MP.StepsCons (MP.XiApp2 M.VLam (MP.BetaFst M.VZero (M.VSuc M.VZero)))
      (MP.StepsCons (MP.BetaLam M.VZero) MP.StepsRefl))
    (SimSuc SimZero)

letDesugarStepsInv
  :: LegInv @M.CEmpty @M.TNat MP.Steps
            (M.Let (M.Fst (M.Pair M.Zero (M.Suc M.Zero))) (M.Suc (M.Var M.Z)))
            (M.Suc M.Zero)
letDesugarStepsInv =
  MkLegInv
    (MP.StepsCons (MP.XiLet (MP.BetaFst M.VZero (M.VSuc M.VZero)))
      (MP.StepsCons (MP.BetaLet M.VZero) MP.StepsRefl))
    (SimSuc SimZero)
```

### Negative control: forging a wrong bisimulation target

To verify that GHC genuinely checks `M.substSingle` inside `MP.BetaLam` and
`SimRel`, trying to claim `(λ x. suc x) 0` simulates to `Zero` (instead of
`Suc Zero`) must be rejected with `GHC-83865`:

```{.haskell .fail name="NegBisimBadTarget" expect="GHC-83865"}
{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeApplications #-}
module NegBisimBadTarget where

import qualified PLFH.Part2.More as M
import qualified PLFH.Part2.MoreProgress as MP
import PLFH.Part2.Bisimulation (Leg (..), SimRel (..))

-- MUST FAIL: `(λx. suc x) 0` reduces to `Suc Zero`, NOT `Zero`!
badLetDesugar :: Leg @M.CEmpty @M.TNat MP.Step (M.App (M.Lam (M.Suc (M.Var M.Z))) M.Zero) M.Zero
badLetDesugar = MkLeg (MP.BetaLam M.VZero) SimZero
```

## Exercises

#### Exercise `sim⁻¹` (practice) {#sim-inv}

Verify that `simInv` above handles every case of `MP.Step` in the reverse
direction—especially observing why `valNoStep M.VLam` is required in the
`SimLetApp` / `MP.XiApp1` case and how `SimLetApp` maps `MP.XiApp2` back to
`MP.XiLet` and `MP.BetaLam` back to `MP.BetaLet`.

#### Exercise `products` (practice) {#products-bisim}

In [More](/More/), products can be formulated either with projections
(`Fst`/`Snd`) or with a pattern-matching eliminator (`case p of (x, y) => n`).
Explain why the simulation between the two formulations of products is *weak*
(multi-step `—↠`) rather than lock-step (`—→`), and how `Leg MP.Steps` already
accommodates weak simulations directly!

## Changes from PLFA

- Adapted from [Bisimulation](https://plfa.inf.ed.ac.uk/Bisimulation/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/Bisimulation.lagda.md)),
  licensed under CC BY 4.0.
- Proved full 20-constructor `SimRel` (including `SimLetApp`), `simRefl`,
  `simTrans`, bidirectional 9-constructor value preservation (`simValue`,
  `simValueInv`), `valNoStep`, **full 20-constructor `simRename`** (including
  double-binder `CaseLst`, exercised in `PLFH.Part2.BisimulationRenaming`),
  exhaustive 27-rule lock-step forward and backward simulation (`sim`,
  `simInv`), multi-step `simSteps`/`simStepsInv`, concrete closed
  `let`-desugaring witnesses, and negative control `NegBisimBadTarget` under
  `-Werror=incomplete-patterns -dcore-lint -dstg-lint` with zero
  promoted-constructor ticks.
- Parameterized simultaneous substitution compatibility (`SubstCompat`) while
  abstract `M.exts` equations remain WIP (`R16_AbstractRenamingInType.hs`).
