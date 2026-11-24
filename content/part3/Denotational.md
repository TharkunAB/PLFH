---
title: "Denotational: Denotational semantics of untyped lambda calculus"
prev: /Confluence/
next: /Compositional/
src: content/part3/Denotational.md
module: PLFH.Part3.Denotational
plfaChapter: https://plfa.inf.ed.ac.uk/22.08/Denotational/
plfaEdition: "PLFA v22.08"
plfaAuthors: "Philip Wadler, Wen Kokke, and Jeremy G. Siek"
---

```haskell
{-# LANGUAGE AllowAmbiguousTypes, DataKinds, EmptyCase, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, Modifiers, PolyKinds, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures, TypeAbstractions, TypeApplications, TypeOperators #-}
module PLFH.Part3.Denotational
  ( Value (..)
  , Sub (..)
  , subRefl
  , joinSubJoin
  , joinArrDist
  , joinSubInvL
  , joinSubInvR
  , ValMem (..)
  , ValSubset
  , memToSub
  , subsetToSub
  , Fun (..)
  , AllFuns
  , notFunBot
  , SomeArrMem (..)
  , allFunsMem
  , dom
  , cod
  , arrMemToSubDom
  , subArrToCodSub
  , Factor (..)
  , subInvTrans
  , subInv
  , arrSubArrInv
  , ValEnv (..)
  , ValLookup (..)
  , LookupSub (..)
  , EnvSub
  , envSubRefl
  , envSubCons
  , Denotes (..)
  , denotId
  , denotIdTwo
  , denotIdAppId
  , denotDelta
  , denotOmega
  , envSubMono
  , upEnv
  , Denotation
  , DenEq
  , denEqRefl
  , denEqSym
  , denEqTrans
  , Den (..)
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import Data.Void (absurd)
import GHC.Exts (M)
import HaskLib.Size (Size (..))
import PLFH.Part1.Negation (Not)
import PLFH.Part2.Untyped (Fin (..), UTerm (..))
```

In Part 3 of PLFA (`v22.08`, authored by Jeremy G. Siek, Philip Wadler, and
Wen Kokke), we construct an elementary **denotational semantics** (a BCD
filter / Plotkin graph model) for the untyped lambda calculus by representing
functions as finite input-output tables `Value` ordered by approximation `Sub`
(`_⊑_`).

Remarkably, almost all of PLFA's **Denotational** chapter—including the full
**inversion of `Sub` for function values (`subInv` and `arrSubArrInv`,
i.e. `↦⊑↦-inv`)** using ordinary recursive binary-tree functions `dom` and
`cod`—compiles cleanly on GHC `d15cbd41fe` with `-dcore-lint -dstg-lint`,
while also uncovering two crisp compiler bugs (`R13_GadtSyntaxBreaksOpenEq.hs`
and `R03_NestedDepCaseCoreLint.hs`)!

## Finite function tables (`Value`) and approximation (`Sub`, `_⊑_`)

A `Value` represents a finite portion of a function:

- `Bot` (`⊥`) provides no information about a computation.
- `Arr v w` (`v ↦ w`) is a single input-output entry mapping `v` to `w`.
- `Join v w` (`v ⊔ w`) joins two tables.

```haskell
-- | Finite function tables (Scott/Plotkin/BCD filter model values).
-- Note: declared with H98 syntax rather than GADT syntax so ordinary `dom`
-- and `cod` get R13 checked source equations (see WIP notice below).
data Value
  = Bot
  | Arr Value Value
  | Join Value Value
  deriving (Show)
```

The approximation relation `Sub u v` (`u ⊑ v`, the inverse of intersection
subtyping) allows self-application by relaxing lookup to any smaller input
entry. Notice that `SubTrans` retains its intermediate `Value` (`foreach (v :: Value)`)
just as Agda's implicit `∀ {v}` retains it at runtime for `subInv`:

```haskell
-- | Domain approximation order `u ⊑ v`.
data Sub (u :: Value) (v :: Value) where
  SubBot    :: Sub 'Bot v
  SubRefl   :: Sub v v
  SubJoinL  :: Sub v u -> Sub w u -> Sub ('Join v w) u
  SubJoinR1 :: forall (u :: Value) (v :: Value) (w :: Value). Sub u v -> Sub u ('Join v w)
  SubJoinR2 :: forall (u :: Value) (v :: Value) (w :: Value). Sub u w -> Sub u ('Join v w)
  SubTrans  :: foreach (v :: Value) -> Sub u v -> Sub v w -> Sub u w
  SubArr    :: Sub v' v -> Sub w w' -> Sub ('Arr v w) ('Arr v' w')
  SubDist   :: Sub ('Arr v ('Join w w')) ('Join ('Arr v w) ('Arr v w'))

-- | Reflexivity of `Sub` can also be derived by structural induction on `Value`.
subRefl :: foreach (v :: Value) -> Sub v v
subRefl Bot        = SubBot
subRefl (Arr v w)  = SubArr (subRefl v) (subRefl w)
subRefl (Join v w) = SubJoinL (SubJoinR1 (subRefl v)) (SubJoinR2 (subRefl w))

-- | Monotonicity of `Join` (`⊔⊑⊔`).
joinSubJoin :: Sub v v' -> Sub w w' -> Sub ('Join v w) ('Join v' w')
joinSubJoin d1 d2 = SubJoinL (SubJoinR1 d1) (SubJoinR2 d2)

-- | Combining two function entries with distinct inputs (`⊔↦⊔-dist`).
joinArrDist :: foreach (v :: Value) -> foreach (v' :: Value)
            -> foreach (w :: Value) -> foreach (w' :: Value)
            -> Sub ('Arr ('Join v v') ('Join w w')) ('Join ('Arr v w) ('Arr v' w'))
joinArrDist v v' w w' =
  SubTrans (Join (Arr (Join v v') w) (Arr (Join v v') w')) SubDist
    (joinSubJoin
      (SubArr (SubJoinR1 (subRefl v)) (subRefl w))
      (SubArr (SubJoinR2 (subRefl v')) (subRefl w')))

-- | Left and right inversion on joins (`⊔⊑-invL`, `⊔⊑-invR`).
joinSubInvL :: Sub ('Join u v) w -> Sub u w
joinSubInvL SubRefl            = SubJoinR1 SubRefl
joinSubInvL (SubJoinL lt1 _)   = lt1
joinSubInvL (SubJoinR1 lt)     = SubJoinR1 (joinSubInvL lt)
joinSubInvL (SubJoinR2 lt)     = SubJoinR2 (joinSubInvL lt)
joinSubInvL (SubTrans m l1 l2) = SubTrans m (joinSubInvL l1) l2

joinSubInvR :: Sub ('Join u v) w -> Sub v w
joinSubInvR SubRefl            = SubJoinR2 SubRefl
joinSubInvR (SubJoinL _ lt2)   = lt2
joinSubInvR (SubJoinR1 lt)     = SubJoinR1 (joinSubInvR lt)
joinSubInvR (SubJoinR2 lt)     = SubJoinR2 (joinSubInvR lt)
joinSubInvR (SubTrans m l1 l2) = SubTrans m (joinSubInvR l1) l2
```

## Value membership (`∈`), inclusion (`⊆`), `dom`, and `cod`

To prove inversion of `Sub` for function values (`Arr v w ⊑ Arr v' w'`), we
define tree membership `ValMem`, inclusion `ValSubset`, the function predicate
`Fun`/`AllFuns`, and the **ordinary recursive binary-tree functions** `dom` and
`cod`:

```haskell
-- | Membership of a leaf value `u` inside a join-tree `v` (`u ∈ v`).
data ValMem (u :: Value) (v :: Value) where
  MemBot   :: ValMem 'Bot 'Bot
  MemArr   :: ValMem ('Arr v w) ('Arr v w)
  MemJoinL :: ValMem u v -> ValMem u ('Join v w)
  MemJoinR :: ValMem u w -> ValMem u ('Join v w)

-- | Subset inclusion of join-trees (`v ⊆ w`).
type ValSubset (v :: Value) (w :: Value) = forall (u :: Value). ValMem u v -> ValMem u w

memToSub :: ValMem u v -> Sub u v
memToSub MemBot       = SubBot
memToSub MemArr       = SubRefl
memToSub (MemJoinL m) = SubJoinR1 (memToSub m)
memToSub (MemJoinR m) = SubJoinR2 (memToSub m)

subsetToSub :: foreach (u :: Value) -> ValSubset u v -> Sub u v
subsetToSub Bot        _ = SubBot
subsetToSub (Arr _ _)  s = memToSub (s MemArr)
subsetToSub (Join a b) s =
  SubJoinL (subsetToSub a (\m -> s (MemJoinL m)))
           (subsetToSub b (\m -> s (MemJoinR m)))

-- | Evidence that a value is a function entry `v ↦ w`.
data Fun (u :: Value) where
  IsFun :: Fun ('Arr v w)

-- | Every leaf in `v` is a function entry.
type AllFuns (v :: Value) = forall (u :: Value). ValMem u v -> Fun u

notFunBot :: Not (Fun 'Bot)
notFunBot = \case {}

data SomeArrMem (u :: Value) where
  MkSomeArrMem :: foreach (v :: Value) -> foreach (w :: Value)
               -> ValMem ('Arr v w) u -> SomeArrMem u

-- | Every non-empty collection of functions contains at least one function entry.
allFunsMem :: foreach (u :: Value) -> AllFuns u -> SomeArrMem u
allFunsMem Bot        f = absurd (notFunBot (f MemBot))
allFunsMem (Arr v w)  _ = MkSomeArrMem v w MemArr
allFunsMem (Join a _) f =
  case allFunsMem a (\m -> f (MemJoinL m)) of
    MkSomeArrMem v w mem -> MkSomeArrMem v w (MemJoinL mem)

-- | Join of all domains in a table (`dom`), ordinary binary-tree recursion!
dom :: Value -> Value
dom Bot        = Bot
dom (Arr v w)  = v
dom (Join a b) = Join (dom a) (dom b)

-- | Join of all codomains in a table (`cod`), ordinary binary-tree recursion!
cod :: Value -> Value
cod Bot        = Bot
cod (Arr v w)  = w
cod (Join a b) = Join (cod a) (cod b)

-- | If `v ↦ w ∈ u` then `v ⊆ dom u` (`↦∈→⊆dom`).
arrMemToSubDom :: forall (v :: Value) (w :: Value) (x :: Value).
                  foreach (u :: Value) -> ValMem ('Arr v w) u -> ValMem x v -> ValMem x (dom u)
arrMemToSubDom Bot        m            _ = case m of {}
arrMemToSubDom (Arr _ _)  MemArr       x = x
arrMemToSubDom (Join a b) (MemJoinL m) x = MemJoinL @x @(dom a) @(dom b) (arrMemToSubDom @v @w @x a m x)
arrMemToSubDom (Join a b) (MemJoinR m) x = MemJoinR @x @(dom b) @(dom a) (arrMemToSubDom @v @w @x b m x)

-- | If `u ⊆ v ↦ w` then `cod u ⊆ w` (`⊆↦→cod⊆`).
subArrToCodSub :: forall (v :: Value) (w :: Value) (x :: Value).
                  foreach (u :: Value) -> ValSubset u ('Arr v w) -> ValMem x (cod u) -> ValMem x w
subArrToCodSub Bot        s _            = case s @'Bot MemBot of {}
subArrToCodSub (Arr a b)  s x            = case s @('Arr a b) MemArr of { MemArr -> x }
subArrToCodSub (Join a _) s (MemJoinL x) = subArrToCodSub @v @w @x a (\m -> s (MemJoinL m)) x
subArrToCodSub (Join _ b) s (MemJoinR y) = subArrToCodSub @v @w @x b (\m -> s (MemJoinR m)) y
```

<div class="wip-notice">
<strong>[WIP NOTICE — GADT syntax silently disables R13 equations for plain ADTs (R13/R16)]</strong>
Notice that <code>dom</code> and <code>cod</code> perform <em>binary-tree recursion</em>
(two recursive calls in <code>Join (dom a) (dom b)</code>) and compute cleanly
in types on GHC <code>d15cbd41fe</code> when <code>Value</code> is declared in
Haskell 98 syntax (<code>data Value = Bot | Arr Value Value | Join Value Value</code>).
Declaring the <em>exact same</em> non-indexed datatype using GADT syntax
(<code>data Value where Bot :: Value; ...</code>) causes GHC to reject
<code>dom</code> and <code>cod</code> with <code>GHC-68947</code>! See minimal
reproducer
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_GadtSyntaxBreaksOpenEq.hs"><code>reproducers/R13_GadtSyntaxBreaksOpenEq.hs</code></a>.
</div>

## Inversion of `Sub` for functions (`subInv` and `arrSubArrInv`)

This is the technical centerpiece of PLFA's **Denotational** chapter (and the
foundation for decidability of `AboveFun` in [Adequacy](/Adequacy/)). Every
single step compiles and passes `-dcore-lint -dstg-lint`!

```haskell
-- | Witness that `v ↦ w` factors `u` into a sub-collection of functions `u'`.
data Factor (u :: Value) (v :: Value) (w :: Value) where
  MkFactor :: forall (u :: Value) (v :: Value) (w :: Value).
              foreach (u' :: Value)
           -> AllFuns u'
           -> ValSubset u' u
           -> Sub (dom u') v
           -> Sub w (cod u')
           -> Factor u v w

allFunsArr :: AllFuns ('Arr a b)
allFunsArr MemArr = IsFun

allFunsDist :: AllFuns ('Join ('Arr a b) ('Arr a c))
allFunsDist (MemJoinL MemArr) = IsFun
allFunsDist (MemJoinR MemArr) = IsFun

subJoinSelf :: Sub ('Join a a) a
subJoinSelf = SubJoinL SubRefl SubRefl

mkJoinFactor :: forall (u2 :: Value) (d1 :: Value) (c1 :: Value) (d2 :: Value) (c2 :: Value).
                Factor u2 d1 c1 -> Factor u2 d2 c2 -> Factor u2 ('Join d1 d2) ('Join c1 c2)
mkJoinFactor (MkFactor u31 f1 s1 d1 c1) (MkFactor u32 f2 s2 d2 c2) =
  MkFactor @u2 @('Join d1 d2) @('Join c1 c2) (Join u31 u32)
    (\case { MemJoinL m -> f1 m; MemJoinR m -> f2 m })
    (\case { MemJoinL m -> s1 m; MemJoinR m -> s2 m })
    (joinSubJoin d1 d2)
    (joinSubJoin c1 c2)

mkArrFactor :: foreach (a :: Value) -> foreach (b :: Value) -> Factor ('Arr a b) a b
mkArrFactor a b = MkFactor @('Arr a b) @a @b (Arr a b) allFunsArr (\z -> z) SubRefl SubRefl

mkArrSubFactor :: forall (v :: Value) (w :: Value).
                  foreach (u21 :: Value) -> foreach (u22 :: Value)
               -> Sub u21 v -> Sub w u22 -> Factor ('Arr u21 u22) v w
mkArrSubFactor u21 u22 lt1 lt2 =
  MkFactor @('Arr u21 u22) @v @w (Arr u21 u22) allFunsArr (\z -> z) lt1 lt2

mkDistFactor :: foreach (a :: Value) -> foreach (b :: Value) -> foreach (c :: Value)
             -> Factor ('Join ('Arr a b) ('Arr a c)) a ('Join b c)
mkDistFactor a b c =
  MkFactor @('Join ('Arr a b) ('Arr a c)) @a @('Join b c) (Join (Arr a b) (Arr a c))
    allFunsDist (\z -> z) subJoinSelf SubRefl

-- | Transitivity factoring lemma (`sub-inv-trans`).
subInvTrans :: forall (u :: Value) (u2 :: Value).
               foreach (u' :: Value)
            -> AllFuns u'
            -> ValSubset u' u
            -> (forall (v' :: Value) (w' :: Value). ValMem ('Arr v' w') u -> Factor u2 v' w')
            -> Factor u2 (dom u') (cod u')
subInvTrans Bot        fu _    _  = absurd (notFunBot (fu MemBot))
subInvTrans (Arr _ _)  _  subU ih = ih (subU MemArr)
subInvTrans (Join a b) fu subU ih =
  mkJoinFactor @u2 @(dom a) @(cod a) @(dom b) @(cod b)
    (subInvTrans @u @u2 a (\m -> fu (MemJoinL m)) (\m -> subU (MemJoinL m)) ih)
    (subInvTrans @u @u2 b (\m -> fu (MemJoinR m)) (\m -> subU (MemJoinR m)) ih)

mapFactorL :: forall (a :: Value) (b :: Value) (v :: Value) (w :: Value).
              Factor a v w -> Factor ('Join a b) v w
mapFactorL (MkFactor u' f s d c) = MkFactor @('Join a b) @v @w u' f (\z -> MemJoinL (s z)) d c

mapFactorR :: forall (a :: Value) (b :: Value) (v :: Value) (w :: Value).
              Factor b v w -> Factor ('Join a b) v w
mapFactorR (MkFactor u' f s d c) = MkFactor @('Join a b) @v @w u' f (\z -> MemJoinR (s z)) d c

subInvRefl :: foreach (x :: Value) -> ValMem ('Arr v w) x -> Factor x v w
subInvRefl Bot        m            = case m of {}
subInvRefl (Arr a b)  MemArr       = mkArrFactor a b
subInvRefl (Join a _) (MemJoinL m) = mapFactorL (subInvRefl a m)
subInvRefl (Join _ b) (MemJoinR m) = mapFactorR (subInvRefl b m)

subInvJoinR1 :: forall (a :: Value) (b :: Value) (u1 :: Value) (v :: Value) (w :: Value).
                foreach (x :: Value) -> (x :~: 'Join a b) -> Sub u1 a -> ValMem ('Arr v w) u1 -> Factor x v w
subInvJoinR1 Bot        eq _ _ = case eq of {}
subInvJoinR1 (Arr _ _)  eq _ _ = case eq of {}
subInvJoinR1 (Join a _) eq lt1 m = case eq of
  Refl -> mapFactorL (subInv a lt1 m)

subInvJoinR2 :: forall (a :: Value) (b :: Value) (u1 :: Value) (v :: Value) (w :: Value).
                foreach (x :: Value) -> (x :~: 'Join a b) -> Sub u1 b -> ValMem ('Arr v w) u1 -> Factor x v w
subInvJoinR2 Bot        eq _ _ = case eq of {}
subInvJoinR2 (Arr _ _)  eq _ _ = case eq of {}
subInvJoinR2 (Join _ b) eq lt2 m = case eq of
  Refl -> mapFactorR (subInv b lt2 m)

subInvArr :: forall (u21 :: Value) (u22 :: Value) (v :: Value) (w :: Value).
             foreach (x :: Value) -> (x :~: 'Arr u21 u22) -> Sub u21 v -> Sub w u22 -> Factor x v w
subInvArr Bot        eq _   _   = case eq of {}
subInvArr (Join _ _) eq _   _   = case eq of {}
subInvArr (Arr a b)  eq lt1 lt2 = case eq of
  Refl -> mkArrSubFactor @v @w a b lt1 lt2

subInvDist2 :: forall (a :: Value) (b :: Value) (c :: Value).
               foreach (l :: Value) -> foreach (r :: Value)
            -> ('Join l r :~: 'Join ('Arr a b) ('Arr a c))
            -> Factor ('Join l r) a ('Join b c)
subInvDist2 Bot         _ eq = case eq of {}
subInvDist2 (Join _ _)  _ eq = case eq of {}
subInvDist2 (Arr a' b') r eq = case r of
  Bot      -> case eq of {}
  Join _ _ -> case eq of {}
  Arr _ c' -> case eq of
    Refl -> mkDistFactor a' b' c'

subInvDist :: forall (a :: Value) (b :: Value) (c :: Value).
              foreach (x :: Value) -> (x :~: 'Join ('Arr a b) ('Arr a c)) -> Factor x a ('Join b c)
subInvDist Bot        eq = case eq of {}
subInvDist (Arr _ _)  eq = case eq of {}
subInvDist (Join l r) eq = subInvDist2 l r eq

-- | Main inversion theorem for `Sub` (`sub-inv`): if `u1 ⊑ u2` and `v ↦ w ∈ u1`,
-- then `v ↦ w` factors `u2` into a sub-collection of functions.
subInv :: forall (u1 :: Value) (v :: Value) (w :: Value).
          foreach (u2 :: Value) -> Sub u1 u2 -> ValMem ('Arr v w) u1 -> Factor u2 v w
subInv u2 lt m = case lt of
  SubBot            -> case m of {}
  SubRefl           -> subInvRefl u2 m
  SubJoinL lt1 lt2  -> case m of
    MemJoinL x -> subInv u2 lt1 x
    MemJoinR y -> subInv u2 lt2 y
  SubJoinR1 @_ @a @b lt1 -> subInvJoinR1 @a @b u2 Refl lt1 m
  SubJoinR2 @_ @a @b lt2 -> subInvJoinR2 @a @b u2 Refl lt2 m
  SubTrans u lt1 lt2 ->
    case subInv u lt1 m of
      MkFactor u' fu' u'sub d1 c1 ->
        case subInvTrans @u @u2 u' fu' u'sub (\m' -> subInv u2 lt2 m') of
          MkFactor u3 fu3 u3sub d2 c2 ->
            MkFactor @u2 @v @w u3 fu3 u3sub (SubTrans (dom u') d2 d1) (SubTrans (cod u') c1 c2)
  SubArr lt1 lt2    -> case m of
    MemArr -> subInvArr u2 Refl lt1 lt2
  SubDist           -> case m of
    MemArr -> subInvDist u2 Refl

finishArrSubInv :: forall (v :: Value) (w :: Value) (v' :: Value) (w' :: Value).
                   Factor ('Arr v' w') v w -> (Sub v' v, Sub w w')
finishArrSubInv (MkFactor g f s db cc) = case allFunsMem g f of
  MkSomeArrMem u u' m -> case s @('Arr u u') m of
    MemArr ->
      ( SubTrans (dom g) (subsetToSub @(dom g) u (\x -> arrMemToSubDom @u @u' g m x)) db
      , SubTrans (cod g) cc (subsetToSub @w' (cod g) (\x -> subArrToCodSub @v' @w' g s x)) )

-- | Function subtyping inversion (`↦⊑↦-inv`): if `v ↦ w ⊑ v' ↦ w'` then `v' ⊑ v` and `w ⊑ w'`.
arrSubArrInv :: forall (v :: Value) (w :: Value).
                foreach (v' :: Value) -> foreach (w' :: Value)
             -> Sub ('Arr v w) ('Arr v' w') -> (Sub v' v, Sub w w')
arrSubArrInv v' w' lt = finishArrSubInv (subInv (Arr v' w') lt MemArr)
```

<div class="wip-notice">
<strong>[WIP NOTICE — Desugar Core Lint out-of-scope coercion in nested dependent <code>case</code> (R03)]</strong>
Writing <code>subInvDist</code> with nested dependent cases directly inside
the <code>Join l r</code> branch (<code>case l of ... Arr a b -&gt; case r of ...</code>)
typechecks on GHC <code>d15cbd41fe</code> and then fails Core Lint after
Desugar with <em>The coercion variable <code>co_...</code> is out of scope</em>!
Splitting the second match into <code>subInvDist2</code> passes Core Lint
cleanly. Reported to the compiler team as a 16-line minimal reproducer in
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R03_NestedDepCaseCoreLint.hs"><code>reproducers/R03_NestedDepCaseCoreLint.hs</code></a>.
</div>

## Environments, denotational semantics (`γ ⊢ M ↓ v`), and monotonicity

We represent environments as length-indexed value vectors `ValEnv n` with
relational lookup `ValLookup` (avoiding the `R13_LookupEnvOpenEq.hs` blocker),
and prove direct derivations for `id`, `id · id`, `Δ = λx. x x`, and
`Ω = Δ · Δ`, as well as **environment monotonicity (`envSubMono`, `upEnv`)**
and the **denotational equivalence (`DenEq`, `_≃_`)** relation:

```haskell
-- | Value environment of scope depth `n`.
data ValEnv (n :: Size) where
  VNil  :: ValEnv 'Zero
  VCons :: ValEnv n -> Value -> ValEnv ('Succ n)

-- | Relational variable lookup in a value environment.
type ValLookup :: forall (n :: Size). ValEnv n -> Fin n -> Value -> Type
data ValLookup e x v where
  VLZ :: ValLookup ('VCons e v) 'FZ v
  VLS :: ValLookup e x v -> ValLookup ('VCons e w) ('FS x) v

-- | Witness that variable `x` in `e2` has a value at least `v1`.
data LookupSub (e2 :: ValEnv n) (x :: Fin n) (v1 :: Value) where
  MkLookupSub :: ValLookup e2 x v2 -> Sub v1 v2 -> LookupSub e2 x v1

-- | Pointwise environment approximation (`e1 ⊑ e2`).
type EnvSub (e1 :: ValEnv n) (e2 :: ValEnv n) =
  forall (x :: Fin n) (v1 :: Value). ValLookup e1 x v1 -> LookupSub e2 x v1

envSubRefl :: EnvSub e e
envSubRefl lk = MkLookupSub lk SubRefl

envSubCons :: EnvSub e1 e2 -> Sub v1 v2 -> EnvSub ('VCons e1 v1) ('VCons e2 v2)
envSubCons _  lt VLZ      = MkLookupSub VLZ lt
envSubCons es _  (VLS lk) = case es lk of
  MkLookupSub lk2 lt -> MkLookupSub (VLS lk2) lt

-- | Denotational semantics judgment: `e ⊢ m ↓ v`.
type Denotes :: forall (n :: Size). ValEnv n -> UTerm n -> Value -> Type
data Denotes e m v where
  DVar   :: ValLookup e x v -> Denotes e ('UVar x) v
  DElim  :: Denotes e l ('Arr v w) -> Denotes e m v -> Denotes e ('UApp l m) w
  DIntro :: Denotes ('VCons e v) b w -> Denotes e ('ULam b) ('Arr v w)
  DBot   :: Denotes e m 'Bot
  DJoin  :: Denotes e m v -> Denotes e m w -> Denotes e m ('Join v w)
  DSub   :: Denotes e m v -> Sub w v -> Denotes e m w

-- | Identity function: `e ⊢ λx. x ↓ v ↦ v`.
denotId :: Denotes e ('ULam ('UVar 'FZ)) ('Arr v v)
denotId = DIntro (DVar VLZ)

-- | Two-row table for identity: `e ⊢ λx. x ↓ (v ↦ v) ⊔ (w ↦ w)`.
denotIdTwo :: Denotes e ('ULam ('UVar 'FZ)) ('Join ('Arr v v) ('Arr w w))
denotIdTwo = DJoin denotId denotId

-- | Self-application of identity: `[] ⊢ id · id ↓ u ↦ u`.
denotIdAppId :: Denotes 'VNil ('UApp ('ULam ('UVar 'FZ)) ('ULam ('UVar 'FZ))) ('Arr u u)
denotIdAppId = DElim denotId denotId

-- | Self-application combinator Δ = λx. x x: `[] ⊢ Δ ↓ ((v ↦ w) ⊔ v) ↦ w`.
denotDelta :: Denotes 'VNil ('ULam ('UApp ('UVar 'FZ) ('UVar 'FZ))) ('Arr ('Join ('Arr v w) v) w)
denotDelta =
  DIntro (DElim (DSub (DVar VLZ) (SubJoinR1 SubRefl))
                (DSub (DVar VLZ) (SubJoinR2 SubRefl)))

-- | Diverging term Ω = Δ · Δ derives ⊥ (both via `DElim` and trivially via `DBot`).
denotOmega :: Denotes 'VNil
                ('UApp ('ULam ('UApp ('UVar 'FZ) ('UVar 'FZ)))
                       ('ULam ('UApp ('UVar 'FZ) ('UVar 'FZ))))
                'Bot
denotOmega = DElim denotDelta (DJoin (DIntro DBot) DBot)

-- | Environment monotonicity (`⊑-env`): enlarging an environment preserves denotations!
envSubMono :: EnvSub e1 e2 -> Denotes e1 m v -> Denotes e2 m v
envSubMono es (DVar lk)     = case es lk of
  MkLookupSub lk2 lt -> DSub (DVar lk2) lt
envSubMono es (DElim d1 d2) = DElim (envSubMono es d1) (envSubMono es d2)
envSubMono es (DIntro d)    = DIntro (envSubMono (envSubCons es SubRefl) d)
envSubMono _  DBot          = DBot
envSubMono es (DJoin d1 d2) = DJoin (envSubMono es d1) (envSubMono es d2)
envSubMono es (DSub d lt)   = DSub (envSubMono es d) lt

-- | Enlarging the most recently bound variable (`up-env`).
upEnv :: Denotes ('VCons e u1) m v -> Sub u1 u2 -> Denotes ('VCons e u2) m v
upEnv d lt = envSubMono (envSubCons envSubRefl lt) d

-- | A denotation in scope depth `n` relates environments to values (matchable arrows `%M`).
type Denotation (n :: Size) = ValEnv n %M -> Value %M -> Type

-- | Denotational equivalence (`D1 ≃ D2`).
type DenEq (d1 :: Denotation n) (d2 :: Denotation n) =
  forall (e :: ValEnv n) (v :: Value). (d1 e v -> d2 e v, d2 e v -> d1 e v)

denEqRefl :: DenEq d d
denEqRefl = (\x -> x, \x -> x)

denEqSym :: DenEq d1 d2 -> DenEq d2 d1
denEqSym eq = case eq of { (f, g) -> (g, f) }

denEqTrans :: DenEq d1 d2 -> DenEq d2 d3 -> DenEq d1 d3
denEqTrans eq1 eq2 =
  case (eq1, eq2) of
    ((f1, g1), (f2, g2)) -> (\x -> f2 (f1 x), \y -> g1 (g2 y))

-- | `Den m` is the denotation `ℰ m` of term `m`, wrapping `Denotes e m v`.
newtype Den (m :: UTerm n) (e :: ValEnv n) (v :: Value) = MkDen { unDen :: Denotes e m v }
```

## Changes from PLFA `v22.08`

- Adapted from [Denotational (v22.08)](https://plfa.inf.ed.ac.uk/22.08/Denotational/)
  ([source](https://github.com/plfa/plfa.github.io/blob/e2d545f3df0db4d4206c5448735665abde02d81f/src/plfa/part3/Denotational.lagda.md))
  by Philip Wadler, Wen Kokke, and Jeremy G. Siek (CC BY 4.0).
- Checked direct ports of `Value`, `Sub`, `subRefl`, `joinSubJoin`,
  `joinArrDist`, `joinSubInvL`/`R`, `ValMem`, `ValSubset`, `memToSub`,
  `subsetToSub`, `Fun`, `AllFuns`, `allFunsMem`, ordinary recursive `dom` and
  `cod`, `arrMemToSubDom`, `subArrToCodSub`, **`subInvTrans`**, **`subInv`**,
  **`arrSubArrInv`**, `ValEnv`, `Denotes`, `denotId`/`denotDelta`/`denotOmega`,
  `envSubMono`, `upEnv`, `Denotation`, `DenEq`, and `Den`.
- Uncovered and reported two new compiler bugs: `R13_GadtSyntaxBreaksOpenEq.hs`
  (GADT vs H98 syntax on `Value`) and `R03_NestedDepCaseCoreLint.hs` (Desugar
  Core Lint out-of-scope coercion on nested dependent `case`).
