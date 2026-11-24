---
title: "Compositional: The denotational semantics is compositional"
prev: /Denotational/
next: /Soundness/
src: content/part3/Compositional.md
module: PLFH.Part3.Compositional
plfaChapter: https://plfa.inf.ed.ac.uk/Compositional/
plfaAuthors: "Philip Wadler, Wen Kokke, and Jeremy G. Siek"
---

```haskell
{-# LANGUAGE AllowAmbiguousTypes, DataKinds, EmptyCase, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, Modifiers, PolyKinds, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures, TypeOperators #-}
module PLFH.Part3.Compositional
  ( LamDen (..)
  , subLamDen
  , denLamToF
  , lamInversion
  , fToDenLam
  , lamEquiv
  , lamDenCong
  , lamCong
  , AppDen (..)
  , subAppDen
  , joinAppDen
  , denAppToAppDen
  , appDenToDenApp
  , appEquiv
  , appDenCong
  , appCong
  , UCtx (..)
  , plug
  ) where

import Data.Kind (Type)
import HaskLib.Nat (Nat (..))
import PLFH.Part2.Untyped (UTerm (..))
import PLFH.Part3.Denotational
  ( Den (..)
  , DenEq
  , Denotation
  , Denotes (..)
  , Sub (..)
  , ValEnv (..)
  , ValW (..)
  , Value (..)
  , denEqSym
  , denEqTrans
  , unArrW
  , unJoinW
  , upEnv
  )
```

In PLFA's **Compositional** chapter, we prove that the relational denotational
semantics `ℰ` obeys **both** compositional equations—for **lambda abstraction**
(`ℰ (ƛ N) ≃ ℱ (ℰ N)`) and for **application** (`ℰ (L · M) ≃ ℰ L ● ℰ M`)—and
derive both **lambda inversion** (`lamInversion`) and congruence for abstraction
and application (`lamCong`, `appCong`)!

## Semantic equation and inversion for lambda abstraction (`ℱ`)

We define the semantic curry operator `LamDen` (`ℱ`) inductively over the
target `Value`, prove downward closure (`subLamDen` / `sub-ℱ`), prove **both
directions** of `ℰ (ƛ N) ≃ ℱ (ℰ N)` (`denLamToF`, `fToDenLam`, `lamEquiv`),
derive the key **lambda inversion lemma** (`lamInversion`), and prove congruence
(`lamCong`):

```haskell
-- | Semantic curry operator `ℱ`: lifts a body denotation to a lambda denotation.
type LamDen :: forall (n :: Nat). Denotation ('Succ n) -> ValEnv n -> Value -> Type
data LamDen d e v where
  LDIntro :: d ('VCons e v) w -> LamDen d e ('Arr v w)
  LDBot   :: LamDen d e 'Bot
  LDJoin  :: ValW u -> ValW v -> LamDen d e u -> LamDen d e v -> LamDen d e ('Join u v)

-- | Downward closure of `LamDen` under `Sub` (`sub-ℱ`).
subLamDen :: ValW u -> ValW v -> LamDen (Den b) e v -> Sub u v -> LamDen (Den b) e u
subLamDen _  _  _  SubBot            = LDBot
subLamDen _  _  d  SubRefl           = d
subLamDen wu wv d  (SubJoinL l1 l2)  = case unJoinW wu of
  (wu1, wu2) -> LDJoin wu1 wu2 (subLamDen wu1 wv d l1) (subLamDen wu2 wv d l2)
subLamDen wu _  (LDJoin wv1 _ d1 _) (SubJoinR1 lt) = subLamDen wu wv1 d1 lt
subLamDen wu _  (LDJoin _ wv2 _ d2) (SubJoinR2 lt) = subLamDen wu wv2 d2 lt
subLamDen wu wv d  (SubTrans mid l1 l2) =
  let wMid = MkValW mid
  in subLamDen wu wMid (subLamDen wMid wv d l2) l1
subLamDen wu wv (LDIntro (MkDen d)) (SubArr lt1 lt2) = case (unArrW wu, unArrW wv) of
  ((wu1, _), (_, wv2)) -> LDIntro (MkDen (DSub wv2 (upEnv wu1 d lt1) lt2))
subLamDen wu _  (LDJoin _ _ (LDIntro (MkDen d1)) (LDIntro (MkDen d2))) SubDist =
  case unArrW wu of
    (_, wJoin) -> case unJoinW wJoin of
      (ww1, ww2) -> LDIntro (MkDen (DJoin ww1 ww2 d1 d2))

-- | Forward direction (`ℰƛ→ℱℰ`).
denLamToF :: ValW v -> Den ('ULam b) e v -> LamDen (Den b) e v
denLamToF _  (MkDen (DIntro d))          = LDIntro (MkDen d)
denLamToF _  (MkDen DBot)                = LDBot
denLamToF _  (MkDen (DJoin w1 w2 d1 d2)) =
  LDJoin w1 w2 (denLamToF w1 (MkDen d1)) (denLamToF w2 (MkDen d2))
denLamToF wv (MkDen (DSub wSuper d lt))  = subLamDen wv wSuper (denLamToF wSuper (MkDen d)) lt

-- | Lambda inversion lemma (`lambda-inversion`): if `e ⊢ λb ↓ v1 ↦ v2` then `(e, v1) ⊢ b ↓ v2`.
lamInversion :: ValW ('Arr v1 v2) -> Denotes e ('ULam b) ('Arr v1 v2) -> Denotes ('VCons e v1) b v2
lamInversion wArr d = case denLamToF wArr (MkDen d) of
  LDIntro (MkDen db) -> db

-- | Backward direction (`ℱℰ→ℰƛ`).
fToDenLam :: LamDen (Den b) e v -> Den ('ULam b) e v
fToDenLam (LDIntro (MkDen d))   = MkDen (DIntro d)
fToDenLam LDBot                 = MkDen DBot
fToDenLam (LDJoin w1 w2 d1 d2)  =
  MkDen (DJoin w1 w2 (unDen (fToDenLam d1)) (unDen (fToDenLam d2)))

-- | Compositional semantic equation for lambda: `ℰ (λb) ≃ ℱ (ℰ b)`.
lamEquiv :: DenEq (Den ('ULam b)) (LamDen (Den b))
lamEquiv wv = (denLamToF wv, fToDenLam)

-- | `LamDen` respects denotational equivalence (`ℱ-cong`).
lamDenCong :: DenEq d1 d2 -> DenEq (LamDen d1) (LamDen d2)
lamDenCong eq wv = (go eq wv, go (denEqSym eq) wv)
  where
    go :: DenEq a b -> ValW v -> LamDen a e v -> LamDen b e v
    go eq' wv' (LDIntro d)          = case unArrW wv' of
      (_, w2) -> LDIntro (fst (eq' w2) d)
    go _   _   LDBot                = LDBot
    go eq' _   (LDJoin w1 w2 d1 d2) = LDJoin w1 w2 (go eq' w1 d1) (go eq' w2 d2)

-- | Congruence for lambda abstraction (`lam-cong`): `ℰ b ≃ ℰ b'` implies `ℰ (λb) ≃ ℰ (λb')`.
lamCong :: DenEq (Den b) (Den b') -> DenEq (Den ('ULam b)) (Den ('ULam b'))
lamCong eq = denEqTrans lamEquiv (denEqTrans (lamDenCong eq) (denEqSym lamEquiv))
```

## Full semantic equation for application (`●`), `UCtx`, and `plug`

Using retained `ValW` witnesses in `AppDen` and `Denotes`, **both directions**
of application compositionality (`denAppToAppDen` / `ℰ·→●ℰ`, `appDenToDenApp` /
`●ℰ→ℰ·`, `appEquiv`, and `appCong`) compile directly with `-dcore-lint -dstg-lint`!

```haskell
-- | Semantic application operator (`D1 ● D2`).
type AppDen :: forall (n :: Nat). Denotation n -> Denotation n -> ValEnv n -> Value -> Type
data AppDen d1 d2 e w where
  ADBot :: Sub w 'Bot -> AppDen d1 d2 e w
  ADApp :: ValW v -> d1 e ('Arr v w) -> d2 e v -> AppDen d1 d2 e w

-- | Downward closure of `AppDen` under `Sub`.
subAppDen :: ValW v -> AppDen (Den l) (Den m) e v -> Sub w v -> AppDen (Den l) (Den m) e w
subAppDen (MkValW v) (ADBot lt1) lt = ADBot (SubTrans v lt lt1)
subAppDen (MkValW v) (ADApp wArg@(MkValW a) (MkDen d1) d2) lt =
  ADApp wArg (MkDen (DSub (MkValW (Arr a v)) d1 (SubArr SubRefl lt))) d2

-- | Join closure of `AppDen` (using `SubDist` when combining two function applications!).
joinAppDen :: ValW w1 -> ValW w2
           -> AppDen (Den l) (Den m) e w1
           -> AppDen (Den l) (Den m) e w2
           -> AppDen (Den l) (Den m) e ('Join w1 w2)
joinAppDen _ _ (ADBot lt1) (ADBot lt2) = ADBot (SubJoinL lt1 lt2)
joinAppDen _ (MkValW w2) (ADBot lt1) (ADApp wArg@(MkValW a) (MkDen d1) d2) =
  ADApp wArg
    (MkDen (DSub (MkValW (Arr a w2)) d1
      (SubArr SubRefl (SubJoinL (SubTrans Bot lt1 SubBot) SubRefl))))
    d2
joinAppDen (MkValW w1) _ (ADApp wArg@(MkValW a) (MkDen d1) d2) (ADBot lt2) =
  ADApp wArg
    (MkDen (DSub (MkValW (Arr a w1)) d1
      (SubArr SubRefl (SubJoinL SubRefl (SubTrans Bot lt2 SubBot)))))
    d2
joinAppDen (MkValW w1) (MkValW w2)
           (ADApp (MkValW v1) (MkDen d1) (MkDen d2))
           (ADApp (MkValW v2) (MkDen d1') (MkDen d2')) =
  let d1L = DSub (MkValW (Arr v1 w1)) d1  (SubArr (SubJoinR1 SubRefl) SubRefl)
      d1R = DSub (MkValW (Arr v2 w2)) d1' (SubArr (SubJoinR2 SubRefl) SubRefl)
      d1J = DJoin (MkValW (Arr (Join v1 v2) w1)) (MkValW (Arr (Join v1 v2) w2)) d1L d1R
      d1F = DSub (MkValW (Join (Arr (Join v1 v2) w1) (Arr (Join v1 v2) w2))) d1J SubDist
      d2F = DJoin (MkValW v1) (MkValW v2) d2 d2'
  in ADApp (MkValW (Join v1 v2)) (MkDen d1F) (MkDen d2F)

-- | Forward direction for application (`ℰ·→●ℰ`)!
denAppToAppDen :: Den ('UApp l m) e w -> AppDen (Den l) (Den m) e w
denAppToAppDen (MkDen (DElim wv d1 d2))    = ADApp wv (MkDen d1) (MkDen d2)
denAppToAppDen (MkDen DBot)                = ADBot SubRefl
denAppToAppDen (MkDen (DJoin w1 w2 d1 d2)) =
  joinAppDen w1 w2 (denAppToAppDen (MkDen d1)) (denAppToAppDen (MkDen d2))
denAppToAppDen (MkDen (DSub wv d lt))      = subAppDen wv (denAppToAppDen (MkDen d)) lt

-- | Backward direction for application (`●ℰ→ℰ·`).
appDenToDenApp :: AppDen (Den l) (Den m) e w -> Den ('UApp l m) e w
appDenToDenApp (ADBot lt)                        = MkDen (DSub (MkValW Bot) DBot lt)
appDenToDenApp (ADApp wv (MkDen d1) (MkDen d2))  = MkDen (DElim wv d1 d2)

-- | Compositional semantic equation for application: `ℰ (l · m) ≃ ℰ l ● ℰ m`!
appEquiv :: DenEq (Den ('UApp l m)) (AppDen (Den l) (Den m))
appEquiv _ = (denAppToAppDen, appDenToDenApp)

-- | `AppDen` respects denotational equivalence (`●-cong`).
appDenCong :: DenEq d1 d1' -> DenEq d2 d2' -> DenEq (AppDen d1 d2) (AppDen d1' d2')
appDenCong e1 e2 wv = (go e1 e2 wv, go (denEqSym e1) (denEqSym e2) wv)
  where
    go :: DenEq a a' -> DenEq b b' -> ValW w -> AppDen a b e w -> AppDen a' b' e w
    go _   _   _          (ADBot lt)                      = ADBot lt
    go e1' e2' (MkValW w) (ADApp wv'@(MkValW v) d1 d2)    =
      ADApp wv' (fst (e1' (MkValW (Arr v w))) d1) (fst (e2' wv') d2)

-- | Congruence for application (`app-cong`): `ℰ l ≃ ℰ l'` & `ℰ m ≃ ℰ m'` implies `ℰ (l·m) ≃ ℰ (l'·m')`!
appCong :: DenEq (Den l) (Den l') -> DenEq (Den m) (Den m')
        -> DenEq (Den ('UApp l m)) (Den ('UApp l' m'))
appCong el em = denEqTrans appEquiv (denEqTrans (appDenCong el em) (denEqSym appEquiv))

-- | One-hole term contexts taking a hole of depth `m` to a term of depth `n`.
data UCtx (m :: Nat) (n :: Nat) where
  CHole :: UCtx n n
  CLam  :: UCtx ('Succ m) ('Succ n) -> UCtx ('Succ m) n
  CAppL :: UCtx m n -> UTerm n -> UCtx m n
  CAppR :: UTerm n -> UCtx m n -> UCtx m n

-- | Plugging a term into a one-hole context.
plug :: UCtx m n -> UTerm m -> UTerm n
plug CHole       t = t
plug (CLam c)    t = ULam (plug c t)
plug (CAppL c r) t = UApp (plug c t) r
plug (CAppR l c) t = UApp l (plug c t)
```

<div class="wip-notice">
<strong>[WIP NOTICE — General <code>compositionality</code> over <code>plug c m</code> (R03/R13)]</strong>
Both structural congruence theorems (<code>lamCong</code> and
<code>appCong</code>) are now <strong>100% checked</strong>! Only the final
induction over arbitrary one-hole contexts <code>UCtx m n</code>:
<pre class="wip"><code>compositionality :: foreach (c :: UCtx m n)
                 -&gt; DenEq (Den t) (Den t')
                 -&gt; DenEq (Den (plug c t)) (Den (plug c t'))</code></pre>
remains open on published GHC <code>1a02a866e7</code>, requiring both
<code>foreach</code> over the indexed GADT <code>UCtx m n</code>
(<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R03_ForEachGadtEquations.hs"><code>R03_ForEachGadtEquations.hs</code></a>)
and R13 checked source equations for GADT-indexed <code>plug</code>
(<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_LookupEnvOpenEq.hs"><code>R13_LookupEnvOpenEq.hs</code></a>).
</div>

## Changes from PLFA

- Adapted from [Compositional](https://plfa.inf.ed.ac.uk/Compositional/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part3/Compositional.lagda.md))
  by Philip Wadler, Wen Kokke, and Jeremy G. Siek (CC BY 4.0).
- Checked direct ports of **both** lambda compositionality (`LamDen`,
  **`subLamDen`**, **`denLamToF`**, **`lamInversion`**, **`fToDenLam`**,
  **`lamEquiv`**, `lamDenCong`, **`lamCong`**) **and** full application
  compositionality (`AppDen`, **`subAppDen`**, **`joinAppDen`**,
  **`denAppToAppDen`**, **`appDenToDenApp`**, **`appEquiv`**, `appDenCong`,
  **`appCong`**), plus `UCtx` and `plug`.
- Marked `compositionality` over `foreach (c :: UCtx m n)` / `plug c t` with
  `[WIP NOTICE]` (R03/R13).
