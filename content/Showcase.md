---
title: "Dependent Haskell Roadmap Showcase"
prev: /Overview/
next: /Playground/
src: content/Showcase.md
playground: true
---

Every card below is a **self-contained, editable Dependent Haskell module**
demonstrating a completed capability from the
[`TharkunAB/ghc` (`dependent-haskell`)](https://github.com/TharkunAB/ghc/tree/dependent-haskell)
roadmap ([`ROADMAP.md`](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/ROADMAP.md),
[`PROPOSAL-378.md`](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/PROPOSAL-378.md),
and [`Showcase.hs`](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/Showcase.hs)).

Pick a tab below, click **Check in GHCi (Wasm)** on any card (or check an
entire tab at once) to compile and load it in WebAssembly GHC `10.1`, or click
**Edit** for the **Agda-mode editor** (code dims while edited and lights up
with semantic colors, green typed-hole goal boxes, and error spans on
**`Ctrl/Cmd+Enter`**).

<div id="plfh-showcase-bar" class="plfh-chapter-bar"></div>

::: {.plfh-showcase-group data-showcase-tab="quantifiers" data-showcase-label="Quantifiers & Types"}

## Unified Quantifiers (`foreach`), Peano Arithmetic & Decimal Literals

<div class="showcase-credits">
  <strong>Spec &amp; Roadmap:</strong>
  GHC Proposal <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#quantifiers">#378 §4.4 Quantifiers</a> &amp;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#dependent-pattern-match">§4.5 Dependent Pattern-Match</a>
  (Richard A. Eisenberg) &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0364-unify-natural.html">#364 Unify <code>Nat</code> &amp; <code>Natural</code></a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#dependent-products">R03 Dependent products</a>,
  <a href="https://ghc.serokell.io/dh#promote-literals">R07 Promote literals</a>,
  <a href="https://ghc.serokell.io/dh#promote-natural">R09 Promote Natural</a> &middot;
  <a href="https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R03-dependent-products.md">Fork R03 notes</a>
</div>

Ordinary Peano functions (`plus`) and decimal literals (`2 + 3`) compute
directly in types under `-XDependentTypes` with zero `type family` or singleton
boilerplate.

```haskell
{-# LANGUAGE DependentTypes #-}
module ShowcaseNat where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..), natToInt, plus, type (+))
import PLFH.Part1.Induction (cong)

twoPlusThree :: (2 + 3 :: Nat) :~: 5
twoPlusThree = Refl

plusIdentityR :: foreach (m :: Nat) -> plus m Zero :~: m
plusIdentityR Zero     = Refl
plusIdentityR (Succ m) = cong Succ (plusIdentityR m)

plusAssoc :: foreach (m n p :: Nat) -> plus (plus m n) p :~: plus m (plus n p)
plusAssoc Zero     _ _ = Refl
plusAssoc (Succ m) n p = cong Succ (plusAssoc m n p)

five :: Int
five = natToInt (plus 2 3)
```

## Retained Dependent Pairs (`Sigma` / `some`) & `OverloadedRecordDot`

<div class="showcase-credits">
  <strong>Spec &amp; Roadmap:</strong>
  GHC Proposal <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#erasure">#378 §4.2 Predictable Erasure</a>
  (Richard A. Eisenberg) &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0282-record-dot-syntax.html">#282 Record Dot Syntax</a>
  (Neil Mitchell, Shayne Fletcher, Adam Gundry) &middot;
  Serokell <a href="https://ghc.serokell.io/dh#dependent-retained-quantifiers">R02 Retained quantifiers</a>,
  <a href="https://ghc.serokell.io/dh#dependent-sums">R04 Dependent sums</a> &middot;
  <a href="https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R04-dependent-sums.md">Fork R04 notes</a>
</div>

`some (x :: a) | p x` (`GHC.Sigma.Sigma`) pairs a runtime witness with a
dependent proof or length-indexed payload, and projects fields via `.first` and
`.second` under `-XOverloadedRecordDot`.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns, OverloadedRecordDot, UndecidableInstances #-}
module ShowcaseSigma where

import Data.Type.Equality ((:~:) (Refl))
import GHC.Sigma (Sigma (Pair), first)
import GHC.Sigma.Projection (second)
import HaskLib.Nat (Nat (..), natToInt, plus)
import HaskLib.Vec (SomeVec, Vec (..), toListVec)

type EvenSigma (n :: Nat) = some (k :: Nat) | plus k k :~: n

halfOfSix :: EvenSigma 6
halfOfSix = Pair 3 Refl

extractHalf :: Int
extractHalf = case halfOfSix of
  Pair k Refl -> natToInt k

packedChars :: SomeVec Char
packedChars = Pair 3 (VCons 'd' (VCons 'e' (VCons 'p' VNil)))

projectVec :: forall a. foreach (p :: SomeVec a) -> Vec a (first p)
projectVec p = p.second

sigmaDemo :: (Int, Int, String)
sigmaDemo = (extractHalf, natToInt packedChars.first, toListVec (projectVec packedChars))
```

## Dependent Records & Parameterized Record Updates

<div class="showcase-credits">
  <strong>Spec &amp; Roadmap:</strong>
  GHC Proposal <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0282-record-dot-syntax.html">#282 Record Dot Syntax</a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#dependent-sums">R04 Dependent sums</a> &middot;
  <a href="https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R04-dependent-sums.md">Fork R04 notes</a> &middot;
  <a href="https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/Showcase.hs"><code>Showcase.hs</code></a>
</div>

Dependent records allow later fields to refer to earlier fields, project
dependent payloads via `.field`, and perform length-preserving updates on
parameterized single-constructor records.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns, OverloadedRecordDot #-}
module ShowcaseDependentRecords where

import HaskLib.Nat (Nat (..), natToInt)
import HaskLib.Vec (Vec (..), mapVec, toListVec)

data SizedRow a = SizedRow
  { rowLen   :: Nat
  , rowItems :: Vec a rowLen
  }

initialRow :: SizedRow Int
initialRow = SizedRow 3 (VCons 10 (VCons 20 (VCons 30 VNil)))

-- Type-changing dependent record update preserving the stored length:
mapRow :: (a -> b) -> SizedRow a -> SizedRow b
mapRow f r = r { rowItems = mapVec f (rowItems r) }

doubledRow :: SizedRow Int
doubledRow = mapRow (* 2) initialRow

shownRow :: SizedRow String
shownRow = mapRow show doubledRow

rowSummary :: (Int, [String])
rowSummary = (natToInt shownRow.rowLen, toListVec shownRow.rowItems)
```

## Runtime `Type` Pattern Matching (`foreach (a :: Type)`)

<div class="showcase-credits">
  <strong>Spec &amp; Roadmap:</strong>
  GHC Proposal <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#phase-distinction">#378 §4.9 Phase Distinction</a>
  (Richard A. Eisenberg) &middot;
  Serokell <a href="https://ghc.serokell.io/dh#dependent-products">R03 Dependent products</a> &middot;
  <a href="https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R03-dependent-products.md">Fork R03 notes</a>
</div>

With `foreach (a :: Type)`, types themselves are retained at runtime and
inspected by ordinary `case` expressions, refining the result type in each
branch.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module ShowcaseTypeCase where

import Data.Kind (Type)

defaultVal :: foreach (a :: Type) -> Maybe a
defaultVal a = case a of
  Int    -> Just 42
  Bool   -> Just True
  [Char] -> Just "dependent haskell"
  _      -> Nothing

demoDefaults :: (Maybe Int, Maybe Bool, Maybe String, Maybe Double)
demoDefaults = (defaultVal Int, defaultVal Bool, defaultVal String, defaultVal Double)
```

:::

::: {.plfh-showcase-group data-showcase-tab="promotion" data-showcase-label="Promotion & Open Evaluation"}

## Stock `Prelude` Lists & Checked Open Evaluation

<div class="showcase-credits">
  <strong>Spec &amp; Roadmap:</strong>
  GHC Proposal <a href="https://github.com/ghc-proposals/ghc-proposals/pull/509">#509 Type-Level Functions</a> (draft) &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0475-tuple-syntax.html">#475 Non-punning List &amp; Tuple Syntax</a>
  (Vladislav Zavialov) &middot;
  Serokell <a href="https://ghc.serokell.io/dh#function-promotion">R13 Function promotion</a>,
  <a href="https://ghc.serokell.io/dh#open-term-evaluator">R16 Open term evaluator</a>,
  <a href="https://ghc.serokell.io/dh#no-list-or-tuple-puns">R38 No list/tuple puns</a> &middot;
  <a href="https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R16-open-term-evaluator.md">Fork R16 notes</a>
</div>

Ordinary functions over stock `Prelude` lists (`List a`, `(++)`, `map`,
`HaskLib.size`) evaluate symbolically over unknown `foreach` variables so
structural and length laws prove directly without custom list clones.

```haskell
{-# LANGUAGE DependentTypes, NoListTuplePuns #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}
module ShowcaseLists where

import Data.Type.Equality ((:~:) (Refl))
import GHC.Types (List)
import HaskLib (size)
import HaskLib.Nat (Nat (..), natToInt, plus)
import PLFH.Part1.Induction (cong)

appendAssoc :: forall a. foreach (xs ys zs :: List a)
            -> ((xs ++ ys) ++ zs) :~: (xs ++ (ys ++ zs))
appendAssoc []       _  _  = Refl
appendAssoc (x : xs) ys zs = cong (x :) (appendAssoc xs ys zs)

lengthAppend :: forall a. foreach (xs ys :: List a)
             -> size (xs ++ ys) :~: plus (size xs) (size ys)
lengthAppend []       _  = Refl
lengthAppend (_ : xs) ys = cong Succ (lengthAppend xs ys)

lengthMap :: forall a b. foreach (f :: a -> b) -> foreach (xs :: List a)
          -> size (map f xs) :~: size xs
lengthMap _ []       = Refl
lengthMap f (_ : xs) = cong Succ (lengthMap f xs)

demoLen :: Int
demoLen = natToInt (size ("dependent" ++ " haskell"))
```

## Matchability-Polymorphic `cong` & T2T Operator Sections

<div class="showcase-credits">
  <strong>Spec &amp; Roadmap:</strong>
  GHC Proposal <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0242-unsaturated-type-families.html">#242 Unsaturated Type Families</a>
  (Csongor Kiss, Tony Field, Susan Eisenbach, Simon Peyton Jones; <a href="https://doi.org/10.1145/3341706">ICFP 2019</a>) &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0281-visible-forall.html">#281 Visible <code>forall</code></a>
  (Vladislav Zavialov) &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0370-modifiers.html">#370 Modifiers</a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#unsaturated-type-families">R23</a>,
  <a href="https://ghc.serokell.io/dh#modifiers-syntax">R25</a>,
  <a href="https://ghc.serokell.io/dh#visible-forall">R39</a> &middot;
  <a href="https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R23-unsaturated-type-families.md">Fork R23 notes</a>
</div>

Matchability polymorphism (`%M` / `%U`) combined with `RequiredTypeArguments`
and Wave 10 T2T operator sections lets a single `cong` accept matchable
constructors (`Succ`), unmatchable functions (`plus m`), and left/right
sections (`(x :)`, `(: ys)`) with zero `@` sigils.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module ShowcaseSections where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..), plus)
import PLFH.Part1.Induction (cong)

congSuccDemo :: forall (m n :: Nat). m :~: n -> Succ m :~: Succ n
congSuccDemo eq = cong Succ eq

congPlusLeft :: forall (n p :: Nat). foreach (m :: Nat)
             -> n :~: p -> plus m n :~: plus m p
congPlusLeft m eq = cong (plus m) eq

congConsLeft :: forall a (x :: a) (ys1 ys2 :: [a]).
                ys1 :~: ys2 -> (x : ys1) :~: (x : ys2)
congConsLeft eq = cong (x :) eq

congConsRight :: forall a (x1 x2 :: a) (ys :: [a]).
                 x1 :~: x2 -> (x1 : ys) :~: (x2 : ys)
congConsRight eq = cong (: ys) eq
```

## Term-to-`Type` Large Eliminations (Zero `type family`)

<div class="showcase-credits">
  <strong>Spec &amp; Roadmap:</strong>
  GHC Proposal <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#syntactic-unification">#378 §4.3.3 Syntactic Unification</a> &amp;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#dependent-application-and-the-static-subset">§4.7 Dependent Application</a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#function-promotion">R13 Function promotion</a>,
  <a href="https://ghc.serokell.io/dh#dependency-analysis">R21 Dependency analysis</a> &middot;
  <a href="https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R21-dependency-analysis.md">Fork R21 notes</a>
</div>

Ordinary Haskell functions can compute `Type` directly from a runtime term
argument without writing a separate `type family`—the same mechanism used in
PLFH's [Adequacy](/Adequacy/) logical relation (`logVLam`).

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module ShowcaseLargeElim where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))

data Tag = TInt | TBool | TStr

-- Ordinary term-level function computing a Type from a runtime Tag:
tagType :: Tag -> Type
tagType TInt  = type Int
tagType TBool = type Bool
tagType TStr  = type String

defaultForTag :: foreach (t :: Tag) -> tagType t
defaultForTag TInt  = 42
defaultForTag TBool = True
defaultForTag TStr  = "dependent haskell"

tagIntEq :: tagType TInt :~: Int
tagIntEq = Refl

demoTagVals :: (Int, Bool, String)
demoTagVals = (defaultForTag TInt, defaultForTag TBool, defaultForTag TStr)
```

:::

::: {.plfh-showcase-group data-showcase-tab="libraries" data-showcase-label="Indexed Libraries (HaskLib)"}

## Length-Indexed Vectors, Safe `Fin` Indexing & Runtime List Boundaries

<div class="showcase-credits">
  <strong>Spec &amp; Roadmap:</strong>
  Serokell <a href="https://ghc.serokell.io/dh#dependent-products">R03 Dependent products</a>,
  <a href="https://ghc.serokell.io/dh#dependent-sums">R04 Dependent sums</a>,
  <a href="https://ghc.serokell.io/dh#homogeneous-equality">R11 Homogeneous equality</a> &middot;
  <a href="/HaskLib/">HaskLib Reference</a> (transitioning to
  <a href="https://github.com/TharkunAB/dependent-base"><code>TharkunAB/dependent-base</code></a>) &middot;
  <a href="https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R11-homogeneous-equality.md">Fork R11 notes</a>
</div>

`HaskLib.Vec` and `HaskLib.Fin` pair static length guarantees (`appendVec`,
`zipVec`, total `lookupVec`) with explicit ordinary-list boundary adapters
(`packListVec`, `fromListExact`) inspired by `linear-base` and Agda's standard
library.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module ShowcaseVecFin where

import GHC.Sigma (Sigma (Pair))
import HaskLib.Fin (Fin (..), lookupVec)
import HaskLib.Nat (Nat (..), natToInt)
import HaskLib.Vec
  ( Vec (..)
  , appendVec
  , headVec
  , mapVec
  , packListVec
  , toListVec
  , zipVec
  )

left :: Vec String 2
left = VCons "dependent" (VCons "haskell" VNil)

right :: Vec String 1
right = VCons "works" VNil

combined :: Vec String 3
combined = appendVec left right

secondWord :: String
secondWord = lookupVec (FS FZ) combined

tagged :: Vec (String, Int) 3
tagged = zipVec combined (mapVec length combined)

packAndRead :: [a] -> (Int, [a])
packAndRead xs = case packListVec xs of
  Pair n v -> (natToInt n, toListVec v)

firstAndPacked :: (String, (Int, String))
firstAndPacked = (headVec combined, packAndRead "plfh")
```

:::

::: {.plfh-showcase-group data-showcase-tab="agda-mode" data-showcase-label="Agda-Mode & Typed Holes"}

## Agda-Mode Typed Holes, Case Splits, Subgoal Refinement & 1-Step Synthesis

<div class="showcase-credits">
  <strong>Spec &amp; Research:</strong>
  Matth&iacute;as P&aacute;ll Gissurarson,
  <a href="https://doi.org/10.1145/3242744.3242760"><em>Suggesting Valid Hole Fits for Typed-Holes in Haskell</em></a>
  (Haskell 2018) &middot;
  Extended for Dependent Haskell subgoal splitting &amp; case-split suggestions &middot;
  Inspired by <a href="https://plfa.inf.ed.ac.uk/">PLFA</a> &amp; Emacs <code>agda-mode</code>
</div>

Click **Edit** and press **`Ctrl/Cmd+Enter`** (or click **Check in GHCi
(Wasm)** directly): GHC highlights `_` in an Agda-green goal box, suggests
splitting on `m` to unblock `plus`, and lets you finish `plusAssoc` via
subgoal refinement (`cong Succ _`) or 1-step synthesis (`cong Succ (plusAssoc m
n p)`). When the proof checks, the buffer lights up in full semantic colors.

```{.haskell data-showcase-hole="1"}
{-# LANGUAGE DependentTypes #-}
module ShowcaseAgdaMode where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..), plus)
import PLFH.Part1.Induction (cong)

-- Solve in 3 clicks:
-- 1. Check in GHCi (Wasm) -> click "Split on m (Zero | Succ)"
-- 2. Click "Refl" for the Zero branch
-- 3. Click "cong Succ (plusAssoc m n p)" (or refine via "cong Succ _")!
plusAssoc :: foreach (m n p :: Nat)
          -> plus (plus m n) p :~: plus m (plus n p)
plusAssoc m n p = _
```

:::

---

## Credits, Specifications & Upcoming Waves

Dependent Haskell in [`TharkunAB/ghc`](https://github.com/TharkunAB/ghc/tree/dependent-haskell)
builds directly on years of design, proposals, and research across the Haskell
and GHC community:

- **GHC Proposals & Authors:**
  - [`#378`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html)
    (*Design for Dependent Types*), [`#364`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0364-unify-natural.html),
    [`#473`](https://github.com/ghc-proposals/ghc-proposals/pull/473) — Richard A. Eisenberg
  - [`#281`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0281-visible-forall.html)
    (*Visible `forall` in types of terms*), [`#402`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0402-gadt-syntax.html),
    [`#425`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0425-decl-invis-binders.html),
    [`#475`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0475-tuple-syntax.html),
    [`#581`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0581-namespace-specified-imports.html) — Vladislav Zavialov
  - [`#242`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0242-unsaturated-type-families.html)
    (*Unsaturated Type Families*) — Csongor Kiss, Tony Field, Susan Eisenbach, and Simon Peyton Jones
  - [`#370`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0370-modifiers.html)
    (*Syntax for Modifiers*) — Arnaud Spiwack, Richard A. Eisenberg, and Vladislav Zavialov
  - [`#282`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0282-record-dot-syntax.html)
    (*Record Dot Syntax*) — Neil Mitchell, Shayne Fletcher, and Adam Gundry
  - [`#509`](https://github.com/ghc-proposals/ghc-proposals/pull/509) (*Type-Level Functions*) and
    [`#523`](https://github.com/ghc-proposals/ghc-proposals/pull/523) (*Extended `let` / local type synonyms*)
- **Serokell Dependent Haskell Roadmap:**
  [`ghc.serokell.io/dh`](https://ghc.serokell.io/dh) (50 roadmap cards `R01`–`R50` and dependency graph).
- **Foundational Literature & Textbooks:**
  Adam Gundry (2013), Richard A. Eisenberg (2016), Stephanie Weirich et al.
  ([ICFP 2017](https://doi.org/10.1145/3110275), [ICFP 2019](https://doi.org/10.1145/3341705)),
  Csongor Kiss et al. ([ICFP 2019](https://doi.org/10.1145/3341706)),
  Matth&iacute;as P&aacute;ll Gissurarson ([Haskell 2018](https://doi.org/10.1145/3242744.3242760)),
  and Philip Wadler, Wen Kokke, &amp; Jeremy G. Siek ([PLFA](https://plfa.inf.ed.ac.uk/), CC BY 4.0).
- **Coming in the Wave 12–13 Wasm refreshes:**
  Proposal [`#473`](https://github.com/ghc-proposals/ghc-proposals/pull/473) erased existentials
  (`GHC.Exists` / `Exists`, `Pack`, `(/\)`, `Witness`, `withExists`, `mapExists`),
  linear `foreach (b %1 :: Bool)` binders, GADT off-diagonal branch refutation
  (`zipEqualVec`), Proposal [`#523`](https://github.com/ghc-proposals/ghc-proposals/pull/523)
  local `type` synonyms, and [`TharkunAB/dependent-base`](https://github.com/TharkunAB/dependent-base)
  (including dependent function composition `(.)`).
