---
title: "Dependent Haskell: Roadmap & Live Walkthrough"
prev: /Overview/
next: /Playground/
src: content/Showcase.md
playground: true
---

[`TharkunAB/ghc` (`dependent-haskell`, tag `dependent-haskell-alpha`)](https://github.com/TharkunAB/ghc/tree/dependent-haskell)
implements the open cards of the
[Serokell Dependent Haskell roadmap](https://ghc.serokell.io/dh) on top of GHC
10.1, validated end to end against all 25 chapters of PLFH and compiled to
`wasm32-wasi` so every example below compiles and runs in your browser.

<div class="showcase-scorecard" aria-label="Project milestones">
  <div class="scorecard-item">
    <div class="scorecard-num">50 / 50</div>
    <div class="scorecard-label">Serokell roadmap cards</div>
    <div class="scorecard-sub">23 upstream GHC + 27 fork</div>
  </div>
  <div class="scorecard-item">
    <div class="scorecard-num">25 / 25</div>
    <div class="scorecard-label">PLFH chapters verified</div>
    <div class="scorecard-sub">Core Lint, STG Lint &amp; <code>.hi</code> audit</div>
  </div>
  <div class="scorecard-item">
    <div class="scorecard-num">642</div>
    <div class="scorecard-label">Compiler showcase checks</div>
    <div class="scorecard-sub"><code>-O0</code>, <code>-O2</code>, &amp; GHCi + 91 registered</div>
  </div>
  <div class="scorecard-item">
    <div class="scorecard-num">3</div>
    <div class="scorecard-label">Companion packages</div>
    <div class="scorecard-sub"><code>dependent-base</code>, <code>obs-eq</code>, <code>proof-search</code></div>
  </div>
</div>

## 1. The 50-Card Roadmap & Dependency Map {#roadmap-map}

Serokell's [Dependent Haskell roadmap](https://ghc.serokell.io/dh) connects
stock GHC to full-spectrum dependent types through **50 cards** and **67
dependency edges** (see the fork's
[`ROADMAP.md`](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/ROADMAP.md)
and [`PROPOSAL-378.md`](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/PROPOSAL-378.md)).
Twenty-three cards already live in upstream GHC; this fork implements the
remaining 27 cards and three companion libraries built on top.

**Hover** any card to trace what it depends on (blue) and what it unlocks
(teal). **Click** any card to read its scope, links, and explicit design
boundaries, then jump directly to a runnable WebAssembly example below.

<div id="plfh-roadmap-dag" class="showcase-dag-shell">
  <p class="dag-fallback">Enable JavaScript to explore the interactive 50-card roadmap graph, or open the complete card index at the bottom of this page.</p>
</div>

## 2. Design Decisions & Deliberate Boundaries {#decisions}

Building Dependent Haskell inside a production Haskell compiler requires
explicit trade-offs. Six architectural decisions govern the fork and its
companion libraries:

<div class="showcase-decisions">
  <div class="decision-card">
    <h3>1. Four-tier specification authority</h3>
    <p>Every syntax, flag, and typing rule follows a fixed hierarchy:
    <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html">GHC Proposal #378</a>
    first, companion GHC proposals (<code>#281</code>, <code>#242</code>, <code>#370</code>, <code>#402</code>, <code>#425</code>, <code>#473</code>, <code>#475</code>, <code>#509</code>, <code>#523</code>, <code>#581</code>, <code>#765</code>) second,
    the Serokell roadmap for scope tracking, and Agda/PLFA for ergonomics where proposals are silent.</p>
  </div>
  <div class="decision-card">
    <h3>2. Opt-in <code>-XDependentTypes</code> &amp; <code>Haskell2010</code> interop</h3>
    <p>Existing Haskell code stays untouched. One umbrella pragma (<code>-XDependentTypes</code>)
    enables retained binders, open/closed function promotion, and <code>NoListTuplePuns</code>.
    Ordinary <code>Haskell2010</code> clients can import compiled <code>.hi</code> interfaces from
    <code>dependent-base</code> without enabling dependent extensions.</p>
  </div>
  <div class="decision-card">
    <h3>3. Soundness without forced totality + modular plugins</h3>
    <p>Following Weirich et al. (ICFP 2017), System FC stays type-safe without forcing
    every Haskell program to terminate. Structural totality checking is opt-in
    (<code>-freport-totality</code>). Observational equality
    (<a href="https://github.com/TharkunAB/dependent-obs-eq"><code>dependent-obs-eq</code></a>, Jules <code>@analytichegel</code>)
    and proof search
    (<a href="https://github.com/TharkunAB/dependent-proof-search"><code>dependent-proof-search</code></a>)
    live as external GHC plugins rather than ad-hoc rules inside the core solver or <code>Hole.hs</code>.</p>
  </div>
  <div class="decision-card">
    <h3>4. Zero-wrapper <code>dependent-base</code></h3>
    <p>Modeled on <code>tweag/linear-base</code> and <code>agda-prelude</code>,
    <a href="https://github.com/TharkunAB/dependent-base"><code>dependent-base</code></a>
    operates directly on stock <code>Prelude</code> types (<code>Bool</code>, <code>Maybe</code>,
    <code>Either</code>, <code>(,)</code>, <code>[a]</code>, <code>(:~:)</code>, <code>Void</code>)
    with zero wrapper datatypes, and generalizes <code>(.)</code> and <code>($)</code> to
    dependent consumers without breaking ordinary callers.</p>
  </div>
  <div class="decision-card">
    <h3>5. Three explicit design boundaries</h3>
    <p>We deliberately preserve three boundaries rather than breaking compatibility:
    <strong>R27</strong> keeps <code>CUSKs</code> default in <code>Haskell98</code>/<code>Haskell2010</code>
    (while <code>-XDependentTypes</code> implies <code>NoCUSKs</code>);
    <strong>R34</strong> keeps GHC's internal <code>HsExpr</code>/<code>HsType</code> ASTs separate
    and reserves bare <code>a -&gt; b</code> in patterns for <code>ViewPatterns</code>;
    <strong>R06</strong> keeps effectful <code>IO</code> and uncertified non-structural functions
    outside type-level conversion (<code>#378 §4.10</code>).</p>
  </div>
  <div class="decision-card">
    <h3>6. Verified end to end by PLFH &amp; WebAssembly</h3>
    <p>Every compiler wave is checked against 25 PLFA textbook chapters (with Core Lint,
    STG Lint, <code>.hi</code> soundness audits, 10 negative controls,
    and 183 runtime checks), 642 compiler Showcase checks, and a live <code>wasm32-wasi</code>
    browser build with compiler-exact <code>RenamedSource</code> semantic highlighting.</p>
  </div>
</div>

## 3. Interactive Five-Act Walkthrough {#walkthrough}

All examples below are visible as you scroll—nothing is hidden behind tabs.
Click **Check in GHCi (Wasm)** on any card, check an entire Act, or click
**Edit** to open the Agda-mode editor (**`Ctrl/Cmd+Enter`** to re-check).

<div id="plfh-showcase-bar" class="plfh-chapter-bar plfh-showcase-sticky"></div>

::: {.plfh-showcase-act id="act-1" data-act-num="1" data-act-title="Core & Quantifiers"}

### Act 1 — Retained Quantifiers & Dependent Core (`R02`, `R03`, `R04`, `R05`, `R11`, `R39`)

Haskell separates erased compile-time arguments (`forall`) from runtime values
(`->`). Dependent Haskell adds a third point in the design space: **retained
dependent quantifiers** (`foreach` for dependent products `Π` and `some` /
`Sigma` for dependent sums `Σ`), backed by native `DepFunTy` and `TermVarTy` in
GHC's System FC Core (`R05`).

#### 1.1 Unified Quantifiers (`foreach`), Peano Arithmetic & Decimal Literals {#card-nat}

<div class="showcase-credits">
  <strong>Spec &amp; Roadmap:</strong>
  GHC Proposal <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#quantifiers">#378 §4.4 Quantifiers</a> &amp;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#dependent-pattern-match">§4.5 Dependent Pattern-Match</a>
  (Richard A. Eisenberg) &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0364-unify-natural.html">#364 Unify <code>Nat</code> &amp; <code>Natural</code></a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#dependent-products">R03</a>,
  <a href="https://ghc.serokell.io/dh#promote-literals">R07</a>,
  <a href="https://ghc.serokell.io/dh#promote-natural">R09</a> &middot;
  <a href="https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R03-dependent-products.md">Fork R03 notes</a>
</div>

Ordinary Peano functions (`plus`) and decimal literals (`2 + 3`) compute
directly in types under `-XDependentTypes` with zero `type family` or singleton
boilerplate.

```haskell
{-# LANGUAGE DependentTypes #-}
module ShowcaseNat where

import Data.Nat.Dependent (Nat (..), natToInt, plus, type (+))
import Data.Type.Equality.Dependent ((:~:) (Refl), cong)

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

#### 1.2 Retained Dependent Pairs (`Sigma` / `some`) & `OverloadedRecordDot` {#card-sigma}

<div class="showcase-credits">
  <strong>Spec &amp; Roadmap:</strong>
  GHC Proposal <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#erasure">#378 §4.2 Predictable Erasure</a>
  (Richard A. Eisenberg) &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0282-record-dot-syntax.html">#282 Record Dot Syntax</a>
  (Neil Mitchell, Shayne Fletcher, Adam Gundry) &middot;
  Serokell <a href="https://ghc.serokell.io/dh#dependent-retained-quantifiers">R02</a>,
  <a href="https://ghc.serokell.io/dh#dependent-sums">R04</a> &middot;
  <a href="https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R04-dependent-sums.md">Fork R04 notes</a>
</div>

`some (x :: a) | p x` (`GHC.Sigma.Sigma`) pairs a runtime witness with a
dependent proof or length-indexed payload, and projects fields via `.first` and
`.second` under `-XOverloadedRecordDot`.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns, OverloadedRecordDot, UndecidableInstances #-}
module ShowcaseSigma where

import Data.Nat.Dependent (Nat (..), natToInt, plus)
import Data.Sigma.Dependent (Sigma (Pair), first)
import Data.Type.Equality ((:~:) (Refl))
import Data.Vec.Dependent (SomeVec, Vec (..), toListVec)
import GHC.Sigma.Projection (second)

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

#### 1.3 Dependent Records & Parameterized Record Updates {#card-records}

<div class="showcase-credits">
  <strong>Spec &amp; Roadmap:</strong>
  GHC Proposal <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0282-record-dot-syntax.html">#282 Record Dot Syntax</a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#dependent-sums">R04 Dependent sums</a> &middot;
  <a href="https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R04-dependent-sums.md">Fork R04 notes</a>
</div>

Dependent records let later fields depend on earlier fields, project dependent
payloads with `.field`, and perform type-changing updates that preserve the
stored index.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns, OverloadedRecordDot #-}
module ShowcaseDependentRecords where

import Data.Nat.Dependent (Nat (..), natToInt)
import Data.Vec.Dependent (Vec (..), mapVec, toListVec)

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

#### 1.4 Runtime `Type` Pattern Matching (`foreach (a :: Type)`) {#card-typecase}

<div class="showcase-credits">
  <strong>Spec &amp; Roadmap:</strong>
  GHC Proposal <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#phase-distinction">#378 §4.9 Phase Distinction</a>
  (Richard A. Eisenberg) &middot;
  Serokell <a href="https://ghc.serokell.io/dh#dependent-products">R03</a>,
  <a href="https://ghc.serokell.io/dh#type-level-case-expressions">R19</a>,
  <a href="https://ghc.serokell.io/dh#syntactic-unification">R34</a>
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

#### 1.5 Linear `foreach` Binders (`foreach (x %1 :: a)`) {#card-linear}

<div class="showcase-credits">
  <strong>Spec &amp; Roadmap:</strong>
  GHC Proposal <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0111-linear-types.html">#111 Linear Types</a>
  (Jean-Philippe Bernardy et al., <a href="https://doi.org/10.1145/3158093">POPL 2018</a>) &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#quantifiers">#378 §4.4 Quantifiers</a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#dependent-products">R03</a>,
  <a href="https://ghc.serokell.io/dh#dependent-core-language">R05</a>
</div>

Dependent `foreach` binders compose with `-XLinearTypes`: a linear retained
argument (`%1`) is consumed exactly once at runtime while appearing freely any
number of times in erased type indices.

```haskell
{-# LANGUAGE DependentTypes, LinearTypes, ListTuplePuns #-}
module ShowcaseLinearForEach where

import Data.Nat.Dependent (Nat (..), natToInt)

data SingBool (b :: Bool) where
  STrue  :: SingBool True
  SFalse :: SingBool False

data SamePair (m :: Nat) (n :: Nat) = SamePair

-- Consume a linear Bool once at runtime while refining the result index:
linearSingBool :: foreach (b %1 :: Bool) -> SingBool b
linearSingBool True  = STrue
linearSingBool False = SFalse

-- Mention `n` twice in the erased type `SamePair n n`, yet consume `n` once at runtime:
dupInTypeLinear :: foreach (n %1 :: Nat) -> SamePair n n -> Nat
dupInTypeLinear n SamePair = n

linearDemo :: (Bool, Int)
linearDemo =
  let bOk = case linearSingBool True of STrue -> True
      nOk = natToInt (dupInTypeLinear (Succ Zero) SamePair)
  in (bOk, nOk)
```

#### 1.6 Off-Diagonal GADT Refutation (`zipEqualVec`) {#card-refute}

<div class="showcase-credits">
  <strong>Spec &amp; Roadmap:</strong>
  GHC Proposal <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#dependent-pattern-match">#378 §4.5 Dependent Pattern-Match</a> &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0402-gadt-syntax.html">#402 GADT Syntax</a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#dependent-products">R03</a>,
  <a href="https://ghc.serokell.io/dh#homogeneous-equality">R11</a>,
  <a href="https://ghc.serokell.io/dh#nested-quantification-in-gadts">R41</a>
</div>

When two independent `foreach` lengths are equated by `m :~: n`, GHC's
dependent pattern-match checker refutes impossible off-diagonal cases
(`Zero`/`Succ` and `Succ`/`Zero`), leaving only the two diagonal clauses with
zero dummy `error` branches.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module ShowcaseRefute where

import Data.Nat.Dependent (Nat (..))
import Data.Type.Equality ((:~:) (Refl))
import Data.Vec.Dependent (Vec (..), toListVec)

zipEqualVec :: foreach (m n :: Nat)
            -> Vec a m -> Vec b n -> (m :~: n) -> Vec (a, b) m
zipEqualVec Zero      Zero      VNil         VNil         Refl = VNil
zipEqualVec (Succ m') (Succ n') (VCons x xs) (VCons y ys) Refl =
  VCons (x, y) (zipEqualVec m' n' xs ys Refl)

zippedDemo :: [(Int, Char)]
zippedDemo =
  let two = Succ (Succ Zero)
      xs  = VCons (1 :: Int) (VCons 2 VNil)
      ys  = VCons 'a' (VCons 'b' VNil)
  in toListVec (zipEqualVec two two xs ys Refl)
```

:::

::: {.plfh-showcase-act id="act-2" data-act-num="2" data-act-title="Promotion & Open Eval"}

### Act 2 — Universal Promotion, Open/Closed Evaluation & Large Eliminations (`R06`, `R10`, `R12`–`R17`, `R21`, `R23`)

Retained quantifiers alone are not enough if every function must be duplicated
as a `type family`. Act 2 shows the promotion stack: GHC publishes checked
source equations for ordinary Haskell functions into `.hi` interfaces (`R13`),
evaluates both closed (`R15`) and symbolic open calls (`R16`), tracks
matchability for unsaturated partial applications (`R23`), and stages mixed
same-module term/type declarations automatically (`R21`).

#### 2.1 Stock `Prelude` Lists & Checked Open Evaluation {#card-lists}

<div class="showcase-credits">
  <strong>Spec &amp; Roadmap:</strong>
  GHC Proposal <a href="https://github.com/ghc-proposals/ghc-proposals/pull/509">#509 Type-Level Functions</a> (draft) &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0475-tuple-syntax.html">#475 Non-punning List &amp; Tuple Syntax</a>
  (Vladislav Zavialov) &middot;
  Serokell <a href="https://ghc.serokell.io/dh#function-promotion">R13</a>,
  <a href="https://ghc.serokell.io/dh#open-term-evaluator">R16</a>,
  <a href="https://ghc.serokell.io/dh#no-list-or-tuple-puns">R38</a> &middot;
  <a href="https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R16-open-term-evaluator.md">Fork R16 notes</a>
</div>

Ordinary functions over stock `Prelude` lists (`List a`, `(++)`, `map`,
`Data.List.Dependent.size`) reduce symbolically over unknown `foreach`
variables, proving structural and length laws directly without custom list
clones.

```haskell
{-# LANGUAGE DependentTypes, NoListTuplePuns #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}
module ShowcaseLists where

import Data.List.Dependent (size)
import Data.Nat.Dependent (Nat (..), natToInt, plus)
import Data.Type.Equality.Dependent ((:~:) (Refl), cong)
import GHC.Types (List)

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

#### 2.2 Matchability-Polymorphic `cong` & T2T Operator Sections {#card-sections}

<div class="showcase-credits">
  <strong>Spec &amp; Roadmap:</strong>
  GHC Proposal <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0242-unsaturated-type-families.html">#242 Unsaturated Type Families</a>
  (Csongor Kiss, Tony Field, Susan Eisenbach, Simon Peyton Jones; <a href="https://doi.org/10.1145/3341706">ICFP 2019</a>) &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0281-visible-forall.html">#281 Visible <code>forall</code></a>
  (Vladislav Zavialov) &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0370-modifiers.html">#370 Modifiers</a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#unsaturated-type-families">R23</a>,
  <a href="https://ghc.serokell.io/dh#type-level-lambdas">R17</a>,
  <a href="https://ghc.serokell.io/dh#modifiers-syntax">R25</a>,
  <a href="https://ghc.serokell.io/dh#visible-forall">R39</a> &middot;
  <a href="https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R23-unsaturated-type-families.md">Fork R23 notes</a>
</div>

Matchability polymorphism (`%M` / `%U`) combined with `RequiredTypeArguments`
and term-to-type operator sections lets a single `cong` accept matchable
constructors (`Succ`), unmatchable functions (`plus m`), and left/right
sections (`(x :)`, `(: ys)`) with zero `@` sigils.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module ShowcaseSections where

import Data.Nat.Dependent (Nat (..), plus)
import Data.Type.Equality.Dependent ((:~:) (Refl), cong)

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

#### 2.3 Term-to-`Type` Large Eliminations (Zero `type family`) {#card-large-elim}

<div class="showcase-credits">
  <strong>Spec &amp; Roadmap:</strong>
  GHC Proposal <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#syntactic-unification">#378 §4.3.3 Syntactic Unification</a> &amp;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#dependent-application-and-the-static-subset">§4.7 Dependent Application</a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#function-promotion">R13</a>,
  <a href="https://ghc.serokell.io/dh#closed-term-evaluator">R15</a>,
  <a href="https://ghc.serokell.io/dh#dependency-analysis">R21</a> &middot;
  <a href="https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R21-dependency-analysis.md">Fork R21 notes</a>
</div>

Ordinary Haskell functions compute `Type` directly from a runtime term argument
without writing a separate `type family`—the same mechanism used for PLFH's
[Adequacy](/Adequacy/) logical relation (`logVLam`).

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

::: {.plfh-showcase-act id="act-3" data-act-num="3" data-act-title="Language Cleanup"}

### Act 3 — Language Cleanup: Erased Existentials, Local `type` Synonyms & Namespaces (`R18`, `R20`, `R22`, `R24`, `R27`, `R35`, `R36`)

Serokell's third pillar removes historical friction between Haskell's term and
type namespaces: erased existentials (`#473` / `R22`), ordered type-level lets
and local `type` synonyms (`#523` / `R18`), constrained type families (`R24`),
and namespace-qualified imports with pun warnings (`#581` / `#765` / `R35`–`R36`).

#### 3.1 Erased Existentials (`GHC.Exists` & `Data.Exists.Dependent`) {#card-exists}

<div class="showcase-credits">
  <strong>Spec &amp; Roadmap:</strong>
  GHC Proposal <a href="https://github.com/ghc-proposals/ghc-proposals/pull/473">#473 Existential Types</a>
  (Richard A. Eisenberg) &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0581-namespace-specified-imports.html">#581 Namespace-Specified Imports</a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#existential-quantification">R22</a>,
  <a href="https://ghc.serokell.io/dh#namespace-management">R35</a>,
  <a href="https://ghc.serokell.io/dh#pun-warnings">R36</a> &middot;
  <a href="https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R22-existential-quantification.md">Fork R22 notes</a>
</div>

Unlike retained `Sigma` pairs, Proposal `#473` erased existentials (`Exists p =
exists x | p x`) hide a compile-time witness erased at runtime.
`Data.Exists.Dependent` exports `Pack`, `mapExists`, `withExists`, constraint
pairing `(/\)`, and erased `Witness` tokens.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module ShowcaseExists where

import Data.Char (toUpper)
import Data.Exists.Dependent
  ( Witness (Witness)
  , data Pack
  , mapExists
  , type (/\) (MkCPair)
  , withEvidence
  , withExists
  )
import Data.Nat.Dependent (Nat (..))
import Data.Vec.Dependent (Vec (..), mapVec, toListVec)
import GHC.Exists (Exists)

hiddenWord :: Exists (Vec Char)
hiddenWord = Pack (type (Succ (Succ Zero))) (VCons 'o' (VCons 'k' VNil))

shoutWord :: Exists (Vec Char)
shoutWord = mapExists (\_ xs -> mapVec toUpper xs) hiddenWord

existsDemo :: (Bool, String)
existsDemo =
  let paired :: Show Bool /\ Bool
      paired = MkCPair True
      witOk  = case Witness @Nat of Witness -> True
  in ( withEvidence paired (\b -> b && witOk)
     , withExists shoutWord (\_ xs -> toListVec xs) )
```

#### 3.2 Local `type` Synonyms in `let` & `where` (`#523` Extended `let`) {#card-local-type}

<div class="showcase-credits">
  <strong>Spec &amp; Roadmap:</strong>
  GHC Proposal <a href="https://github.com/ghc-proposals/ghc-proposals/pull/523">#523 Extended <code>let</code></a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#type-level-let-bindings">R18 Type-level let-bindings</a>,
  <a href="https://ghc.serokell.io/dh#dependency-analysis">R21</a>,
  <a href="https://ghc.serokell.io/dh#deprecate-cusks">R27</a> &middot;
  <a href="https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R18-type-level-lets.md">Fork R18 notes</a>
</div>

Non-recursive local `type` synonyms bind directly inside `let` and `where`
blocks, and capture retained `foreach` variables in scope to name local
dependent shapes cleanly.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module ShowcaseLocalTypeSyn where

import Data.Nat.Dependent (Nat (..))
import Data.Vec.Dependent (Vec (..))

localTypeSynDemo :: Int
localTypeSynDemo =
  let type PairOf a = (a, a)
      p :: PairOf Int
      p = (20, 22)
  in addPair (Succ Zero) p
  where
    addPair :: foreach (n :: Nat) -> (Int, Int) -> Int
    addPair n (u, v) =
      let v1 :: LocalVec Int
          v1 = VCons (u + v) (replicateZero n)
      in case v1 of
           VCons total _ -> total
      where
        type LocalVec b = Vec b (Succ n)
        replicateZero :: foreach (m :: Nat) -> Vec Int m
        replicateZero Zero     = VNil
        replicateZero (Succ k) = VCons 0 (replicateZero k)
```

:::

::: {.plfh-showcase-act id="act-4" data-act-num="4" data-act-title="dependent-base"}

### Act 4 — `dependent-base` & First-Class Dependent Combinators (`TharkunAB/dependent-base`)

Language features only prove themselves when real libraries compose cleanly.
[`TharkunAB/dependent-base`](https://github.com/TharkunAB/dependent-base)
(22 modules, zero wrapper types, `Haskell2010` `.hi`-only interop) turns the
compiler primitives into an ergonomic standard library—including a single
first-class `(.)` operator that works across dependent proofs, indexed vectors,
and ordinary Haskell functions.

#### 4.1 First-Class Dependent Composition `(.)` & `($)` {#card-dep-compose}

<div class="showcase-credits">
  <strong>Package &amp; Reference:</strong>
  <a href="https://github.com/TharkunAB/dependent-base"><code>TharkunAB/dependent-base</code></a> &middot;
  <a href="/DependentBase/#datafunctiondependent"><code>Data.Function.Dependent</code></a> &middot;
  Modeled on <a href="https://github.com/tweag/linear-base"><code>linear-base</code></a> &amp; <code>agda-prelude</code>
</div>

`Data.Function.Dependent.(.)` generalizes `Prelude.(.)` to dependent consumers
whose return type mentions `f x`. GHC synthesizes the motive automatically for
`plusZero . Succ`, `zeros . plus 1`, and `cong (Succ . plus m)`, while leaving
ordinary `Int -> Int` composition unchanged.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}
module ShowcaseDepCompose where

import Prelude hiding ((.))
import Data.Function.Dependent ((.))
import Data.Nat.Dependent (Nat (..), natToInt, plus)
import Data.Nat.Dependent.Properties (plusZero)
import Data.Type.Equality.Dependent ((:~:) (Refl), cong)
import Data.Vec.Dependent (Vec (..), toListVec)

zeros :: foreach (n :: Nat) -> Vec Nat n
zeros Zero     = VNil
zeros (Succ n) = VCons Zero (zeros n)

-- Dependent vector producer composed with an ordinary arithmetic function:
zerosPlus1 :: foreach (n :: Nat) -> Vec Nat (plus 1 n)
zerosPlus1 = (.) zeros (plus 1)

-- Dependent equality proof composed directly with constructor Succ:
plusIdSucc :: foreach (n :: Nat) -> plus (Succ n) Zero :~: Succ n
plusIdSucc = plusZero . Succ

-- Composed function passed directly to matchability-polymorphic cong:
congSuccPlus :: foreach (m :: Nat)
             -> forall (x y :: Nat). x :~: y -> Succ (plus m x) :~: Succ (plus m y)
congSuccPlus m eq = cong (Succ . plus m) eq

-- The exact same (.) works unchanged on ordinary non-dependent functions:
ordinaryCompose :: (Int -> Int) -> (Int -> Int) -> Int -> Int
ordinaryCompose g f = g . f

composeDemo :: ([Int], Int)
composeDemo = (map natToInt (toListVec (zerosPlus1 2)), ordinaryCompose (* 2) (+ 1) 20)
```

#### 4.2 Length-Indexed `Vec`, Safe `Fin` Indexing & Runtime List Boundaries {#card-vec-fin}

<div class="showcase-credits">
  <strong>Package &amp; Roadmap:</strong>
  <a href="https://github.com/TharkunAB/dependent-base"><code>TharkunAB/dependent-base</code></a> &middot;
  <a href="/DependentBase/#datavecdependent"><code>Data.Vec.Dependent</code></a> &amp;
  <a href="/DependentBase/#datafindependent"><code>Data.Fin.Dependent</code></a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#dependent-products">R03</a>,
  <a href="https://ghc.serokell.io/dh#dependent-sums">R04</a>,
  <a href="https://ghc.serokell.io/dh#homogeneous-equality">R11</a>
</div>

`Data.Vec.Dependent` and `Data.Fin.Dependent` pair static length guarantees
(`appendVec`, `zipVec`, total `lookupVec`) with explicit ordinary-list boundary
adapters (`packListVec`, `fromListExact`).

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module ShowcaseVecFin where

import Data.Fin.Dependent (Fin (..))
import Data.Nat.Dependent (Nat (..), natToInt)
import Data.Sigma.Dependent (Sigma (Pair))
import Data.Vec.Dependent
  ( Vec (..)
  , appendVec
  , headVec
  , lookupVec
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

::: {.plfh-showcase-act id="act-5" data-act-num="5" data-act-title="Agda-Mode & Plugins"}

### Act 5 — Interactive Agda-Mode, `dependent-proof-search` & `dependent-obs-eq`

Rather than hard-coding proof heuristics or non-standard equality rules into
GHC's core, the fork keeps `GHC.Tc.Errors.Hole` and System FC conversion clean
and exposes general plugin hooks (`HoleFitPlugin`, `TcPlugin`, and
`installCoreToDos`). Two standalone packages build on those hooks.

#### 5.1 Agda-Mode Typed Holes, Case Splits & `Dependent.Plugin.ProofSearch` {#card-agda-mode}

<div class="showcase-credits">
  <strong>Spec, Research &amp; Plugin:</strong>
  Matth&iacute;as P&aacute;ll Gissurarson,
  <a href="https://doi.org/10.1145/3242744.3242760"><em>Suggesting Valid Hole Fits for Typed-Holes in Haskell</em></a>
  (Haskell 2018) &middot;
  <a href="https://github.com/TharkunAB/dependent-proof-search"><code>TharkunAB/dependent-proof-search</code></a>
  (<code>-fplugin=Dependent.Plugin.ProofSearch</code>) &middot;
  Compiler-exact <code>RenamedSource</code> semantic highlighting
</div>

Click **Edit** and press **`Ctrl/Cmd+Enter`** (or click **Check in GHCi
(Wasm)** directly): GHC highlights `_` in an Agda-green goal box, suggests
splitting on `m` to unblock `plus`, and—with `Dependent.Plugin.ProofSearch`
active—suggests both step-by-step subgoal refinements (`cong Succ _`) and
direct bounded synthesis (`cong Succ (plusAssoc m n p)`). Try replacing the
proof of `plusComm` with `trans (plusSuc m k) (cong Succ (plusComm _ _))` too!

```{.haskell data-showcase-hole="1"}
{-# LANGUAGE DependentTypes #-}
module ShowcaseAgdaMode where

import Data.Nat.Dependent (Nat (..), plus)
import Data.Type.Equality.Dependent ((:~:) (Refl), cong)

-- Solve in 3 clicks:
-- 1. Check in GHCi (Wasm) -> click "Split on m (Zero | Succ)"
-- 2. Click "Refl" for the Zero branch
-- 3. Click "cong Succ (plusAssoc m n p)" (or refine via "cong Succ _")!
plusAssoc :: foreach (m n p :: Nat)
          -> plus (plus m n) p :~: plus m (plus n p)
plusAssoc m n p = _
```

#### 5.2 Observational Equality Plugin (`Dependent.Plugin.ObsEq`) {#card-obs-eq}

<div class="showcase-credits">
  <strong>Plugin, Credit &amp; Roadmap:</strong>
  Idea by <strong>Jules (<code>@analytichegel</code>)</strong> &middot;
  <a href="https://github.com/TharkunAB/dependent-obs-eq"><code>TharkunAB/dependent-obs-eq</code></a>
  (<code>-fplugin=Dependent.Plugin.ObsEq</code>) &middot;
  Uninterpreted open term calls (<code>U:f</code>) + GHC <code>TcPlugin</code> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#dependent-core-language">R05</a>,
  <a href="https://ghc.serokell.io/dh#homogeneous-equality">R11</a>,
  <a href="https://ghc.serokell.io/dh#open-term-evaluator">R16</a>
</div>

Non-structural, accumulator-based, or fuel-free functions (such as `unfoldPlus`,
`accPlus`, or `collatz`) do not have structural source equations in GHC's core
conversion. Enabling `Dependent.Plugin.ObsEq` elaborates open calls into
uninterpreted families (`U:f`) and tests observational equalities in-process
over total and partial (`ObsBottom`) inputs: `obsEq`, `obsEqWith`, and
`obsEqGen` discharge explicit witnesses without weakening bare `Refl`. Click
**Edit**, break `go Zero acc = acc` to `go Zero acc = Succ acc`, and press
**`Ctrl/Cmd+Enter`** to watch the plugin refute the law with a shrunk minimal
counterexample (`m = Zero, n = Zero`).

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ObsEq -fplugin-opt=Dependent.Plugin.ObsEq:tests=30 #-}
module ShowcaseObsEq where

import Data.Nat.Dependent (Nat (..), plus)
import Data.Type.Equality ((:~:) (Refl), gcastWith)
import Data.Vec.Dependent (Vec (..), toListVec)
import Dependent.ObsEq
  ( Gen
  , ObsConfig
  , chooseInt
  , defaultObsConfig
  , obsEq
  , obsEqGen
  , obsEqWith
  , withMaxSize
  , withObsEqWith
  , withPartialPct
  , withTests
  )

-- 1. Non-structural unfold addition (lazy-equivalent to plus on partial inputs too).
unfoldPlus :: Nat -> Nat -> Nat
unfoldPlus m n = step (Just m) n
  where
    step Nothing acc         = acc
    step (Just Zero) acc     = step Nothing acc
    step (Just (Succ k)) acc = Succ (step (Just k) acc)

-- 2. Non-structural tail-recursive accumulator addition (total-domain equivalent to plus).
-- Try changing `go Zero acc = acc` to `go Zero acc = Succ acc` to see counterexample shrinking!
accPlus :: Nat -> Nat -> Nat
accPlus m n = go m n
  where
    go Zero acc     = acc
    go (Succ k) acc = go k (Succ acc)

-- 3. Non-structural fuel-free Collatz convergence on total Nats.
isEvenNat :: Nat -> Bool
isEvenNat Zero            = True
isEvenNat (Succ Zero)     = False
isEvenNat (Succ (Succ n)) = isEvenNat n

halfNat :: Nat -> Nat
halfNat Zero            = Zero
halfNat (Succ Zero)     = Zero
halfNat (Succ (Succ n)) = Succ (halfNat n)

tripleNat :: Nat -> Nat
tripleNat Zero     = Zero
tripleNat (Succ n) = Succ (Succ (Succ (tripleNat n)))

collatz :: Nat -> Nat
collatz Zero        = Succ Zero
collatz (Succ Zero) = Succ Zero
collatz n
  | isEvenNat n = collatz (halfNat n)
  | otherwise   = collatz (Succ (tripleNat n))

-- 4. Domain-restricted law on even Ints via custom generator (obsEqGen).
twiceHalfEven :: Int -> Int
twiceHalfEven n
  | even n    = (n `quot` 2) * 2
  | otherwise = error "twiceHalfEven: odd input"

genEvenInt :: Gen Int
genEvenInt = (* 2) <$> chooseInt (-50, 50)

totalCfg :: ObsConfig
totalCfg = withMaxSize 12 (withPartialPct 0 (withTests 30 defaultObsConfig))

unfoldPlusCorrect :: foreach (m n :: Nat) -> unfoldPlus m n :~: plus m n
unfoldPlusCorrect m n = obsEq

accPlusCorrect :: foreach (m n :: Nat) -> accPlus m n :~: plus m n
accPlusCorrect m n = obsEqWith totalCfg

collatzConverges :: foreach (n :: Nat) -> collatz n :~: Succ Zero
collatzConverges n = obsEqWith totalCfg

evenRoundtrip :: foreach (n :: Int) -> twiceHalfEven n :~: n
evenRoundtrip n = obsEqGen genEvenInt

-- Transport a dependent-base Vec across an observational witness at runtime:
toAccVec :: foreach (m n :: Nat) -> Vec Int (plus m n) -> Vec Int (accPlus m n)
toAccVec m n v = gcastWith (obsEqWith totalCfg :: plus m n :~: accPlus m n) v

fromAccVec :: foreach (m n :: Nat) -> Vec Int (accPlus m n) -> Vec Int (plus m n)
fromAccVec m n v = withObsEqWith totalCfg @(accPlus m n) @(plus m n) @(Vec Int (plus m n)) v

roundtripAccVec :: foreach (m n :: Nat) -> Vec Int (plus m n) -> Vec Int (plus m n)
roundtripAccVec m n v = fromAccVec m n (toAccVec m n v)

sampleAccVec :: [Int]
sampleAccVec = toListVec (roundtripAccVec 2 1 (VCons 10 (VCons 20 (VCons 30 VNil))))
```

:::

---

## 4. Complete 50-Card Roadmap Index (`R01`–`R50`) {#complete-index}

<details class="roadmap-index-details">
<summary>Expand full table of all 50 Serokell cards (23 upstream GHC + 27 fork implemented)</summary>

| Card | Serokell Title | Status | Depends on | Fork / Proposal Reference |
| --- | --- | --- | --- | --- |
| **R01** | [Dependent Haskell](https://ghc.serokell.io/dh#dependent-haskell) | Fork | R02, R06, R20 | [`#378`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html), [`PROPOSAL-378.md`](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/PROPOSAL-378.md) |
| **R02** | [Dependent retained quantifiers](https://ghc.serokell.io/dh#dependent-retained-quantifiers) | Fork | R03, R04 | `#378 §4.2–4.5` |
| **R03** | [Dependent products](https://ghc.serokell.io/dh#dependent-products) | Fork | R05, R39 | [R03 notes](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R03-dependent-products.md) |
| **R04** | [Dependent sums](https://ghc.serokell.io/dh#dependent-sums) | Fork | R05, R22 | [R04 notes](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R04-dependent-sums.md) |
| **R05** | [Dependent Core language](https://ghc.serokell.io/dh#dependent-core-language) | Fork | — | [R05 notes](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R05-dependent-core.md) |
| **R06** | [Universal promotion](https://ghc.serokell.io/dh#universal-promotion) | Fork (boundary: `#378 §4.10`) | R07, R10, R12, R13, R14 | Pure promotion; `IO` excluded |
| **R07** | [Promote literals](https://ghc.serokell.io/dh#promote-literals) | Fork | R08, R09, R24 | [`#364`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0364-unify-natural.html) |
| **R08** | [Promote Char](https://ghc.serokell.io/dh#promote-char) | Upstream GHC | — | Inherited `DataKinds` `Char` |
| **R09** | [Promote Natural](https://ghc.serokell.io/dh#promote-natural) | Upstream GHC | — | [`#364`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0364-unify-natural.html) |
| **R10** | [Promote unboxed types](https://ghc.serokell.io/dh#promote-unboxed-types) | Fork | R11 | [R10 notes](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R10-unboxed-promotion.md) |
| **R11** | [Homogeneous equality](https://ghc.serokell.io/dh#homogeneous-equality) | Fork | — | [R11 notes](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R11-homogeneous-equality.md) |
| **R12** | [Promote classes](https://ghc.serokell.io/dh#promote-classes) | Fork | R13, R24 | [R12 notes](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R12-promote-classes.md) |
| **R13** | [Function promotion](https://ghc.serokell.io/dh#function-promotion) | Fork | R15–R19, R21, R23 | [R16 notes](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R16-open-term-evaluator.md) |
| **R14** | [Data family promotion](https://ghc.serokell.io/dh#data-family-promotion) | Fork | — | [R14 notes](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R14-data-family-promotion.md) |
| **R15** | [Closed term evaluator](https://ghc.serokell.io/dh#closed-term-evaluator) | Fork | — | [R15 notes](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R15-closed-term-evaluator.md) |
| **R16** | [Open term evaluator](https://ghc.serokell.io/dh#open-term-evaluator) | Fork | — | [R16 notes](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R16-open-term-evaluator.md) |
| **R17** | [Type-level lambdas](https://ghc.serokell.io/dh#type-level-lambdas) | Fork | R05, R16 | [R17 notes](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R17-type-level-lambdas.md) |
| **R18** | [Type-level let-bindings](https://ghc.serokell.io/dh#type-level-let-bindings) | Fork (release-ready) | R05, R16 | [R18 notes](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R18-type-level-lets.md), `#523` |
| **R19** | [Type-level case-expressions](https://ghc.serokell.io/dh#type-level-case-expressions) | Fork | R05, R16 | [R19 notes](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R19-type-level-cases.md) |
| **R20** | [Clean up the language](https://ghc.serokell.io/dh#clean-up-the-language) | Fork | R21–R24, R27, R28, R35, R39, R49 | Aggregate milestone |
| **R21** | [Dependency analysis](https://ghc.serokell.io/dh#dependency-analysis) | Fork | — | [R21 notes](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R21-dependency-analysis.md) |
| **R22** | [Existential quantification](https://ghc.serokell.io/dh#existential-quantification) | Fork | — | [R22 notes](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R22-existential-quantification.md), `#473` |
| **R23** | [Unsaturated type families](https://ghc.serokell.io/dh#unsaturated-type-families) | Fork | R25 | [R23 notes](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R23-unsaturated-type-families.md), `#242` |
| **R24** | [Constrained type families](https://ghc.serokell.io/dh#constrained-type-families) | Fork | — | [R24 notes](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R24-constrained-type-families.md) |
| **R25** | [Modifiers syntax](https://ghc.serokell.io/dh#modifiers-syntax) | Upstream GHC | — | [`#370`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0370-modifiers.html) |
| **R26** | [Standalone kind signatures](https://ghc.serokell.io/dh#standalone-kind-signatures) | Upstream GHC | — | Implied by `-XDependentTypes` |
| **R27** | [Deprecate CUSKs](https://ghc.serokell.io/dh#deprecate-cusks) | Fork (boundary: H98/H2010) | R26, R29 | [R27 notes](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R27-deprecate-cusks.md) |
| **R28** | [Invisible type arguments](https://ghc.serokell.io/dh#invisible-type-arguments) | Upstream GHC | R29–R33 | Inherited upstream |
| **R29** | [Invisible binders in types](https://ghc.serokell.io/dh#invisible-binders-in-types) | Upstream GHC | R26 | [`#425`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0425-decl-invis-binders.html) |
| **R30** | [Invisible binders in functions](https://ghc.serokell.io/dh#invisible-binders-in-functions) | Upstream GHC | — | `#448` |
| **R31** | [Invisible binders in constructors](https://ghc.serokell.io/dh#invisible-binders-in-constructors) | Upstream GHC | — | `#126` |
| **R32** | [Visible type applications](https://ghc.serokell.io/dh#visible-type-applications) | Upstream GHC | — | `TypeApplications` |
| **R33** | [Visible kind applications](https://ghc.serokell.io/dh#visible-kind-applications) | Upstream GHC | — | `#15` |
| **R34** | [Syntactic unification](https://ghc.serokell.io/dh#syntactic-unification) | Fork (boundary: AST split) | R44–R47 | `#378 §4.3`, `#281` |
| **R35** | [Namespace management](https://ghc.serokell.io/dh#namespace-management) | Fork (release-ready) | R36–R38, R42 | [R35 notes](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R35-namespace-management.md) |
| **R36** | [Pun warnings](https://ghc.serokell.io/dh#pun-warnings) | Fork (release-ready) | — | [R36 notes](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R36-pun-warnings.md), `#765` |
| **R37** | [Namespace-specified imports](https://ghc.serokell.io/dh#namespace-specified-imports) | Upstream GHC | — | [`#581`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0581-namespace-specified-imports.html) |
| **R38** | [No list or tuple puns](https://ghc.serokell.io/dh#no-list-or-tuple-puns) | Upstream GHC | — | [`#475`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0475-tuple-syntax.html) |
| **R39** | [Visible forall](https://ghc.serokell.io/dh#visible-forall) | Upstream GHC | R34, R40, R41, R43 | [`#281`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0281-visible-forall.html) |
| **R40** | [Visibility coercions](https://ghc.serokell.io/dh#visibility-coercions) | Upstream GHC | — | `#281` |
| **R41** | [Nested quantification in GADTs](https://ghc.serokell.io/dh#nested-quantification-in-gadts) | Fork (release-ready) | — | [R41 notes](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/R41-nested-quantification-in-gadts.md), `#402` |
| **R42** | [Embed types](https://ghc.serokell.io/dh#embed-types) | Upstream GHC | — | `(type T)` herald |
| **R43** | [Term variable capture](https://ghc.serokell.io/dh#term-variable-capture) | Upstream GHC | — | `#281` |
| **R44** | [No star kind syntax](https://ghc.serokell.io/dh#no-star-kind-syntax) | Upstream GHC | R50 | `NoStarIsType` |
| **R45** | [The forall keyword](https://ghc.serokell.io/dh#the-forall-keyword) | Upstream GHC | — | `#378` |
| **R46** | [The tilde operator](https://ghc.serokell.io/dh#the-tilde-operator) | Upstream GHC | R48 | `#229` |
| **R47** | [The dot type operator](https://ghc.serokell.io/dh#the-dot-type-operator) | Upstream GHC | R48 | `#229`, `#282` |
| **R48** | [Whitespace-sensitive operators](https://ghc.serokell.io/dh#whitespace-sensitive-operators) | Upstream GHC | — | `#229` |
| **R49** | [Unify type and kind variables](https://ghc.serokell.io/dh#unify-type-and-kind-variables) | Upstream GHC | R50 | `PolyKinds` |
| **R50** | [Unify types and kinds](https://ghc.serokell.io/dh#unify-types-and-kinds) | Upstream GHC | — | `TypeInType` |

</details>

## 5. Credits & Literature {#credits}

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
  - [`#509`](https://github.com/ghc-proposals/ghc-proposals/pull/509) (*Type-Level Functions*),
    [`#523`](https://github.com/ghc-proposals/ghc-proposals/pull/523) (*Extended `let`*), and
    [`#765`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0765-pun-warnings.html) (*Pun Warnings*)
- **Serokell Dependent Haskell Roadmap:**
  [`ghc.serokell.io/dh`](https://ghc.serokell.io/dh) (50 roadmap cards `R01`–`R50` and 67 dependency edges).
- **Companion Packages:**
  - [`TharkunAB/dependent-base`](https://github.com/TharkunAB/dependent-base) — zero-wrapper Dependent Haskell standard library
  - [`TharkunAB/dependent-obs-eq`](https://github.com/TharkunAB/dependent-obs-eq) — QuickCheck observational equality `TcPlugin`, credited to **Jules (`@analytichegel`)**
  - [`TharkunAB/dependent-proof-search`](https://github.com/TharkunAB/dependent-proof-search) — bounded proof-search `HoleFitPlugin`
- **Foundational Literature & Textbooks:**
  Adam Gundry (2013), Richard A. Eisenberg (2016), Stephanie Weirich et al.
  ([ICFP 2017](https://doi.org/10.1145/3110275), [ICFP 2019](https://doi.org/10.1145/3341705)),
  Csongor Kiss et al. ([ICFP 2019](https://doi.org/10.1145/3341706)),
  Matth&iacute;as P&aacute;ll Gissurarson ([Haskell 2018](https://doi.org/10.1145/3242744.3242760)),
  and Philip Wadler, Wen Kokke, &amp; Jeremy G. Siek ([PLFA](https://plfa.inf.ed.ac.uk/), CC BY 4.0).
