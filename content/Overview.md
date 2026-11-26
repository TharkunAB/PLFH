---
title: "Dependent Haskell in GHC"
description: "Full-spectrum dependent types in GHC 10.1 (-XDependentTypes): type-safe web routes as values, runtime monad stacks, type-level case and lambdas, Agda-mode holes, and a 25-chapter textbook running live in WebAssembly."
prev: /
next: /Playground/
src: content/Overview.md
playground: true
---

<div class="hero-actions">
  <a class="hero-btn hero-btn--primary" href="/Playground/">Open Playground</a>
  <a class="hero-btn" href="/">Read the Book (25 Chapters)</a>
  <a class="hero-btn" href="https://github.com/TharkunAB/ghc/tree/dependent-haskell">GHC Fork</a>
  <a class="hero-btn" href="https://github.com/TharkunAB/dependent-proof-search">ProofSearch Plugin</a>
  <a class="hero-btn" href="https://github.com/TharkunAB/dependent-obs-eq">ObsEq Plugin</a>
</div>

[`TharkunAB/ghc`](https://github.com/TharkunAB/ghc/tree/dependent-haskell)
(branch `dependent-haskell`, tag `dependent-haskell-alpha`) adds full-spectrum
dependent types to GHC 10.1 under `-XDependentTypes`, keeping type erasure by
default, separate compilation, and compatibility with existing Haskell code.
Companion libraries and plugins live in
[`TharkunAB/dependent-base`](https://github.com/TharkunAB/dependent-base),
[`TharkunAB/dependent-proof-search`](https://github.com/TharkunAB/dependent-proof-search),
and [`TharkunAB/dependent-obs-eq`](https://github.com/TharkunAB/dependent-obs-eq).

Every code block below compiles and runs in your browser through WebAssembly
(`wasm32-wasi`). Click **Check in GHCi (Wasm)** on any example, or click
**Edit** and press **`Ctrl/Cmd+Enter`** to change the code and inspect types or
evaluate expressions at the `ghci>` prompt.

<div id="plfh-showcase-bar" class="plfh-chapter-bar plfh-showcase-sticky"></div>

::: {.plfh-showcase-act id="act-1" data-act-num="1" data-act-title="Routes & Stacks"}

### 1. Lead example: web routes as values and runtime monad stacks

In libraries such as Servant, HTTP routes live at the type level. That design
catches handler mismatches at compile time, but routes cannot sit in ordinary
lists or pass through plain functions. Every new interpretation needs its own
type class (`HasServer`, `HasClient`, `HasDocs`) plus `Proxy` and `KnownSymbol`
machinery.

With `-XDependentTypes`, a `Route` is an ordinary Haskell datatype and a
`RunMode` is an ordinary configuration value. In the module below, one route
definition (`apiRoute UserPost`) drives three things:

1. Documentation (`describeRoute`) is a three-line ordinary function.
2. URL construction (`buildLink (apiRoute UserPost)`) has the computed type
   `Int -> String -> String`, so passing arguments in the wrong order fails at
   compile time.
3. Request dispatch (`dispatch`) selects a `transformers` monad stack from
   `RunMode` using a type-level `case` (`Identity`, `WriterT [String] Identity`,
   or `StateT Int (WriterT [String] Identity)`), checks that the handler matches
   both the route and the stack, and returns the exact unwrapped result type.

#### 1.1 Type-safe routes and runtime monad stacks {#card-servant-stack}

<div class="showcase-credits">
  <strong>Features &amp; specs:</strong>
  <code>foreach</code> (<a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html">#378</a>) &middot;
  Type-level <code>case</code> (<a href="https://ghc.serokell.io/dh#type-level-case-expressions">R19</a>) &middot;
  Term-to-<code>Type</code> large elimination (<a href="https://ghc.serokell.io/dh#function-promotion">R13</a>) &middot;
  <code>transformers</code> (<code>Identity</code>, <code>WriterT</code>, <code>StateT</code>)
</div>

Click **Check in GHCi (Wasm)** and evaluate `demo` at the `ghci>` prompt, or
swap `Int` and `String` in `handleUserPost` to see GHC reject the mismatch.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns, TypeFamilies, UndecidableInstances #-}
module ShowcaseServantStack where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, modify', runStateT)
import Control.Monad.Trans.Writer.Strict (WriterT, runWriterT, tell)
import Data.Functor.Identity (Identity (runIdentity))
import Data.Kind (Type)
import Text.Read (readMaybe)

-- 1. Select a monad transformer stack from a runtime mode value (type-level case).
data RunMode = PureMode | LoggedMode | MeteredMode

type StackM (m :: RunMode) = case m of
  PureMode    -> Identity
  LoggedMode  -> WriterT [String] Identity
  MeteredMode -> StateT Int (WriterT [String] Identity)

type StackOut (m :: RunMode) a = case m of
  PureMode    -> a
  LoggedMode  -> (a, [String])
  MeteredMode -> ((a, Int), [String])

withStackMonad :: foreach (m :: RunMode) -> (Monad (StackM m) => a) -> a
withStackMonad PureMode    k = k
withStackMonad LoggedMode  k = k
withStackMonad MeteredMode k = k

runMode :: foreach (m :: RunMode) -> StackM m a -> StackOut m a
runMode PureMode    act = runIdentity act
runMode LoggedMode  act = runIdentity (runWriterT act)
runMode MeteredMode act = runIdentity (runWriterT (runStateT act 0))

recordHit :: foreach (m :: RunMode) -> String -> StackM m ()
recordHit PureMode    _   = pure ()
recordHit LoggedMode  msg = tell [msg]
recordHit MeteredMode msg = modify' (+ 1) >> lift (tell [msg])

-- 2. Define HTTP routes as ordinary Haskell values.
data WireTy = TInt | TString | TBool

interp :: WireTy -> Type
interp TInt    = type Int
interp TString = type String
interp TBool   = type Bool

data Seg  = Users | Posts | Health
data Part = Lit Seg | Cap WireTy

infixr 5 :>
data Route = Part :> Route | Get WireTy

data Endpoint = UserPost | HealthCheck

apiRoute :: Endpoint -> Route
apiRoute UserPost    = Lit Users :> Cap TInt :> Lit Posts :> Cap TString :> Get TBool
apiRoute HealthCheck = Lit Health :> Get TString

type family HandlerType (m :: RunMode) (r :: Route) :: Type where
  HandlerType m (Lit _  :> rest) = HandlerType m rest
  HandlerType m (Cap ty :> rest) = interp ty -> HandlerType m rest
  HandlerType m (Get res)        = StackM m (Either String (interp res))

type family LinkType (r :: Route) :: Type where
  LinkType (Lit _  :> rest) = LinkType rest
  LinkType (Cap ty :> rest) = interp ty -> LinkType rest
  LinkType (Get _)          = String

segPath :: Seg -> String
segPath Users  = "users"
segPath Posts  = "posts"
segPath Health = "health"

wireName :: WireTy -> String
wireName TInt    = "Int"
wireName TString = "String"
wireName TBool   = "Bool"

parseWire :: foreach (t :: WireTy) -> String -> Either String (interp t)
parseWire TInt    raw = maybe (Left ("400: bad Int " ++ raw)) Right (readMaybe raw)
parseWire TString raw = Right raw
parseWire TBool   raw = maybe (Left ("400: bad Bool " ++ raw)) Right (readMaybe raw)

renderWire :: foreach (t :: WireTy) -> interp t -> String
renderWire TInt    n = show n
renderWire TString s = s
renderWire TBool   b = show b

-- Docs: a three-line ordinary function over Route.
describeRoute :: Route -> String
describeRoute (Lit s  :> rest) = "/" ++ segPath s ++ describeRoute rest
describeRoute (Cap ty :> rest) = "/<" ++ wireName ty ++ ">" ++ describeRoute rest
describeRoute (Get res)        = " -> " ++ wireName res

-- Links: GHC computes `buildLink (apiRoute UserPost) :: Int -> String -> String`.
buildLink :: foreach (r :: Route) -> LinkType r
buildLink r = go r ""
  where
    go :: foreach (r' :: Route) -> String -> LinkType r'
    go (Lit s  :> rest) acc = go rest (acc ++ "/" ++ segPath s)
    go (Cap ty :> rest) acc = \val -> go rest (acc ++ "/" ++ renderWire ty val)
    go (Get _)          acc = acc

-- Dispatch: runs in whichever monad stack `m` selects at runtime.
dispatch :: foreach (m :: RunMode) -> foreach (r :: Route)
         -> HandlerType m r -> [String] -> StackOut m (Either String String)
dispatch m r handler path = withStackMonad m (runMode m (go r handler path))
  where
    go :: Monad (StackM m)
       => foreach (r' :: Route) -> HandlerType m r' -> [String] -> StackM m (Either String String)
    go (Lit s :> rest) h ps = case ps of
      (p : ps') | p == segPath s -> go rest h ps'
                | otherwise      -> pure (Left ("404: expected /" ++ segPath s))
      []                         -> pure (Left ("404: missing /" ++ segPath s))
    go (Cap ty :> rest) h ps = case ps of
      (p : ps') -> case parseWire ty p of
                     Left err  -> pure (Left err)
                     Right val -> go rest (h val) ps'
      []        -> pure (Left "404: missing segment")
    go (Get res) h ps = case ps of
      [] -> do
        out <- h
        pure (case out of { Left err -> Left err; Right val -> Right (renderWire res val) })
      _  -> pure (Left "404: trailing path")

-- One handler runs across PureMode, LoggedMode, and MeteredMode:
handleUserPost :: foreach (m :: RunMode) -> Int -> String -> StackM m (Either String Bool)
handleUserPost m uid slug = withStackMonad m (do
  recordHit m ("GET /users/" ++ show uid ++ "/posts/" ++ slug)
  pure (Right (uid > 0 && not (null slug))))

demo :: (String, String, Either String String, (Either String String, [String]), ((Either String String, Int), [String]))
demo =
  ( describeRoute (apiRoute UserPost)
  , buildLink (apiRoute UserPost) 42 "dependent-haskell"
  , dispatch PureMode    (apiRoute UserPost) (handleUserPost PureMode)    ["users", "42", "posts", "dependent-haskell"]
  , dispatch LoggedMode  (apiRoute UserPost) (handleUserPost LoggedMode)  ["users", "42", "posts", "dependent-haskell"]
  , dispatch MeteredMode (apiRoute UserPost) (handleUserPost MeteredMode) ["users", "42", "posts", "dependent-haskell"]
  )
```

:::

::: {.plfh-showcase-act id="act-2" data-act-num="2" data-act-title="Quantifiers & Data"}

### 2. Retained quantifiers, dependent pairs, and records

Standard Haskell has two function arrows: `forall (x :: a). b` passes `x` at
compile time and erases it before execution, while `a -> b` passes a runtime
value that cannot appear in `b`. Dependent Haskell adds a third quantifier,
`foreach (x :: a) -> b` (written `∏` under `-XUnicodeSyntax`), which retains
`x` at runtime and lets `b` mention `x`.

#### 2.1 Retained `foreach`, Peano arithmetic, and decimal numerals {#card-nat}

<div class="showcase-credits">
  <strong>Specs &amp; roadmap:</strong>
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#quantifiers">GHC Proposal #378 §4.4–4.5</a> &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0364-unify-natural.html">#364 Unify <code>Nat</code> &amp; <code>Natural</code></a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#dependent-products">R03</a>,
  <a href="https://ghc.serokell.io/dh#promote-literals">R07</a>,
  <a href="https://ghc.serokell.io/dh#promote-natural">R09</a>
</div>

When a function takes `foreach (m :: Nat) -> plus m Zero :~: m`, pattern
matching on `m` refines `m` inside the return type. In the `Zero` clause, GHC
reduces `plus Zero Zero` to `Zero`, so `Refl` checks directly. In the `Succ m`
clause, GHC reduces `plus (Succ m) Zero` to `Succ (plus m Zero)`, and the
recursive call proves the inner equality. Ordinary Peano functions (`plus`) and
decimal literals (`2 + 3`) work at both the term and type levels without a
separate `type family` or singleton copy.

```haskell
{-# LANGUAGE DependentTypes #-}
module ShowcaseNat where

import Data.Nat.Dependent (Nat (..), natToInt, plus, type (+))
import Data.Type.Equality.Dependent ((:~:) (Refl), cong)

-- Decimal numerals and (+) reduce directly at the type level:
twoPlusThree :: (2 + 3 :: Nat) :~: 5
twoPlusThree = Refl

-- Pattern matching on a retained `foreach` argument refines the return type:
plusIdentityR :: foreach (m :: Nat) -> plus m Zero :~: m
plusIdentityR Zero     = Refl
plusIdentityR (Succ m) = cong Succ (plusIdentityR m)

-- Multi-binder `foreach (m n p :: Nat)` quantifies three retained naturals at once:
plusAssoc :: foreach (m n p :: Nat) -> plus (plus m n) p :~: plus m (plus n p)
plusAssoc Zero     _ _ = Refl
plusAssoc (Succ m) n p = cong Succ (plusAssoc m n p)

five :: Int
five = natToInt (plus 2 3)
```

#### 2.2 Dependent pairs (`some` / `Sigma`) and `OverloadedRecordDot` {#card-sigma}

<div class="showcase-credits">
  <strong>Specs &amp; roadmap:</strong>
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#erasure">#378 §4.2 Predictable Erasure</a> &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0282-record-dot-syntax.html">#282 Record Dot Syntax</a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#dependent-sums">R04</a>
</div>

A dependent pair type `some (x :: a) | p x` (backed by `GHC.Sigma.Sigma`) pairs
a runtime value `x :: a` with a second value whose type `p x` mentions `x`. For
example, `EvenSigma 6 = some (k :: Nat) | plus k k :~: 6` packages the half `3`
together with the proof that `3 + 3 = 6`, and `SomeVec Char = some (n :: Nat) |
Vec Char n` packages a vector together with its runtime length.

Unlike erased `Exists` (shown in section 4.1), a `some` pair keeps its first
component at runtime. Callers can read `p.first` directly, and a function that
takes a retained pair (`foreach (p :: SomeVec a)`) can project `p.second` at
type `Vec a (first p)`.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns, OverloadedRecordDot, UndecidableInstances #-}
module ShowcaseSigma where

import Data.Nat.Dependent (Nat (..), natToInt, plus)
import Data.Sigma.Dependent (Sigma (Pair), first)
import Data.Type.Equality ((:~:) (Refl))
import Data.Vec.Dependent (SomeVec, Vec (..), toListVec)
import GHC.Sigma.Projection (second)

-- A dependent pair carrying a witness `k` and a proof that `k + k == n`:
type EvenSigma (n :: Nat) = some (k :: Nat) | plus k k :~: n

halfOfSix :: EvenSigma 6
halfOfSix = Pair 3 Refl

-- Matching `Pair k Refl` exposes both the runtime witness `k` and its equality:
extractHalf :: Int
extractHalf = case halfOfSix of
  Pair k Refl -> natToInt k

-- `SomeVec Char` is `some (n :: Nat) | Vec Char n`: length and payload stay paired.
packedChars :: SomeVec Char
packedChars = Pair 3 (VCons 'd' (VCons 'e' (VCons 'p' VNil)))

-- Because `p` is bound with `foreach`, `p.second` has the dependent type `Vec a (first p)`:
projectVec :: forall a. foreach (p :: SomeVec a) -> Vec a (first p)
projectVec p = p.second

sigmaDemo :: (Int, Int, String)
sigmaDemo = (extractHalf, natToInt packedChars.first, toListVec (projectVec packedChars))
```

#### 2.3 Dependent records and type-changing updates {#card-records}

<div class="showcase-credits">
  <strong>Specs &amp; roadmap:</strong>
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0282-record-dot-syntax.html">#282 Record Dot Syntax</a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#dependent-sums">R04</a>
</div>

Dependent records generalize `Sigma` to named fields: later fields can mention
earlier fields in their types (`rowItems :: Vec a rowLen`), projections work
with `.field`, and record updates can change a type parameter (`SizedRow Int`
to `SizedRow String`) while preserving the stored length `rowLen`.

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

-- Type-changing record update that keeps `rowLen` intact:
mapRow :: (a -> b) -> SizedRow a -> SizedRow b
mapRow f r = r { rowItems = mapVec f (rowItems r) }

shownRow :: SizedRow String
shownRow = mapRow (show . (* 2)) initialRow

rowSummary :: (Int, [String])
rowSummary = (natToInt shownRow.rowLen, toListVec shownRow.rowItems)
```

#### 2.4 Runtime `Type` pattern matching (`foreach (a :: Type)`) {#card-typecase}

<div class="showcase-credits">
  <strong>Specs &amp; roadmap:</strong>
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#phase-distinction">#378 §4.9 Phase Distinction</a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#dependent-products">R03</a>,
  <a href="https://ghc.serokell.io/dh#type-level-case-expressions">R19</a>
</div>

A `foreach (a :: Type)` argument retains a type representation at runtime.
Matching on `a` with an ordinary `case` refines `a` in each branch, so
`defaultVal` returns `Just 42 :: Maybe Int` or `Just "dependent haskell" ::
Maybe String` without `Typeable` casts.

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

#### 2.5 Linear `foreach` binders (`foreach (x %1 :: a)`) {#card-linear}

<div class="showcase-credits">
  <strong>Specs &amp; roadmap:</strong>
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0111-linear-types.html">#111 Linear Types</a> &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#quantifiers">#378 §4.4</a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#dependent-products">R03</a>,
  <a href="https://ghc.serokell.io/dh#dependent-core-language">R05</a>
</div>

Dependent `foreach` binders combine with `-XLinearTypes`. A linear retained
argument (`%1`) must be consumed once at runtime, while appearing freely in
erased type indices.

```haskell
{-# LANGUAGE DependentTypes, LinearTypes, ListTuplePuns #-}
module ShowcaseLinearForEach where

import Data.Nat.Dependent (Nat (..), natToInt)

data SingBool (b :: Bool) where
  STrue  :: SingBool True
  SFalse :: SingBool False

data SamePair (m :: Nat) (n :: Nat) = SamePair

-- Consume `b` linearly at runtime while refining the result type `SingBool b`:
linearSingBool :: foreach (b %1 :: Bool) -> SingBool b
linearSingBool True  = STrue
linearSingBool False = SFalse

-- `n` appears twice in the erased index `SamePair n n`, and once at runtime:
dupInTypeLinear :: foreach (n %1 :: Nat) -> SamePair n n -> Nat
dupInTypeLinear n SamePair = n

linearDemo :: (Bool, Int)
linearDemo =
  let bOk = case linearSingBool True of STrue -> True
      nOk = natToInt (dupInTypeLinear (Succ Zero) SamePair)
  in (bOk, nOk)
```

#### 2.6 Off-diagonal GADT refutation (`zipEqualVec`) {#card-refute}

<div class="showcase-credits">
  <strong>Specs &amp; roadmap:</strong>
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#dependent-pattern-match">#378 §4.5</a> &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0402-gadt-syntax.html">#402 GADT Syntax</a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#homogeneous-equality">R11</a>,
  <a href="https://ghc.serokell.io/dh#nested-quantification-in-gadts">R41</a>
</div>

When two retained lengths `m` and `n` are tied by `m :~: n`, GHC's pattern
match checker refutes the off-diagonal `Zero`/`Succ` and `Succ`/`Zero` cases.
Only the two diagonal equations need to be written.

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

::: {.plfh-showcase-act id="act-3" data-act-num="3" data-act-title="Types as Code"}

### 3. Term promotion, type-level expressions, and matchability

This section covers the type-level language added by the fork: open evaluation
of ordinary functions, inline `case` and `let` inside types, local `type`
synonyms inside term `let`/`where` blocks, type-level lambdas, and explicit
matchability (`%M` / `%U` / `%m`).

#### 3.1 Stock `Prelude` lists and open function evaluation {#card-lists}

<div class="showcase-credits">
  <strong>Specs &amp; roadmap:</strong>
  <a href="https://github.com/ghc-proposals/ghc-proposals/pull/509">#509 Type-Level Functions</a> &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0475-tuple-syntax.html">#475 Non-Punning List &amp; Tuple Syntax</a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#function-promotion">R13</a>,
  <a href="https://ghc.serokell.io/dh#open-term-evaluator">R16</a>,
  <a href="https://ghc.serokell.io/dh#no-list-or-tuple-puns">R38</a>
</div>

Ordinary functions on `Prelude` lists (`(++)`, `map`, `Data.List.Dependent.size`)
publish checked source equations in `.hi` interfaces and reduce symbolically
over unknown `foreach` variables. Under `NoListTuplePuns` (implied by
`-XDependentTypes`), `[]` and `:` work directly in types without promotion
ticks.

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

#### 3.2 Type-level `case`, type-level `let`, and local `type` synonyms {#card-type-case-let}

<div class="showcase-credits">
  <strong>Specs &amp; roadmap:</strong>
  <a href="https://github.com/ghc-proposals/ghc-proposals/pull/523">#523 Extended <code>let</code></a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#type-level-let-bindings">R18 Type-level lets</a>,
  <a href="https://ghc.serokell.io/dh#type-level-case-expressions">R19 Type-level cases</a>,
  <a href="https://ghc.serokell.io/dh#dependency-analysis">R21</a>
</div>

Type expressions support inline `case` matching (`case isNumeric of True ->
Int; False -> String`) and ordered `let` bindings (`let slot = Maybe a in
(slot, Either String slot)`). Inside term `let` and `where` blocks, non-recursive
local `type` synonyms can capture retained `foreach` variables in scope.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module ShowcaseTypeCaseLet where

import Data.Nat.Dependent (Nat (..))
import Data.Vec.Dependent (Vec (..))

-- 1. Type-level `case`: branch on a promoted value directly inside a type.
type FieldType (isNumeric :: Bool) = case isNumeric of
  True  -> Int
  False -> String

defaultField :: foreach (isNumeric :: Bool) -> FieldType isNumeric
defaultField True  = 42
defaultField False = "default"

-- 2. Type-level `let`: name an intermediate type and reuse it in the result.
type SyncedPair a =
  let slot = Maybe a
  in (slot, Either String slot)

sampleSynced :: SyncedPair Int
sampleSynced = (Just 7, Right (Just 7))

-- 3. Local `type` synonyms inside term `let` / `where` blocks (#523),
--    capturing the retained `foreach` variable `n`.
localTypeSynDemo :: (Int, String, SyncedPair Int, Int)
localTypeSynDemo =
  let type PairOf a = (a, a)
      p :: PairOf Int
      p = (20, 22)
  in (defaultField True, defaultField False, sampleSynced, addPair (Succ Zero) p)
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

#### 3.3 Type-level lambdas and explicit matchability (`%M`, `%U`, `%m`) {#card-type-lambda}

<div class="showcase-credits">
  <strong>Specs &amp; roadmap:</strong>
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0242-unsaturated-type-families.html">#242 Unsaturated Type Families</a>
  (Kiss et al., <a href="https://doi.org/10.1145/3341706">ICFP 2019</a>) &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0281-visible-forall.html">#281 Visible <code>forall</code></a> &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0370-modifiers.html">#370 Modifiers</a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#type-level-lambdas">R17</a>,
  <a href="https://ghc.serokell.io/dh#unsaturated-type-families">R23</a>
</div>

GHC distinguishes two kinds of type-level arrows. A **matchable** arrow (`a %M
-> b`) is injective and generative, such as a type or data constructor (`Maybe`,
`Succ`): if `f x ~ f y`, GHC can conclude `x ~ y`. An **unmatchable** arrow
(`a %U -> b`) allows arbitrary computation, including type-level lambdas (`\f
-> f Int`) and partially applied promoted functions (`plus 1`), where `f x ~ f
y` does not imply `x ~ y`. Polymorphic arrows (`a %m -> b`) accept both: a
single `cong` works on `%M` constructors (`Succ`), `%U` partial applications
(`plus m`), and operator sections (`(x :)`, `(: ys)`).

```haskell
{-# LANGUAGE DependentTypes, TypeFamilies #-}
module ShowcaseTypeLambdaMatch where

import Data.Kind (Type)
import Data.Nat.Dependent (Nat (..), plus)
import Data.Type.Equality.Dependent ((:~:) (Refl), cong)
import GHC.Matchability (M, U)
import GHC.Types (List)

-- `%U` (unmatchable): accepts type-level lambdas and promoted functions.
type family MapT (f :: a %U -> b) (xs :: List a) :: List b where
  MapT _ []       = []
  MapT f (x : xs) = f x : MapT f xs

-- Inline type-level lambda (`\f -> f Int`) mapped over a list of type constructors:
type AppliedToInt = MapT (\f -> f Int) [Maybe, Either String, IO]

appliedProof :: AppliedToInt :~: [Maybe Int, Either String Int, IO Int]
appliedProof = Refl

-- Partially applied promoted arithmetic (`plus 1`) passed directly to `MapT`:
type Incremented = MapT (plus 1) [Zero, Succ Zero, Succ (Succ Zero)]

incProof :: Incremented :~: [Succ Zero, Succ (Succ Zero), Succ (Succ (Succ Zero))]
incProof = Refl

-- `%M` (matchable): accepts injective constructors such as `Maybe`,
-- and rejects unmatchable lambdas such as `(\a -> Either String a)`.
data BoxM (f :: Type %M -> Type) (a :: Type) = MkBoxM (f a)

boxedMaybe :: BoxM Maybe Int
boxedMaybe = MkBoxM (Just 42)

-- Matchability-polymorphic `cong` (`forall (f :: a %m -> b) -> ...`) handles
-- `%M` constructors, `%U` promoted functions, and operator sections uniformly:
congMatchable :: forall (m n :: Nat). m :~: n -> Succ m :~: Succ n
congMatchable eq = cong Succ eq

congUnmatchable :: forall (n p :: Nat). foreach (m :: Nat)
                -> n :~: p -> plus m n :~: plus m p
congUnmatchable m eq = cong (plus m) eq

congConsLeft :: forall a (x :: a) (ys1 ys2 :: List a).
                ys1 :~: ys2 -> (x : ys1) :~: (x : ys2)
congConsLeft eq = cong (x :) eq

congConsRight :: forall a (x1 x2 :: a) (ys :: List a).
                 x1 :~: x2 -> (x1 : ys) :~: (x2 : ys)
congConsRight eq = cong (: ys) eq
```

#### 3.4 Type-safe `printf` via `foreach` {#card-printf}

<div class="showcase-credits">
  <strong>Specs &amp; roadmap:</strong>
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#dependent-application-and-the-static-subset">#378 §4.7 Dependent Application</a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#closed-term-evaluator">R15</a>,
  <a href="https://ghc.serokell.io/dh#dependency-analysis">R21</a>
</div>

A format descriptor value (`Fmt`) determines both the arity and argument types
of `printf`. For `Lit "Hello " (S (Lit ", " (D (Lit " chapters checked!" End))))`,
GHC computes the curried type `String -> Int -> String` and rejects arguments of
the wrong type or count at compile time.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns, TypeFamilies #-}
module ShowcasePrintf where

import Data.Kind (Type)

data Fmt
  = End
  | Lit String Fmt
  | D Fmt
  | S Fmt

type family FmtType (f :: Fmt) :: Type where
  FmtType End       = String
  FmtType (Lit _ r) = FmtType r
  FmtType (D r)     = Int -> FmtType r
  FmtType (S r)     = String -> FmtType r

printf :: foreach (f :: Fmt) -> FmtType f
printf f = go f ""
  where
    go :: foreach (f' :: Fmt) -> String -> FmtType f'
    go End       acc = acc
    go (Lit s r) acc = go r (acc ++ s)
    go (D r)     acc = \n -> go r (acc ++ show n)
    go (S r)     acc = \s -> go r (acc ++ s)

-- GHC checks that `"Matti" :: String` and `25 :: Int` match `S` followed by `D`:
greeting :: String
greeting = printf (Lit "Hello " (S (Lit ", " (D (Lit " chapters checked!" End))))) "Matti" 25
```

:::

::: {.plfh-showcase-act id="act-4" data-act-num="4" data-act-title="Exists & Base"}

### 4. Erased existentials and `dependent-base`

[`TharkunAB/dependent-base`](https://github.com/TharkunAB/dependent-base)
(documented in the [`dependent-base` Reference](/DependentBase/)) builds a
standard library directly on stock `Prelude` types (`Bool`, `Maybe`, `Either`,
`(,)`, `[a]`, `(:~:)`, `Void`) and compiles `.hi` interfaces that ordinary
`Haskell2010` modules can import without enabling `-XDependentTypes`.

#### 4.1 Erased existentials (`GHC.Exists` & `Data.Exists.Dependent`) {#card-exists}

<div class="showcase-credits">
  <strong>Specs &amp; roadmap:</strong>
  <a href="https://github.com/ghc-proposals/ghc-proposals/pull/473">#473 Existential Types</a> &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0581-namespace-specified-imports.html">#581 Namespace-Specified Imports</a> &middot;
  Serokell <a href="https://ghc.serokell.io/dh#existential-quantification">R22</a>,
  <a href="https://ghc.serokell.io/dh#namespace-management">R35</a>
</div>

Proposal `#473` separates retained dependent pairs (`some` / `Sigma`) from
erased existential packages (`Exists p = exists x | p x`). In an `Exists`
package, the hidden witness is erased before runtime: callers can use a packed
type-class dictionary (`Show a /\ a`) or apply a polymorphic transformation
(`mapExists`), but cannot branch on the hidden type or read a runtime length
tag.

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

-- Pack a value together with its `Show` dictionary under an erased type `a`.
-- At runtime only the dictionary and value exist; the type `a` is erased.
newtype ShowEntry a = ShowEntry (Show a /\ a)
newtype AnyShow = AnyShow (Exists ShowEntry)

packShow :: forall a. Show a => a -> AnyShow
packShow x = AnyShow (Pack (type a) (ShowEntry (MkCPair x)))

renderShow :: AnyShow -> String
renderShow (AnyShow item) =
  withExists item (\_ (ShowEntry paired) -> withEvidence paired show)

-- Compare erased `Exists (Vec Char)` with retained `SomeVec Char` (`Sigma`):
-- the length `2` is erased at runtime, yet `mapExists` still transforms the vector.
hiddenWord :: Exists (Vec Char)
hiddenWord = Pack (type (Succ (Succ Zero))) (VCons 'o' (VCons 'k' VNil))

shoutWord :: Exists (Vec Char)
shoutWord = mapExists (\_ xs -> mapVec toUpper xs) hiddenWord

existsDemo :: ([String], String, Bool)
existsDemo =
  let items = [packShow (42 :: Int), packShow True, packShow "haskell"]
      witOk = case Witness @Nat of Witness -> True
  in (map renderShow items, withExists shoutWord (\_ xs -> toListVec xs), witOk)
```

#### 4.2 First-class dependent composition `(.)` {#card-dep-compose}

<div class="showcase-credits">
  <strong>Package:</strong>
  <a href="https://github.com/TharkunAB/dependent-base"><code>TharkunAB/dependent-base</code></a> &middot;
  <a href="/DependentBase/#datafunctiondependent"><code>Data.Function.Dependent</code></a>
</div>

`Data.Function.Dependent.(.)` generalizes `Prelude.(.)` to dependent consumers
whose return type mentions `f x`. The same `(.)` composes equality proofs
(`plusZero . Succ`), indexed vector producers (`(.) zeros (plus 1)`), functions
passed to `cong` (`cong (Succ . plus m)`), and ordinary `Int -> Int` functions.

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

-- Dependent vector producer composed with ordinary arithmetic:
zerosPlus1 :: foreach (n :: Nat) -> Vec Nat (plus 1 n)
zerosPlus1 = (.) zeros (plus 1)

-- Dependent equality proof composed directly with `Succ`:
plusIdSucc :: foreach (n :: Nat) -> plus (Succ n) Zero :~: Succ n
plusIdSucc = plusZero . Succ

-- Composed function passed directly to matchability-polymorphic `cong`:
congSuccPlus :: foreach (m :: Nat)
             -> forall (x y :: Nat). x :~: y -> Succ (plus m x) :~: Succ (plus m y)
congSuccPlus m eq = cong (Succ . plus m) eq

-- Ordinary non-dependent composition uses the same `(.)`:
ordinaryCompose :: (Int -> Int) -> (Int -> Int) -> Int -> Int
ordinaryCompose g f = g . f

composeDemo :: ([Int], Int)
composeDemo = (map natToInt (toListVec (zerosPlus1 2)), ordinaryCompose (* 2) (+ 1) 20)
```

#### 4.3 Length-indexed `Vec` and bounded `Fin` indexing {#card-vec-fin}

<div class="showcase-credits">
  <strong>Package:</strong>
  <a href="https://github.com/TharkunAB/dependent-base"><code>TharkunAB/dependent-base</code></a> &middot;
  <a href="/DependentBase/#datavecdependent"><code>Data.Vec.Dependent</code></a> &middot;
  <a href="/DependentBase/#datafindependent"><code>Data.Fin.Dependent</code></a>
</div>

`Data.Vec.Dependent` and `Data.Fin.Dependent` pair length-checked operations
(`appendVec`, `zipVec`, total `lookupVec`) with runtime list conversions
(`packListVec`, `toListVec`). `Fin` currently names its constructors `FZ` and
`FS` so `Prelude.Dependent` can export `Nat (Zero, Succ)` and `Fin (FZ, FS)`
unqualified together, without a partial `Num` instance.

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

::: {.plfh-showcase-act id="act-5" data-act-num="5" data-act-title="Plugins & Holes"}

### 5. Interactive Agda-mode and compiler plugins

Proof search and observational equality are external GHC plugins. GHC's core
solver and `GHC.Tc.Errors.Hole` stay general, and both plugins are statically
linked into the browser WebAssembly build so you can run them here.

#### 5.1 Typed holes, case splits, and `Dependent.Plugin.ProofSearch` {#card-agda-mode}

<div class="showcase-credits">
  <strong>Plugin &amp; paper:</strong>
  <a href="https://github.com/TharkunAB/dependent-proof-search"><code>TharkunAB/dependent-proof-search</code></a>
  (<code>-fplugin=Dependent.Plugin.ProofSearch</code>) &middot;
  Matth&iacute;as P&aacute;ll Gissurarson,
  <a href="https://doi.org/10.1145/3242744.3242760"><em>Suggesting Valid Hole Fits for Typed-Holes in Haskell</em></a>
  (Haskell 2018)
</div>

Click **Check in GHCi (Wasm)** below. GHC marks `_` in a green goal box,
suggests splitting on `m` to unblock `plus`, and uses
`Dependent.Plugin.ProofSearch` to suggest both step-by-step subgoal refinements
(`cong Succ _`) and direct synthesis (`cong Succ (plusAssoc m n p)`).

```{.haskell data-showcase-hole="1"}
{-# LANGUAGE DependentTypes #-}
module ShowcaseAgdaMode where

import Data.Nat.Dependent (Nat (..), plus)
import Data.Type.Equality.Dependent ((:~:) (Refl), cong)

-- Solve in 3 clicks:
-- 1. Check in GHCi (Wasm) -> click "Split on m (Zero | Succ)"
-- 2. Click "Refl" for the Zero branch
-- 3. Click "cong Succ (plusAssoc m n p)" (or refine via "cong Succ _")
plusAssoc :: foreach (m n p :: Nat)
          -> plus (plus m n) p :~: plus m (plus n p)
plusAssoc m n p = _
```

#### 5.2 Observational equality with `Dependent.Plugin.ObsEq` {#card-obs-eq}

<div class="showcase-credits">
  <strong>Plugin &amp; credit:</strong>
  <a href="https://github.com/TharkunAB/dependent-obs-eq"><code>TharkunAB/dependent-obs-eq</code></a>
  (<code>-fplugin=Dependent.Plugin.ObsEq</code>) &middot;
  Idea by <strong>Jules (<code>@analytichegel</code>)</strong> &middot;
  Uninterpreted open calls (<code>U:f</code>) + GHC <code>TcPlugin</code>
</div>

Non-structural, accumulator-based, or fuel-free functions such as `unfoldPlus`,
`accPlus`, and `collatz` do not have structural source equations in GHC's core
conversion. When `Dependent.Plugin.ObsEq` is enabled, GHC elaborates open calls
into uninterpreted families (`U:f`) and the plugin tests observational
equalities in-process over total and partial (`ObsBottom`) inputs. Explicit
combinators (`obsEq`, `obsEqWith`, `obsEqGen`) discharge passing witnesses while
keeping bare `Refl` strict.

Click **Edit**, change `go Zero acc = acc` to `go Zero acc = Succ acc`, and
press **`Ctrl/Cmd+Enter`** to watch the plugin refute `accPlusCorrect` with a
shrunk counterexample (`m = Zero, n = Zero`).

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

-- 1. Non-structural unfold addition (equivalent to `plus` on partial inputs too).
unfoldPlus :: Nat -> Nat -> Nat
unfoldPlus m n = step (Just m) n
  where
    step Nothing acc         = acc
    step (Just Zero) acc     = step Nothing acc
    step (Just (Succ k)) acc = Succ (step (Just k) acc)

-- 2. Tail-recursive accumulator addition (total-domain equivalent to `plus`).
-- Break `go Zero acc = acc` to `go Zero acc = Succ acc` to see counterexample shrinking.
accPlus :: Nat -> Nat -> Nat
accPlus m n = go m n
  where
    go Zero acc     = acc
    go (Succ k) acc = go k (Succ acc)

-- 3. Fuel-free Collatz convergence on total Nats.
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

-- 4. Domain-restricted law on even Ints via a custom generator (`obsEqGen`).
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

-- Transport a length-indexed `Vec` across an observational witness at runtime:
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

## Repositories and design choices

| Repository | Role |
| --- | --- |
| [`TharkunAB/ghc`](https://github.com/TharkunAB/ghc/tree/dependent-haskell) | GHC 10.1 fork implementing `-XDependentTypes`, native dependent Core (`DepFunTy`, `TermVarTy`, `ExistsTy`), and the open cards of the [Serokell roadmap](https://ghc.serokell.io/dh) ([`ROADMAP.md`](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/ROADMAP.md)) |
| [`TharkunAB/dependent-base`](https://github.com/TharkunAB/dependent-base) | Standard library (`Prelude.Dependent`, `Data.Function.Dependent`, `Data.{Nat,List,Vec,Fin,Sigma,Exists,Decision,...}.Dependent`); see the [API reference](/DependentBase/) |
| [`TharkunAB/dependent-proof-search`](https://github.com/TharkunAB/dependent-proof-search) | `HoleFitPlugin` (`-fplugin=Dependent.Plugin.ProofSearch`) for congruence/transitivity subgoal refinements and bounded proof synthesis |
| [`TharkunAB/dependent-obs-eq`](https://github.com/TharkunAB/dependent-obs-eq) | `TcPlugin` (`-fplugin=Dependent.Plugin.ObsEq`, idea by Jules `@analytichegel`) for QuickCheck observational-equality testing and counterexample shrinking |
| [`TharkunAB/PLFH`](https://github.com/TharkunAB/PLFH) | This 25-chapter interactive textbook adapted from PLFA ([Table of Contents](/), [Coverage](/Status/), [Setup](/Setup/)) |

<div class="showcase-decisions">
  <div class="decision-card">
    <h3>1. Specification hierarchy</h3>
    <p>Syntax, flags, and typing rules follow
    <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html">GHC Proposal #378</a>
    first, companion GHC proposals second, the Serokell roadmap for scope tracking,
    and Agda/PLFA for surface syntax and conventions where proposals are silent.</p>
  </div>
  <div class="decision-card">
    <h3>2. Opt-in extension and <code>Haskell2010</code> interop</h3>
    <p>Existing Haskell code compiles unchanged. One pragma (<code>-XDependentTypes</code>)
    enables retained binders, function promotion, and <code>NoListTuplePuns</code>.
    Plain <code>Haskell2010</code> modules can import compiled <code>.hi</code> interfaces from
    <code>dependent-base</code> without enabling dependent extensions.</p>
  </div>
  <div class="decision-card">
    <h3>3. Type safety without forced totality</h3>
    <p>Following Weirich et al. (ICFP 2017), System FC remains type-safe even with
    general recursion and non-termination. Structural totality diagnostics are opt-in
    (<code>-freport-totality</code>), while proof search and observational equality
    live in external GHC plugins.</p>
  </div>
  <div class="decision-card">
    <h3>4. Deliberate compatibility boundaries</h3>
    <p>Three boundaries stay fixed for Haskell compatibility: <code>Haskell98</code>
    and <code>Haskell2010</code> keep <code>CUSKs</code> by default (while
    <code>-XDependentTypes</code> implies <code>NoCUSKs</code>); internal
    <code>HsExpr</code> and <code>HsType</code> ASTs remain separate with bare
    <code>a -&gt; b</code> in patterns kept for <code>ViewPatterns</code>; effectful
    <code>IO</code> and uncertified non-structural functions stay outside built-in
    type conversion (<code>#378 §4.10</code>).</p>
  </div>
</div>

## GHC proposals and research papers

| Proposal | Title | Role |
| --- | --- | --- |
| [`#378`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html) | *Design for Dependent Types* | `-XDependentTypes` bundle, lexical scoping across terms and types, `foreach` / `forall` / `some` / `exists` / `∏` |
| [`#281`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0281-visible-forall.html) | *Visible `forall` in types of terms* | `RequiredTypeArguments` (`forall a ->`), enabling visible `cong Succ` and `cong (plus m)` |
| [`#242`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0242-unsaturated-type-families.html) | *Unsaturated Type Families* | Matchable and unmatchable arrows (`%M` / `%U`) and partial application of type-level functions |
| [`#370`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0370-modifiers.html) | *Syntax for Modifiers* | `%` modifier syntax for matchability and linearity annotations |
| [`#402`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0402-gadt-syntax.html) | *GADT Constructor Syntax* | Nested quantification and free ordering of `forall` groups and constraints in GADT constructors |
| [`#425`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0425-decl-invis-binders.html) | *Invisible Binders in Type Declarations* | Arity inference and invisible binder scoping in type and data declarations |
| [`#473`](https://github.com/ghc-proposals/ghc-proposals/pull/473) | *Existential Types* | Erased existential quantification (`Exists`, `Pack`, `(/\)`) |
| [`#475`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0475-tuple-syntax.html) | *Non-punning List & Tuple Syntax* | `NoListTuplePuns` so `[]` and `:` work in types without leading ticks |
| [`#364`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0364-unify-natural.html) | *Unify `Nat` and `Natural`* | Type-level natural literals paired with `FromNatural` |
| [`#509`](https://github.com/ghc-proposals/ghc-proposals/pull/509) & [`#523`](https://github.com/ghc-proposals/ghc-proposals/pull/523) | *Type-Level Functions* & *Extended `let`* | Promoting ordinary functions across `.hi` interfaces and local `type` synonyms in `let`/`where` |
| [`#581`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0581-namespace-specified-imports.html) & [`#765`](https://ghc-proposals.readthedocs.io/en/latest/proposals/0765-pun-warnings.html) | *Namespace-Specified Imports* & *Pun Warnings* | Disambiguating `type (+)` and `data Pack` across imports and diagnosing puns |

### Foundational literature

- **Adam Gundry (2013).** *Type Inference, Haskell and Dependent Types.* PhD
  thesis, University of Strathclyde.
- **Richard A. Eisenberg (2016).** *Dependent Types in Haskell: Theory and
  Practice.* PhD dissertation, University of Pennsylvania
  ([`arXiv:1610.07978`](https://arxiv.org/abs/1610.07978)).
- **Stephanie Weirich, Antoine Voizard, Pedro Henrique Azevedo de Amorim, and
  Richard A. Eisenberg (ICFP 2017).** *A Specification for Dependent Types in
  Haskell.* PACMPL 1(ICFP):31:1–31:29
  ([DOI `10.1145/3110275`](https://doi.org/10.1145/3110275)).
- **Stephanie Weirich, Pritam Choudhury, Antoine Voizard, and Richard A.
  Eisenberg (ICFP 2019).** *A Role for Dependent Types in Haskell.* PACMPL
  3(ICFP):101:1–101:29
  ([DOI `10.1145/3341705`](https://doi.org/10.1145/3341705)).
- **Csongor Kiss, Tony Field, Susan Eisenbach, and Simon Peyton Jones (ICFP
  2019).** *Higher-Order Type-Level Programming in Haskell.* PACMPL
  3(ICFP):102:1–102:26
  ([DOI `10.1145/3341706`](https://doi.org/10.1145/3341706)).
- **Matthías Páll Gissurarson (Haskell 2018).** *Suggesting Valid Hole Fits for
  Typed-Holes in Haskell.* Haskell Symposium, pp. 179–185
  ([DOI `10.1145/3242744.3242760`](https://doi.org/10.1145/3242744.3242760)).
- **Philip Wadler, Wen Kokke, and Jeremy G. Siek.** *Programming Language
  Foundations in Agda* ([`plfa.inf.ed.ac.uk`](https://plfa.inf.ed.ac.uk/), CC
  BY 4.0).
