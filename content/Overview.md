---
title: "Dependent Haskell in GHC"
description: "Full-spectrum dependent types in GHC 10.1 (-XDependentTypes): type-safe web routes as values, runtime monad stacks, type-level case and lambdas, linear protocols, Agda-mode holes, and a 25-chapter textbook running live in WebAssembly."
prev: /
next: /Playground/
src: content/Overview.md
playground: true
---

`-XDependentTypes` adds full-spectrum dependent types to GHC 10.1
([`TharkunAB/ghc`](https://github.com/TharkunAB/ghc/tree/dependent-haskell)).
Ordinary Haskell datatypes and functions compute inside types directly, while
keeping type erasure by default, separate compilation, and full compatibility
with existing Haskell code.

<div class="hero-actions">
  <a class="hero-btn hero-btn--primary" href="/Playground/">Open Playground</a>
  <a class="hero-btn" href="/">Read the Book (25 Chapters)</a>
  <a class="hero-btn" href="https://github.com/TharkunAB/ghc/tree/dependent-haskell">GHC Fork</a>
  <a class="hero-btn" href="https://github.com/TharkunAB/dependent-proof-search">ProofSearch</a>
  <a class="hero-btn" href="https://github.com/TharkunAB/dependent-obs-eq">ObsEq</a>
</div>

Every module on this page compiles and runs in your browser through WebAssembly
(`wasm32-wasi`). Click **Check in GHCi (Wasm)** on any block, or click **Edit**
and press **`Ctrl/Cmd+Enter`** to change the code and inspect types or evaluate
expressions at the `ghci>` prompt.

:::::: {.plfh-walkthrough-scope}

<div id="plfh-showcase-bar" class="plfh-chapter-bar plfh-showcase-sticky"></div>

::::: {.plfh-showcase-act id="act-1" data-act-num="1" data-act-title="By Domain"}

## 1. Real-world Haskell, by domain

Standard Haskell separates compile-time type arguments (`forall a. b` and
`forall a -> b`, erased at runtime) from runtime value arguments (`a -> b`,
invisible to types). `-XDependentTypes` completes the grid with three dependent
quantifiers: retained **`foreach (x :: a) -> b`** (and invisible
`foreach (x :: a). b`) for dependent functions, retained **`some (x :: a) | b`**
for dependent pairs, and erased **`exists (x :: a) | b`** (Proposal `#473`) for
erased existentials.

Pick a domain below to see what disappears when types can inspect ordinary
Haskell values directly. Every tab compiles and runs in your browser through
WebAssembly, and **Check Part 1 (8 modules)** above verifies all eight tabs
together.

:::: {.plfh-domain-tabs id="domain-showcase"}

::: {.plfh-domain-tab id="tab-routes" data-tab-label="Web & Effects" data-tab-audience="Servant / transformers"}

### 1.1 Web routes as values and runtime monad stacks {#card-servant-stack}

<div class="showcase-credits">
  <strong>Replaces:</strong> <code>Servant</code> <code>HasServer</code>/<code>HasClient</code>/<code>HasDocs</code>, <code>Proxy</code>, <code>KnownSymbol</code> &middot;
  <strong>Features:</strong> <code>foreach</code> (<a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html">#378</a>) &middot;
  Type-level <code>case</code> &amp; lambdas (<a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0242-unsaturated-type-families.html">#242</a>) &middot;
  <code>transformers</code>
</div>

One `Route` value drives three things without type-class boilerplate:
documentation (`describeRoute`) is a three-line function, URL construction
(`buildLink (apiRoute UserPost)`) has computed type `Int -> String -> String`,
and `dispatch` selects a `transformers` monad stack (`Identity`, `WriterT`, or
`StateT`) from `RunMode` at runtime. Click **Check in GHCi (Wasm)** and run
`demo`, or swap `Int` and `String` in `handleUserPost` to trigger a compile
error.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns, TypeFamilies, UndecidableInstances #-}
module RoutesAndEffects where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, modify', runStateT)
import Control.Monad.Trans.Writer.Strict (WriterT, runWriterT, tell)
import Data.Functor.Identity (Identity (runIdentity))
import Data.Kind (Type)
import GHC.Matchability (U)
import Text.Read (readMaybe)

-- 1. Select a monad transformer stack from a runtime value (type-level case).
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

-- 2. Define HTTP routes as ordinary values.
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

-- 3. Higher-order fold + type-level lambdas derive both handler and link types.
type family RouteType (ret :: WireTy %U -> Type) (r :: Route) :: Type where
  RouteType ret (Lit _  :> rest) = RouteType ret rest
  RouteType ret (Cap ty :> rest) = interp ty -> RouteType ret rest
  RouteType ret (Get res)        = ret res

type HandlerRet (m :: RunMode) = \res -> StackM m (Either String (interp res))
type LinkRet                   = \res -> String

type HandlerType m r = RouteType (HandlerRet m) r
type LinkType      r = RouteType LinkRet r

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
       => foreach (r' :: Route) -> HandlerType m r' -> [String]
       -> StackM m (Either String String)
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
        pure (case out of
          Left err  -> Left err
          Right val -> Right (renderWire res val))
      _  -> pure (Left "404: trailing path")

-- One handler runs across PureMode, LoggedMode, and MeteredMode:
handleUserPost :: foreach (m :: RunMode) -> Int -> String -> StackM m (Either String Bool)
handleUserPost m uid slug = withStackMonad m (do
  recordHit m ("GET /users/" ++ show uid ++ "/posts/" ++ slug)
  pure (Right (uid > 0 && not (null slug))))

type DemoOut =
  ( String
  , String
  , Either String String
  , (Either String String, [String])
  , ((Either String String, Int), [String])
  )

demo :: DemoOut
demo =
  ( describeRoute (apiRoute UserPost)
  , buildLink (apiRoute UserPost) 42 "dependent-haskell"
  , dispatch PureMode    (apiRoute UserPost) (handleUserPost PureMode)    req
  , dispatch LoggedMode  (apiRoute UserPost) (handleUserPost LoggedMode)  req
  , dispatch MeteredMode (apiRoute UserPost) (handleUserPost MeteredMode) req
  )
  where
    req = ["users", "42", "posts", "dependent-haskell"]
```

:::

::: {.plfh-domain-tab id="tab-sql" data-tab-label="Typed SQL" data-tab-audience="squeal / beam / vinyl"}

### 1.2 Typed SQL schemas, DDL, and `JOIN` without `TypeFamilies` {#card-typed-sql}

<div class="showcase-credits">
  <strong>Replaces:</strong> <code>squeal</code> / <code>beam</code> / <code>vinyl</code> / <code>Frames</code> (<code>KnownSymbol</code>, <code>NP</code>, <code>OverloadedLabels</code>, TH) &middot;
  <strong>Features:</strong> Term-to-<code>Type</code> large elimination &middot; Promoted Prelude <code>(++)</code> &middot; <code>foreach</code>
</div>

One ordinary `List Col` value drives `CREATE TABLE` DDL (`createTableDDL`),
compile-time checked column projection (`getCol`), and `INNER JOIN`
(`joinRow` concatenating schemas with stock `Prelude.(++)`), with zero
`TypeFamilies`. Evaluate `sqlDemo` at the `ghci>` prompt.

```haskell
{-# LANGUAGE DependentTypes, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}
module TypedSQL where

import Data.Kind (Type)
import GHC.Tuple (Tuple2)
import GHC.Types (List)

data ColId = CId | CName | CActive
data SqlTy = SInt | SText | SBool
data Col   = MkCol ColId SqlTy

-- Ordinary term-to-Type function maps SQL column types to Haskell types:
sqlVal :: SqlTy -> Type
sqlVal SInt  = type Int
sqlVal SText = type String
sqlVal SBool = type Bool

data Row (s :: List Col) where
  RNil  :: Row []
  RCons :: sqlVal t -> Row rest -> Row (MkCol c t : rest)

data InSchema (col :: Col) (s :: List Col) where
  Here  :: InSchema col (col : rest)
  There :: InSchema col rest -> InSchema col (other : rest)

data Table where
  MkTable :: foreach (s :: List Col) -> List (Row s) -> Table

colName :: ColId -> String
colName CId     = "id"
colName CName   = "name"
colName CActive = "active"

sqlTypeName :: SqlTy -> String
sqlTypeName SInt  = "INT"
sqlTypeName SText = "TEXT"
sqlTypeName SBool = "BOOL"

createTableDDL :: String -> List Col -> String
createTableDDL tbl cols = "CREATE TABLE " ++ tbl ++ " (" ++ go cols ++ ");"
  where
    go []                 = ""
    go [MkCol c t]        = colName c ++ " " ++ sqlTypeName t
    go (MkCol c t : rest) = colName c ++ " " ++ sqlTypeName t ++ ", " ++ go rest

getCol :: InSchema (MkCol c t) s -> Row s -> sqlVal t
getCol Here      (RCons v _)    = v
getCol (There p) (RCons _ rest) = getCol p rest

-- INNER JOIN combines two row schemas directly with stock Prelude (++):
joinRow :: Row s1 -> Row s2 -> Row (s1 ++ s2)
joinRow RNil         r2 = r2
joinRow (RCons v r1) r2 = RCons v (joinRow r1 r2)

type UserSchema = [MkCol CId SInt, MkCol CName SText, MkCol CActive SBool]

userRows :: List (Row UserSchema)
userRows =
  [ RCons 1 (RCons "Ada"   (RCons True RNil))
  , RCons 2 (RCons "Grace" (RCons True RNil))
  ]

usersTable :: Table
usersTable = MkTable [MkCol CId SInt, MkCol CName SText, MkCol CActive SBool] userRows

tableDDL :: String -> Table -> String
tableDDL name (MkTable s _) = createTableDDL name s

sqlDemo :: Tuple2 String (List String)
sqlDemo =
  ( tableDDL "users" usersTable
  , map (getCol (There Here)) userRows
  )
```

:::

::: {.plfh-domain-tab id="tab-effects" data-tab-label="Effect Stacks" data-tab-audience="mtl / effectful"}

### 1.3 Composable `transformers` stacks from an ordinary `List Eff` {#card-effects}

<div class="showcase-credits">
  <strong>Replaces:</strong> <code>mtl</code> <em>O</em>(<em>n</em>&sup2;) lifting instances &middot; <code>polysemy</code> / <code>effectful</code> overlapping <code>Member</code> search &middot;
  <strong>Features:</strong> <code>foreach (es :: List Eff)</code> &middot; <code>transformers</code> (<code>ReaderT</code>, <code>StateT</code>, <code>WriterT</code>)
</div>

Pass any list of effects (`[EEnv, ECount, ELog]`) as an ordinary value.
`StackM` builds the nested `transformers` stack, `runStack` peels each layer at
runtime, and `Has e es` lifts `askEff`, `tickEff`, and `tellEff` structurally
without `mtl` instances or overlapping type classes. Evaluate `effDemo` at the
`ghci>` prompt.

```haskell
{-# LANGUAGE DependentTypes, TypeFamilies, UndecidableInstances #-}
module EffectStack where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader (ReaderT, ask, runReaderT)
import Control.Monad.Trans.State.Strict (StateT, modify', runStateT)
import Control.Monad.Trans.Writer.Strict (WriterT, runWriterT, tell)
import Data.Functor.Identity (Identity (runIdentity))
import Data.Kind (Type)
import GHC.Tuple (Tuple2, Unit)
import GHC.Types (List)

data Eff = EEnv | ECount | ELog

type family StackM (es :: List Eff) :: Type -> Type where
  StackM []            = Identity
  StackM (EEnv   : es) = ReaderT String (StackM es)
  StackM (ECount : es) = StateT  Int    (StackM es)
  StackM (ELog   : es) = WriterT (List String) (StackM es)

type family StackOut (es :: List Eff) (a :: Type) :: Type where
  StackOut []            a = a
  StackOut (EEnv   : es) a = StackOut es a
  StackOut (ECount : es) a = StackOut es (Tuple2 a Int)
  StackOut (ELog   : es) a = StackOut es (Tuple2 a (List String))

withMonad :: foreach (es :: List Eff) -> (Monad (StackM es) => r) -> r
withMonad []            k = k
withMonad (EEnv   : es) k = withMonad es k
withMonad (ECount : es) k = withMonad es k
withMonad (ELog   : es) k = withMonad es k

runStack :: foreach (es :: List Eff) -> String -> StackM es a -> StackOut es a
runStack []            _   m = runIdentity m
runStack (EEnv   : es) env m = runStack es env (runReaderT m env)
runStack (ECount : es) env m = runStack es env (runStateT  m 0)
runStack (ELog   : es) env m = runStack es env (runWriterT m)

-- Structural lifting witness replaces O(n^2) mtl instances and overlapping Member:
data Has (e :: Eff) (es :: List Eff) where
  Here  :: Has e (e : es)
  There :: Has e es -> Has e (x : es)

liftStep :: foreach (x :: Eff) (es :: List Eff)
         -> (Monad (StackM es) => StackM es a -> StackM (x : es) a)
liftStep EEnv   _ m = lift m
liftStep ECount _ m = lift m
liftStep ELog   _ m = lift m

askEff :: foreach (es :: List Eff) -> Has EEnv es -> StackM es String
askEff []       h = case h of {}
askEff (x : es) h = case x of
  EEnv   -> case h of { Here -> withMonad es ask; There p -> withMonad es (liftStep EEnv es (askEff es p)) }
  ECount -> case h of { There p -> withMonad es (liftStep ECount es (askEff es p)) }
  ELog   -> case h of { There p -> withMonad es (liftStep ELog es (askEff es p)) }

tickEff :: foreach (es :: List Eff) -> Has ECount es -> StackM es Unit
tickEff []       h = case h of {}
tickEff (x : es) h = case x of
  EEnv   -> case h of { There p -> withMonad es (liftStep EEnv es (tickEff es p)) }
  ECount -> case h of { Here -> withMonad es (modify' (+ 1)); There p -> withMonad es (liftStep ECount es (tickEff es p)) }
  ELog   -> case h of { There p -> withMonad es (liftStep ELog es (tickEff es p)) }

tellEff :: foreach (es :: List Eff) -> Has ELog es -> String -> StackM es Unit
tellEff []       h _   = case h of {}
tellEff (x : es) h msg = case x of
  EEnv   -> case h of { There p -> withMonad es (liftStep EEnv es (tellEff es p msg)) }
  ECount -> case h of { There p -> withMonad es (liftStep ECount es (tellEff es p msg)) }
  ELog   -> case h of { Here -> withMonad es (tell [msg]); There p -> withMonad es (liftStep ELog es (tellEff es p msg)) }

-- One polymorphic worker runs in any stack containing EEnv, ECount, and ELog:
worker :: foreach (es :: List Eff)
       -> Has EEnv es -> Has ECount es -> Has ELog es
       -> StackM es String
worker es hEnv hCount hLog = withMonad es (do
  env <- askEff es hEnv
  tellEff es hLog ("boot:" ++ env)
  tickEff es hCount
  tickEff es hCount
  tellEff es hLog "done"
  pure ("ok@" ++ env))

effDemo :: Tuple2 (Tuple2 String Int) (List String)
effDemo = runStack [EEnv, ECount, ELog] "prod"
  (worker [EEnv, ECount, ELog] Here (There Here) (There (There Here)))
```

:::

::: {.plfh-domain-tab id="tab-protocols" data-tab-label="Linear Protocols" data-tab-audience="typed-protocols"}

### 1.4 Session-typed network protocol with linear `foreach` {#card-linear}

<div class="showcase-credits">
  <strong>Replaces:</strong> <code>typed-protocols</code> (<code>StateToken</code>, <code>PeerHasAgency</code>, <code>exclusionLemma</code>) &middot;
  <strong>Proposals:</strong> <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0111-linear-types.html">#111 Linear Types</a> &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#quantifiers">#378 §4.4</a>
</div>

Dependent `foreach` binders combine directly with `-XLinearTypes`. An ordinary
promoted function (`agency`) enforces turn-taking while linear
`Chan from %1 -> Chan to` guarantees every channel handle is consumed once:
sending in `StDone`, reusing `c1`, or forgetting `closeChan` all fail at
compile time. Evaluate `runSession` at the `ghci>` prompt.

```haskell
{-# LANGUAGE DependentTypes, LinearTypes, ListTuplePuns #-}
module LinearProtocol where

import Data.Type.Equality ((:~:) (Refl))

data Ur a where
  Ur :: a -> Ur a

data ProtoState = StInit | StAuthed | StDone
data Agency     = ClientTurn | Closed

-- Ordinary promoted function replaces StateToken / PeerHasAgency / exclusionLemma:
agency :: ProtoState -> Agency
agency StInit   = ClientTurn
agency StAuthed = ClientTurn
agency StDone   = Closed

type Payload (st :: ProtoState) = case st of
  StInit   -> String
  StAuthed -> Int
  StDone   -> ()

data Msg (from :: ProtoState) (to :: ProtoState) where
  MLogin  :: Payload StInit   -> Msg StInit   StAuthed
  MQuery  :: Payload StAuthed -> Msg StAuthed StAuthed
  MLogout ::                     Msg StAuthed StDone

data Chan (st :: ProtoState) = MkChan (Ur [String])

-- Linear retained transition: consumes `from` and `Chan from` once,
-- and statically requires `agency from :~: ClientTurn`.
send :: foreach (from %1 :: ProtoState)
     -> (agency from :~: ClientTurn)
     -> Msg from to -> Chan from %1 -> Chan to
send StInit   Refl (MLogin tok) (MkChan (Ur log0)) = MkChan (Ur (("AUTH "  ++ tok)      : log0))
send StAuthed Refl (MQuery qid) (MkChan (Ur log0)) = MkChan (Ur (("QUERY " ++ show qid) : log0))
send StAuthed Refl MLogout      (MkChan (Ur log0)) = MkChan (Ur ("BYE"                  : log0))

closeChan :: Chan StDone %1 -> [String]
closeChan (MkChan (Ur log0)) = reverse log0

runSession :: [String]
runSession =
  let c0 = MkChan (Ur []) :: Chan StInit
      c1 = send StInit   Refl (MLogin "tok-42") c0
      c2 = send StAuthed Refl (MQuery 7)        c1
      c3 = send StAuthed Refl MLogout           c2
  in closeChan c3
```

:::

::: {.plfh-domain-tab id="tab-nets" data-tab-label="Neural Nets" data-tab-audience="grenade / hmatrix"}

### 1.5 Shape-checked neural networks and constructive tensor reshapes {#card-nets}

<div class="showcase-credits">
  <strong>Replaces:</strong> <code>grenade</code> / <code>hmatrix</code> / <code>vector-sized</code> (<code>KnownNat</code>, <code>SingI</code>, <code>ghc-typelits-natnormalise</code>, <code>unsafeCoerce</code>) &middot;
  <strong>Features:</strong> <code>Data.Vec.Dependent</code> &middot; <code>Data.Nat.Dependent.Properties</code> (<code>mulComm</code>)
</div>

Matrix multiplication (`matVec`) and multi-layer networks (`Net inp out`) track
dimensions with ordinary Peano `Nat` numerals and `Vec`, rejecting mismatched
weight matrices at compile time. `reshapeTranspose` transports
`Vec Double (mul r c)` to `Vec Double (mul c r)` in one line with
`dependent-base`'s constructively proved `mulComm`, without `TypeFamilies` or a
bespoke `ghc-typelits` solver plugin. Evaluate `netDemo` at the `ghci>` prompt.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module TypedNet where

import Data.Nat.Dependent (Nat (..), mul)
import Data.Nat.Dependent.Properties (mulComm)
import Data.Type.Equality.Dependent (rewrite)
import Data.Vec.Dependent (Vec (..), appendVec, foldrVec, mapVec, toListVec, zipWithVec)

type Matrix r c = Vec (Vec Double c) r

dot :: Vec Double n -> Vec Double n -> Double
dot xs ys = foldrVec (+) 0 (zipWithVec (*) xs ys)

-- Dimension-checked dense layer (mismatched weights fail at compile time):
matVec :: Matrix out inp -> Vec Double inp -> Vec Double out
matVec weights x = mapVec (`dot` x) weights

data Net (inp :: Nat) (out :: Nat) where
  NId    :: Net n n
  NDense :: Matrix h i -> Net h o -> Net i o

forward :: Net i o -> Vec Double i -> Vec Double o
forward NId          x = x
forward (NDense w n) x = forward n (mapVec (max 0) (matVec w x))

-- Flatten a matrix into a vector of length `mul r c`:
flatten :: foreach (r c :: Nat) -> Matrix r c -> Vec Double (mul r c)
flatten Zero     _ VNil           = VNil
flatten (Succ r) c (VCons row rs) = appendVec row (flatten r c rs)

-- Constructive reshape via dependent-base's proved `mulComm` (no ghc-typelits plugin needed):
reshapeTranspose :: foreach (r c :: Nat) -> Vec Double (mul r c) -> Vec Double (mul c r)
reshapeTranspose r c v = rewrite (mulComm r c) v

layer1 :: Matrix 2 3
layer1 =
  VCons (VCons 1.0 (VCons 2.0 (VCons (-1.0) VNil)))
 (VCons (VCons 0.5 (VCons (-1.0) (VCons 2.0 VNil))) VNil)

layer2 :: Matrix 1 2
layer2 = VCons (VCons 2.0 (VCons 3.0 VNil)) VNil

sampleNet :: Net 3 1
sampleNet = NDense layer1 (NDense layer2 NId)

netDemo :: ([Double], [Double])
netDemo =
  ( toListVec (forward sampleNet (VCons 1.0 (VCons 1.0 (VCons 1.0 VNil))))
  , toListVec (reshapeTranspose 2 3 (flatten 2 3 layer1))
  )
```

:::

::: {.plfh-domain-tab id="tab-codecs" data-tab-label="Wire Codecs" data-tab-audience="autodocodec / aeson"}

### 1.6 Self-documenting wire codec and schema framing without `TypeFamilies` {#card-codecs}

<div class="showcase-credits">
  <strong>Replaces:</strong> <code>autodocodec</code> / <code>aeson-schemas</code> / separate schema &amp; codec definitions &middot;
  <strong>Features:</strong> Term-to-<code>Type</code> large elimination &middot; Constructive schema associativity
</div>

One `Schema` value with ordinary `String` field names drives the payload type
(`payload :: Schema -> Type`, with zero `TypeFamilies`), documentation
(`docSchema`), encoder (`encode`), and decoder (`decode`). Constructive
associativity (`appendSchemaAssoc`) is consumed directly by `reassocPacket` to
re-frame concatenated packet schemas without copying wire tokens. Evaluate
`codecDemo` at the `ghci>` prompt.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module CheckedCodec where

import Data.Kind (Type)
import Data.Type.Equality.Dependent ((:~:) (Refl), cong, rewrite)

data Schema = SEnd | SInt String Schema | SBool String Schema

-- 1. Ordinary term-to-Type function computes the Haskell payload type (no TypeFamilies):
payload :: Schema -> Type
payload SEnd        = type ()
payload (SInt  _ r) = type (Int,  payload r)
payload (SBool _ r) = type (Bool, payload r)

-- 2. Documentation from the same Schema value:
docSchema :: Schema -> String
docSchema SEnd        = "{}"
docSchema (SInt  f r) = f ++ ":int, "  ++ docSchema r
docSchema (SBool f r) = f ++ ":bool, " ++ docSchema r

data Tok = TokInt Int | TokBool Bool deriving (Eq, Show)

-- 3. Bidirectional wire codec sharing one Schema value:
encode :: foreach (s :: Schema) -> payload s -> [Tok]
encode SEnd        ()      = []
encode (SInt  _ r) (n, xs) = TokInt  n : encode r xs
encode (SBool _ r) (b, xs) = TokBool b : encode r xs

decode :: foreach (s :: Schema) -> [Tok] -> Either String (payload s)
decode SEnd        []               = Right ()
decode SEnd        _                = Left "trailing tokens"
decode (SInt  _ r) (TokInt  n : ts) = fmap (\xs -> (n, xs)) (decode r ts)
decode (SBool _ r) (TokBool b : ts) = fmap (\xs -> (b, xs)) (decode r ts)
decode (SInt  f _) _                = Left ("expected int for "  ++ f)
decode (SBool f _) _                = Left ("expected bool for " ++ f)

-- 4. Schema concatenation + constructive associativity used to re-frame packets:
appendSchema :: Schema -> Schema -> Schema
appendSchema SEnd        s2 = s2
appendSchema (SInt  f r) s2 = SInt  f (appendSchema r s2)
appendSchema (SBool f r) s2 = SBool f (appendSchema r s2)

appendSchemaAssoc :: foreach (a b c :: Schema)
                  -> appendSchema (appendSchema a b) c :~: appendSchema a (appendSchema b c)
appendSchemaAssoc SEnd        _ _ = Refl
appendSchemaAssoc (SInt  f r) b c = cong (SInt  f) (appendSchemaAssoc r b c)
appendSchemaAssoc (SBool f r) b c = cong (SBool f) (appendSchemaAssoc r b c)

newtype Packet (s :: Schema) = MkPacket { unPacket :: [Tok] } deriving Show

reassocPacket :: foreach (a b c :: Schema)
              -> Packet (appendSchema (appendSchema a b) c)
              -> Packet (appendSchema a (appendSchema b c))
reassocPacket a b c p = rewrite (appendSchemaAssoc a b c) p

codecDemo :: (String, [Tok], Either String (Int, (Bool, (Int, ()))))
codecDemo =
  let wire = encode (SInt "id" (SBool "active" (SInt "score" SEnd))) (7, (True, (99, ())))
      pkt  = reassocPacket (SInt "id" SEnd) (SBool "active" SEnd) (SInt "score" SEnd) (MkPacket wire)
  in ( docSchema (SInt "id" (SBool "active" (SInt "score" SEnd)))
     , unPacket pkt
     , decode (SInt "id" (SBool "active" (SInt "score" SEnd))) (unPacket pkt)
     )
```

:::

::: {.plfh-domain-tab id="tab-units" data-tab-label="Units of Measure" data-tab-audience="dimensional / uom-plugin"}

### 1.7 Physical units of measure without `uom-plugin` or `TypeFamilies` {#card-units}

<div class="showcase-credits">
  <strong>Replaces:</strong> <code>dimensional</code> / <code>units</code> / bespoke <code>uom-plugin</code> <code>TcPlugin</code> &middot;
  <strong>Features:</strong> Stock <code>plus</code> &amp; <code>minus</code> &middot; Constructive <code>plusComm</code> &amp; <code>minusDiag</code>
</div>

Adding meters to seconds (`dist +! time`) fails at compile time with
`GHC-83865`. Each zero-cost `Qty mp mn sp sn` tracks numerator and denominator
exponents ($m^{mp - mn} \cdot s^{sp - sn}$) using ordinary `plus` and `minus`
from `dependent-base`, with zero `TypeFamilies` or `KnownNat` plumbing.
`commUnit` and `cancelSelf` prove commutativity and inverse cancellation
constructively for all dimensions via `plusComm` and `minusDiag`, without
writing a custom units-of-measure plugin. Evaluate `physicsDemo` at the `ghci>`
prompt.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module UnitsOfMeasure where

import Data.Nat.Dependent (Nat (..), minus, plus)
import Data.Nat.Dependent.Properties (minusDiag, plusComm)
import Data.Type.Equality.Dependent (rewrite)

-- Zero-cost quantity indexed by numerator/denominator exponents: m^(mp - mn) * s^(sp - sn).
newtype Qty (mp :: Nat) (mn :: Nat) (sp :: Nat) (sn :: Nat) = Qty { unQty :: Double }
  deriving Show

type Scalar = Qty 0 0 0 0
type Meter  = Qty 1 0 0 0
type Sec    = Qty 0 0 1 0
type Speed  = Qty 1 0 0 1  -- m^1 * s^-1

-- Adding incompatible units (e.g. `dist +! time`) fails at compile time with GHC-83865:
(+!) :: Qty mp mn sp sn -> Qty mp mn sp sn -> Qty mp mn sp sn
Qty x +! Qty y = Qty (x + y)

(*!) :: Qty mp1 mn1 sp1 sn1 -> Qty mp2 mn2 sp2 sn2
     -> Qty (plus mp1 mp2) (plus mn1 mn2) (plus sp1 sp2) (plus sn1 sn2)
Qty x *! Qty y = Qty (x * y)

(/!) :: Qty mp1 mn1 sp1 sn1 -> Qty mp2 mn2 sp2 sn2
     -> Qty (plus mp1 mn2) (plus mn1 mp2) (plus sp1 sn2) (plus sn1 sp2)
Qty x /! Qty y = Qty (x / y)

-- Cancel common powers in numerator and denominator using stock `minus`:
normalize :: Qty mp mn sp sn -> Qty (minus mp mn) (minus mn mp) (minus sp sn) (minus sn sp)
normalize (Qty x) = Qty x

-- Constructive commutativity and self-cancellation for ALL dimensions via dependent-base:
commUnit :: foreach (mp1 mn1 sp1 sn1 mp2 mn2 sp2 sn2 :: Nat)
         -> Qty (plus mp1 mp2) (plus mn1 mn2) (plus sp1 sp2) (plus sn1 sn2)
         -> Qty (plus mp2 mp1) (plus mn2 mn1) (plus sp2 sp1) (plus sn2 sn1)
commUnit mp1 mn1 sp1 sn1 mp2 mn2 sp2 sn2 q =
  rewrite (plusComm mp1 mp2) (rewrite (plusComm mn1 mn2)
    (rewrite (plusComm sp1 sp2) (rewrite (plusComm sn1 sn2) q)))

cancelSelf :: foreach (mp mn sp sn :: Nat)
           -> Qty (plus mp mn) (plus mn mp) (plus sp sn) (plus sn sp)
           -> Scalar
cancelSelf mp mn sp sn q =
  rewrite (plusComm mn mp)
    (rewrite (plusComm sn sp)
      (rewrite (minusDiag (plus mp mn))
        (rewrite (minusDiag (plus sp sn)) (normalize q))))

physicsDemo :: (Double, Double)
physicsDemo =
  let dist  = Qty 100.0 :: Meter
      time  = Qty 10.0  :: Sec
      speed = normalize (dist /! time) :: Speed
      ratio = cancelSelf 1 0 0 0 (dist /! dist)
  in (unQty speed, unQty ratio)
```

:::

::: {.plfh-domain-tab id="tab-printf" data-tab-label="Type-Safe Printf" data-tab-audience="Text.Printf"}

### 1.8 Type-safe `printf` without `TypeFamilies` {#card-printf}

<div class="showcase-credits">
  <strong>Replaces:</strong> Runtime <code>Text.Printf</code> crashes &amp; polyvariadic type classes &middot;
  <strong>Proposal:</strong> <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#dependent-application-and-the-static-subset">#378 §4.7 Dependent Application</a>
</div>

An ordinary Haskell function `fmtType :: Fmt -> Type` computes both the arity
and argument types of `printf` directly from a `Fmt` value, with zero
`TypeFamilies`. GHC checks that `"Haskell" :: String` and `25 :: Int` match
`S` followed by `D` and rejects mismatched arguments at compile time. Evaluate
`greeting` at the `ghci>` prompt.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module Printf where

import Data.Kind (Type)

data Fmt
  = End
  | Lit String Fmt
  | D Fmt
  | S Fmt

-- Ordinary term-to-Type function (no `type family` required):
fmtType :: Fmt -> Type
fmtType End       = type String
fmtType (Lit _ r) = type (fmtType r)
fmtType (D r)     = type (Int -> fmtType r)
fmtType (S r)     = type (String -> fmtType r)

printf :: foreach (f :: Fmt) -> fmtType f
printf f = go f ""
  where
    go :: foreach (f' :: Fmt) -> String -> fmtType f'
    go End       acc = acc
    go (Lit s r) acc = go r (acc ++ s)
    go (D r)     acc = \n -> go r (acc ++ show n)
    go (S r)     acc = \s -> go r (acc ++ s)

-- GHC checks that `"Haskell" :: String` and `25 :: Int` match `S` followed by `D`:
greeting :: String
greeting = printf (Lit "Hello " (S (Lit ", " (D (Lit " chapters checked!" End))))) "Haskell" 25
```

:::

::::

:::::

::::: {.plfh-showcase-act id="act-2" data-act-num="2" data-act-title="Quantifiers & Data"}

## 2. Retained quantifiers, dependent pairs, records, and runtime types

This section walks through the core building blocks of `-XDependentTypes`:
retained `foreach` (written `∏` under `-XUnicodeSyntax`), dependent pairs
(`some`), dependent records, runtime `Type` matching, and GADT refutation.

### 2.1 Retained `foreach`, Peano arithmetic, and decimal numerals {#card-nat}

<div class="showcase-credits">
  <strong>Proposals:</strong>
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#quantifiers">#378 §4.4–4.5 Quantifiers</a> &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0364-unify-natural.html">#364 Unify <code>Nat</code> &amp; <code>Natural</code></a>
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
module Peano where

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

### 2.2 Dependent pairs (`some` / `Sigma`) and `OverloadedRecordDot` {#card-sigma}

<div class="showcase-credits">
  <strong>Proposals:</strong>
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#erasure">#378 §4.2 Predictable Erasure</a> &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0282-record-dot-syntax.html">#282 Record Dot Syntax</a>
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
module DependentPairs where

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

### 2.3 Dependent records and type-changing updates {#card-records}

<div class="showcase-credits">
  <strong>Proposals:</strong>
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0282-record-dot-syntax.html">#282 Record Dot Syntax</a> &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html">#378 Dependent Types</a>
</div>

Dependent records generalize `Sigma` to named fields: later fields can mention
earlier fields in their types (`rowItems :: Vec a rowLen`), projections work
with `.field`, and record updates can change a type parameter (`SizedRow Int`
to `SizedRow String`) while preserving the stored length `rowLen`.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns, OverloadedRecordDot #-}
module DependentRecords where

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

### 2.4 Runtime `Type` pattern matching: type-directed JSON {#card-typecase}

<div class="showcase-credits">
  <strong>Proposal:</strong>
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#phase-distinction">#378 §4.9 Phase Distinction</a>
</div>

A `foreach (a :: Type)` argument retains a type representation at runtime.
Matching on `a` with an ordinary `case` handles both atomic (`Int`, `Bool`)
and compound (`[Char]`, `Maybe Int`, `(Int, Bool)`) type patterns, refining `v
:: a` in every branch without `Typeable` casts, `eqT` pyramids, or type classes.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module RuntimeTypeJson where

import Data.Kind (Type)

-- Type-directed JSON serializer with compound Type patterns (no Typeable or classes):
toJson :: foreach (a :: Type) -> a -> String
toJson a v = case a of
  Int         -> show v
  Bool        -> if v then "true" else "false"
  [Char]      -> "\"" ++ v ++ "\""
  Maybe Int   -> maybe "null" show v
  (Int, Bool) -> "[" ++ show (fst v) ++ "," ++ toJson Bool (snd v) ++ "]"
  _           -> "\"<opaque>\""

jsonDemo :: [String]
jsonDemo =
  [ toJson Int         42
  , toJson Bool        True
  , toJson [Char]      "dependent haskell"
  , toJson (Maybe Int) (Just 7)
  , toJson (Int, Bool) (3, False)
  , toJson Double      3.14
  ]
```

### 2.5 Off-diagonal GADT refutation (`zipEqualVec`) {#card-refute}

<div class="showcase-credits">
  <strong>Proposals:</strong>
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html#dependent-pattern-match">#378 §4.5</a> &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0402-gadt-syntax.html">#402 GADT Syntax</a>
</div>

When two retained lengths `m` and `n` are tied by `m :~: n`, GHC's pattern
match checker refutes the off-diagonal `Zero`/`Succ` and `Succ`/`Zero` cases.
Only the two diagonal equations need to be written.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module ZipEqual where

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

:::::

::::: {.plfh-showcase-act id="act-3" data-act-num="3" data-act-title="Types as Code"}

## 3. Term promotion, type-level expressions, and matchability

Under `-XDependentTypes`, ordinary functions compute inside types alongside
inline `case`, `let`, local `type` synonyms inside term `let`/`where` blocks,
type-level lambdas, and explicit matchability (`%M` / `%U` / `%m`). None of the
three modules below uses `TypeFamilies`.

### 3.1 Stock `Prelude` lists and open function evaluation {#card-lists}

<div class="showcase-credits">
  <strong>Proposals:</strong>
  <a href="https://github.com/ghc-proposals/ghc-proposals/pull/509">#509 Type-Level Functions</a> &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0475-tuple-syntax.html">#475 Non-Punning List &amp; Tuple Syntax</a>
</div>

Ordinary functions on `Prelude` lists (`(++)`, `map`, `Data.List.Dependent.size`)
publish checked source equations in `.hi` interfaces and reduce symbolically
over unknown `foreach` variables. Under `NoListTuplePuns` (implied by
`-XDependentTypes`), `[]` and `:` work directly in types without promotion
ticks.

```haskell
{-# LANGUAGE DependentTypes, NoListTuplePuns #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}
module ListLaws where

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

### 3.2 Type-level `case`, type-level `let`, and local `type` synonyms {#card-type-case-let}

<div class="showcase-credits">
  <strong>Proposal:</strong>
  <a href="https://github.com/ghc-proposals/ghc-proposals/pull/523">#523 Extended <code>let</code></a>
</div>

Type expressions support inline `case` matching (`case isNumeric of True ->
Int; False -> String`) and ordered `let` bindings (`let slot = Maybe a in
(slot, Either String slot)`). Inside term `let` and `where` blocks, non-recursive
local `type` synonyms can capture retained `foreach` variables in scope.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module TypeCaseLet where

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

### 3.3 Type-level lambdas, higher-order forms, and matchability (`%M`, `%U`, `%m`) {#card-type-lambda}

<div class="showcase-credits">
  <strong>Proposals &amp; paper:</strong>
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0242-unsaturated-type-families.html">#242 Unsaturated Type Families</a>
  (Kiss et al., <a href="https://doi.org/10.1145/3341706">ICFP 2019</a>) &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0281-visible-forall.html">#281 Visible <code>forall</code></a> &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0370-modifiers.html">#370 Modifiers</a>
</div>

GHC distinguishes two kinds of type-level arrows. A **matchable** arrow (`a %M
-> b`) is injective and generative, such as `Maybe` or `Succ`: if `f x ~ f y`,
GHC concludes `x ~ y`. An **unmatchable** arrow (`a %U -> b`) allows arbitrary
computation, including type-level lambdas (`\t -> Either String (Maybe t)`) and
partially applied promoted functions (`plus 1`).

In higher-kinded data libraries (`barbies`, `vinyl`, `singletons`), passing a
composed wrapper to a record requires `Compose`/`Identity` newtypes or
`TyFun`/`@@` defunctionalization because standard `Type -> Type` is restricted
to matchable constructors. Here `Form (f :: Type %U -> Type)` accepts inline
type-level lambdas directly, `Prelude.map (plus 1)` promotes without a
`type family`, and matchability-polymorphic `cong` (`a %m -> b`) handles `%M`,
`%U`, and operator sections uniformly.

```haskell
{-# LANGUAGE DependentTypes #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}
module FormValidation where

import Data.Kind (Type)
import Data.Nat.Dependent (Nat (..), plus)
import Data.Type.Equality.Dependent ((:~:) (Refl), cong)
import GHC.Matchability (M, U)
import GHC.Types (List)

-- Ordinary Prelude.map promotes directly with partially applied `plus 1` (no type family):
type Incremented = map (plus 1) [Zero, Succ Zero, Succ (Succ Zero)]

incProof :: Incremented :~: [Succ Zero, Succ (Succ Zero), Succ (Succ (Succ Zero))]
incProof = Refl

-- `%U` (unmatchable): accepts inline type-level lambdas directly, with no Compose/TyFun:
data Form (f :: Type %U -> Type) (ts :: List Type) where
  FNil  :: Form f []
  FCons :: f t -> Form f ts -> Form f (t : ts)

type OptField    = \t -> Maybe t
type ValidField  = \t -> Either String t
type StagedField = \t -> Either String (Maybe t)

type PartialForm   ts = Form OptField ts
type ValidatedForm ts = Form ValidField ts
type StagedForm    ts = Form StagedField ts

type UserFields = [String, Int, Bool]

requireFields :: List String -> PartialForm ts -> ValidatedForm ts
requireFields _        FNil            = FNil
requireFields (l : ls) (FCons mv rest) =
  FCons (maybe (Left ("Missing " ++ l)) Right mv) (requireFields ls rest)
requireFields []       (FCons mv rest) =
  FCons (maybe (Left "Missing field") Right mv) (requireFields [] rest)

sampleValidated :: ValidatedForm UserFields
sampleValidated =
  requireFields ["name", "age", "active"]
    (FCons (Just "Ada") (FCons Nothing (FCons (Just True) FNil)))

sampleStaged :: StagedForm UserFields
sampleStaged =
  FCons (Right (Just "Ada")) (FCons (Left "invalid") (FCons (Right Nothing) FNil))

-- `%M` (matchable): accepts injective constructors (`Maybe`), rejects lambdas.
data BoxM (f :: Type %M -> Type) (a :: Type) = MkBoxM (f a)

boxedMaybe :: BoxM Maybe Int
boxedMaybe = MkBoxM (Just 42)

-- Matchability-polymorphic `cong` (`a %m -> b`) handles `%M`, `%U`, and sections uniformly:
congMatchable :: forall (m n :: Nat). m :~: n -> Succ m :~: Succ n
congMatchable eq = cong Succ eq

congUnmatchable :: forall (n p :: Nat). foreach (m :: Nat)
                -> n :~: p -> plus m n :~: plus m p
congUnmatchable m eq = cong (plus m) eq

congConsLeft :: forall a (x :: a) (ys1 ys2 :: List a).
                ys1 :~: ys2 -> (x : ys1) :~: (x : ys2)
congConsLeft eq = cong (x :) eq
```

:::::

::::: {.plfh-showcase-act id="act-4" data-act-num="4" data-act-title="Exists & Base"}

## 4. Erased existentials and `dependent-base`

[`TharkunAB/dependent-base`](https://github.com/TharkunAB/dependent-base)
(documented in the [`dependent-base` Reference](/DependentBase/)) builds a
standard library directly on stock `Prelude` types (`Bool`, `Maybe`, `Either`,
`(,)`, `[a]`, `(:~:)`, `Void`) and compiles `.hi` interfaces that ordinary
`Haskell2010` modules can import without enabling `-XDependentTypes`.

### 4.1 Erased existentials (`GHC.Exists` & `Data.Exists.Dependent`) {#card-exists}

<div class="showcase-credits">
  <strong>Proposals:</strong>
  <a href="https://github.com/ghc-proposals/ghc-proposals/pull/473">#473 Existential Types</a> &middot;
  <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0581-namespace-specified-imports.html">#581 Namespace-Specified Imports</a>
</div>

Proposal `#473` separates retained dependent pairs (`some` / `Sigma`) from
erased existential packages (`Exists p = exists x | p x`). In an `Exists`
package, the hidden witness is erased before runtime: callers can use a packed
type class dictionary (`Show a /\ a`) or apply a polymorphic transformation
(`mapExists`), but cannot branch on the hidden type or read a runtime length
tag.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module ExistsDemo where

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

### 4.2 First-class dependent composition `(.)` {#card-dep-compose}

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
module DepCompose where

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

### 4.3 Length-indexed `Vec` and bounded `Fin` indexing {#card-vec-fin}

<div class="showcase-credits">
  <strong>Package:</strong>
  <a href="https://github.com/TharkunAB/dependent-base"><code>TharkunAB/dependent-base</code></a> &middot;
  <a href="/DependentBase/#datavecdependent"><code>Data.Vec.Dependent</code></a> &middot;
  <a href="/DependentBase/#datafindependent"><code>Data.Fin.Dependent</code></a>
</div>

`Data.Vec.Dependent` and `Data.Fin.Dependent` pair length-checked operations
(`appendVec`, `zipVec`, total `lookupVec`) with runtime list conversions
(`packListVec`, `toListVec`). `Fin` names its constructors `FZ` and `FS` so
`Prelude.Dependent` can export `Nat (Zero, Succ)` and `Fin (FZ, FS)`
unqualified together, without a partial `Num` instance.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
module VecFin where

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

:::::

::::: {.plfh-showcase-act id="act-5" data-act-num="5" data-act-title="Plugins & Holes"}

## 5. Interactive Agda-mode and compiler plugins

Proof search and observational equality are external GHC plugins. GHC's core
solver and typed-hole machinery stay general, and both plugins are statically
linked into the browser WebAssembly build so you can run them here.

### 5.1 Typed holes, case splits, and `Dependent.Plugin.ProofSearch` {#card-agda-mode}

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
module TypedHoles where

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

### 5.2 Reference-oracle checking with `Dependent.Plugin.ObsEq` {#card-obs-eq}

<div class="showcase-credits">
  <strong>Plugin &amp; credit:</strong>
  <a href="https://github.com/TharkunAB/dependent-obs-eq"><code>TharkunAB/dependent-obs-eq</code></a>
  (<code>-fplugin=Dependent.Plugin.ObsEq</code>) &middot;
  Idea by <strong>Jules (<code>@analytichegel</code>)</strong>
</div>

The main pattern for `Dependent.Plugin.ObsEq` is comparing a fast or
non-structural implementation against a simple structural reference oracle.
Structural `plus` promotes directly into GHC's type checker, while `unfoldPlus`
and tail-recursive `accPlus` do not have structural source equations. With the
plugin enabled, GHC elaborates open calls into uninterpreted families (`U:f`)
and tests equivalence against the reference oracle in-process over total and
partial (`ObsBottom`) inputs. Explicit combinators (`obsEq`, `obsEqWith`,
`obsEqGen`) discharge passing witnesses while keeping bare `Refl` strict, and
`toAccVec` / `fromAccVec` use the checked witness to transport length-indexed
vectors across `accPlus`.

Click **Edit**, change `go Zero acc = acc` to `go Zero acc = Succ acc`, and
press **`Ctrl/Cmd+Enter`** to watch the plugin refute `accPlusCorrect` with a
shrunk counterexample (`m = Zero, n = Zero`).

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ObsEq -fplugin-opt=Dependent.Plugin.ObsEq:tests=30 #-}
module ObsEqDemo where

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

-- 3. Domain-restricted law on even Ints via a custom generator (`obsEqGen`).
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

evenRoundtrip :: foreach (n :: Int) -> twiceHalfEven n :~: n
evenRoundtrip n = obsEqGen genEvenInt

-- Transport a length-indexed `Vec` across an observational witness at runtime:
-- `gcastWith (obsEqWith totalCfg)` transports via an explicit `(:~:)` witness,
-- while `withObsEqWith totalCfg` brings the tested `a ~ b` constraint into scope directly.
toAccVec :: foreach (m n :: Nat) -> Vec Int (plus m n) -> Vec Int (accPlus m n)
toAccVec m n v = gcastWith (obsEqWith totalCfg :: plus m n :~: accPlus m n) v

fromAccVec :: foreach (m n :: Nat) -> Vec Int (accPlus m n) -> Vec Int (plus m n)
fromAccVec m n v =
  withObsEqWith totalCfg @(accPlus m n) @(plus m n) @(Vec Int (plus m n)) v

roundtripAccVec :: foreach (m n :: Nat) -> Vec Int (plus m n) -> Vec Int (plus m n)
roundtripAccVec m n v = fromAccVec m n (toAccVec m n v)

sampleAccVec :: [Int]
sampleAccVec = toListVec (roundtripAccVec 2 1 (VCons 10 (VCons 20 (VCons 30 VNil))))
```

### 5.3 NP-style witness checking: the Four-Color Theorem (`ObsEq`) {#card-four-color}

<div class="showcase-credits">
  <strong>Plugin:</strong>
  <a href="https://github.com/TharkunAB/dependent-obs-eq"><code>TharkunAB/dependent-obs-eq</code></a>
  (<code>-fplugin=Dependent.Plugin.ObsEq</code>) &middot;
  <strong>Pattern:</strong> Hard general theorem, fast polynomial witness check
</div>

A complementary pattern for `ObsEq` is NP-style witness certification, where a
general proof is massive (Georges Gonthier's formal proof of the Four-Color
Theorem took ~60,000 lines of Coq) yet checking a candidate coloring takes one
pass over the edges. Here `buildPlanar` builds guaranteed-planar triangulations
(stacked Apollonian networks) from a list of face subdivisions: `[]` is a
triangle ($K_3$), `[0]` places a vertex inside that triangle to form a
tetrahedron ($K_4$), and longer lists subdivide further faces while preserving
planarity. `colorGraph` searches for a coloring, `validColoring` verifies every
edge, and `ObsEq` certifies `validColoring steps :~: True` during compilation.

Click **Edit**, delete `Yellow` from `palette` (attempting 3-coloring instead
of 4-coloring), and press **`Ctrl/Cmd+Enter`** to watch GHC refuse to compile
and shrink the planar counterexample straight to **`steps = [0]`** ($K_4$, the
exact smallest planar graph that requires four colors). Evaluate
`fourColorDemo` at the `ghci>` prompt.

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns #-}
{-# OPTIONS_GHC -fplugin=Dependent.Plugin.ObsEq -fplugin-opt=Dependent.Plugin.ObsEq:tests=25 #-}
module FourColor where

import Data.Maybe (fromMaybe)
import Data.Type.Equality ((:~:))
import Dependent.ObsEq (ObsConfig, defaultObsConfig, obsEqWith, withMaxSize, withPartialPct)

graphCfg :: ObsConfig
graphCfg = withMaxSize 5 (withPartialPct 0 defaultObsConfig)

data Color = Red | Green | Blue | Yellow deriving (Eq, Show)

-- Palette of 4 colors. Delete `Yellow` (3-coloring) to watch GHC shrink to `steps = [0]` (K4)!
palette :: [Color]
palette = [Red, Green, Blue, Yellow]

-- Build a planar triangulation by repeatedly subdividing triangular faces:
-- [] = K3 (triangle), [0] = K4 (tetrahedron), longer lists = stacked planar triangulations.
buildPlanar :: [Int] -> (Int, [(Int, Int)])
buildPlanar steps = go 3 [(0, 1, 2)] [(0, 1), (1, 2), (2, 0)] steps
  where
    go n _     edges []       = (n, edges)
    go n faces edges (k : ks) =
      let idx              = abs k `mod` length faces
          (before, rest)   = splitAt idx faces
          ((a, b, c), aft) = case rest of (f : fs) -> (f, fs); [] -> ((0, 1, 2), [])
          faces'           = before ++ [(a, b, n), (b, c, n), (c, a, n)] ++ aft
          edges'           = (a, n) : (b, n) : (c, n) : edges
      in go (n + 1) faces' edges' ks

-- Backtracking k-coloring solver for vertices 0..n-1:
colorGraph :: Int -> [(Int, Int)] -> Maybe [(Int, Color)]
colorGraph n edges = go 0 []
  where
    go v assigned
      | v == n    = Just (reverse assigned)
      | otherwise = firstJust [go (v + 1) ((v, c) : assigned) | c <- palette, ok v c assigned]
    ok v c assigned =
      all (\(u, col) -> not (adj u v) || col /= c) assigned
    adj u v = any (\(x, y) -> (x == u && y == v) || (x == v && y == u)) edges
    firstJust []             = Nothing
    firstJust (Just r  : _)  = Just r
    firstJust (Nothing : rs) = firstJust rs

-- Fast polynomial verifier: checks every vertex is colored and no edge clashes.
validColoring :: [Int] -> Bool
validColoring steps =
  let (n, edges) = buildPlanar steps
  in case colorGraph n edges of
    Nothing  -> False
    Just col ->
      length col == n &&
      all (\(u, v) -> lookup u col /= lookup v col) edges

data FourColorCert (steps :: [Int]) where
  MkFourColor :: [(Int, Color)] -> (validColoring steps :~: True) -> FourColorCert steps

fourColor :: foreach (steps :: [Int]) -> FourColorCert steps
fourColor steps =
  let (n, edges) = buildPlanar steps
      col        = fromMaybe [] (colorGraph n edges)
  in MkFourColor col (obsEqWith graphCfg)

colorPlanar :: [Int] -> [(Int, Color)]
colorPlanar steps = case fourColor steps of MkFourColor col _ -> col

-- Color K4 ([0]) and a 7-vertex stacked planar triangulation ([0, 1, 2, 0]):
fourColorDemo :: ([(Int, Color)], [(Int, Color)])
fourColorDemo = (colorPlanar [0], colorPlanar [0, 1, 2, 0])
```

:::::

::::::

## Repositories and design choices

| Repository | Role |
| --- | --- |
| [`TharkunAB/ghc`](https://github.com/TharkunAB/ghc/tree/dependent-haskell) | GHC 10.1 fork implementing `-XDependentTypes`, native dependent Core (`DepFunTy`, `TermVarTy`, `ExistsTy`), and the [Serokell roadmap](https://ghc.serokell.io/dh) ([`ROADMAP.md`](https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/ROADMAP.md)) |
| [`TharkunAB/dependent-base`](https://github.com/TharkunAB/dependent-base) | Standard library (`Prelude.Dependent`, `Data.Function.Dependent`, `Data.Decision`, `Data.{Nat,List,Vec,Fin,Sigma,Exists,...}.Dependent`); see the [API reference](/DependentBase/) |
| [`TharkunAB/dependent-proof-search`](https://github.com/TharkunAB/dependent-proof-search) | `HoleFitPlugin` (`-fplugin=Dependent.Plugin.ProofSearch`) for congruence/transitivity subgoal refinements and bounded proof synthesis |
| [`TharkunAB/dependent-obs-eq`](https://github.com/TharkunAB/dependent-obs-eq) | `TcPlugin` (`-fplugin=Dependent.Plugin.ObsEq`, idea by Jules `@analytichegel`) for observational-equality testing and counterexample shrinking |
| [`TharkunAB/PLFH`](https://github.com/TharkunAB/PLFH) | 25-chapter interactive textbook adapted from PLFA ([Table of Contents](/), [Coverage](/Status/), [Setup](/Setup/)) |

<div class="showcase-decisions">
  <div class="decision-card">
    <h3>1. Specification hierarchy</h3>
    <p>Syntax, flags, and typing rules follow
    <a href="https://ghc-proposals.readthedocs.io/en/latest/proposals/0378-dependent-type-design.html">GHC Proposal #378</a>
    first, companion GHC proposals second, the Serokell roadmap for scope tracking,
    and Agda/PLFA for surface conventions where proposals are silent.</p>
  </div>
  <div class="decision-card">
    <h3>2. Opt-in extension and <code>Haskell2010</code> interop</h3>
    <p>Existing Haskell code compiles unchanged. One pragma (<code>-XDependentTypes</code>)
    enables retained binders, function promotion, and <code>NoListTuplePuns</code>.
    Plain <code>Haskell2010</code> modules import compiled interfaces from
    <code>dependent-base</code> without enabling dependent extensions.</p>
  </div>
  <div class="decision-card">
    <h3>3. Type safety without forced totality</h3>
    <p>Following Weirich et al. (ICFP 2017), System FC stays type-safe even with
    general recursion and non-termination. Structural totality diagnostics are opt-in
    (<code>-freport-totality</code>), while proof search and observational equality
    live in external GHC plugins.</p>
  </div>
  <div class="decision-card">
    <h3>4. Predictable boundaries</h3>
    <p>Effectful <code>IO</code> actions and uncertified non-structural functions stay
    outside built-in type conversion (<code>#378 §4.10</code>). Bare <code>-&gt;</code>
    in patterns remains reserved for <code>ViewPatterns</code>, and
    <code>Haskell2010</code> defaults stay intact when <code>-XDependentTypes</code>
    is off.</p>
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
