---
title: "Inference: Type Inference for Intrinsically-Typed Terms"
prev: /DeBruijn/
next: /Untyped/
src: content/part2/Inference.md
module: PLFH.Part2.Inference
plfaChapter: https://plfa.inf.ed.ac.uk/Inference/
---

In [DeBruijn](/DeBruijn/) we represented programs as intrinsically typed terms
`Term g a`, whose well-typedness is enforced statically by GHC. That makes
metatheory wonderfully clean—ill-typed terms simply do not exist!—but it leaves
a practical question: in a real compiler or interpreter, programs arrive from a
parser as **untyped abstract syntax trees** (`RawTerm`), not as pre-verified
typing derivations!

How do we bridge the gap between untyped syntax and intrinsically typed terms?
We write a **certified type inference and typechecking algorithm**:

- Given a runtime typing context `g :: Ctx` and a raw syntax tree `RawTerm`,
  `infer` *synthesizes* a runtime type `a :: Ty` paired with an intrinsically
  typed `Term g a` (or returns `Nothing` if the raw term is ill-typed).
- Given an expected runtime type `a :: Ty`, `check` verifies that the raw term
  has type `a` and returns `Maybe (Term g a)`.

Notice the beauty of dependent types here: **soundness of type inference is
guaranteed by construction!** Because `infer` returns a `Term g a`, it is
impossible for `infer` to succeed and report a bogus type—the returned value
*is* a complete machine-checked typing derivation! Every single line of this
chapter compiles natively with `-dcore-lint -dstg-lint` with **no singletons
and no type families**.

## Imports

We import propositional equality `(:~:)`, Peano naturals `Data.Nat.Dependent` (for
raw de Bruijn numbers), `Not` from [Decidable](/Decidable/), and our
intrinsically typed STLC definitions from [DeBruijn](/DeBruijn/).

```haskell
{-# LANGUAGE DependentTypes, LambdaCase #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
module PLFH.Part2.Inference
  ( RawTerm (..)
  , decEqTy
  , Typed (..)
  , LookupRes (..)
  , lookupCtx
  , infer
  , check
  , rawIdNat
  , rawTwo
  , TermPos (..)
  , TermNeg (..)
  , LookupAt (..)
  , eraseLookupAt
  , lookupAtUnique
  , LookupDec (..)
  , lookupDec
  , Synth (..)
  , Inherit (..)
  , eraseSynth
  , eraseInherit
  , synthUnique
  , SynthDec (..)
  , synthesize
  , inherit
  , bidirIdAppTwo
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import qualified Data.Nat.Dependent as N
import PLFH.Part1.Decidable (Dec (..), Not)
import PLFH.Part2.DeBruijn (Ctx (..), Lookup (..), Term (..), Ty (..))
```

## Bidirectional vs. syntax-directed typing, and raw syntax (`RawTerm`)

Our typing rules in [DeBruijn](/DeBruijn/) are almost **syntax-directed**: the
outermost constructor of a term determines which typing rule applies. The only
places where an untyped term lacks enough information to *synthesize* its type
from the bottom up are variable-binding forms (`Lam` and `Mu`), where the
bound variable's type could otherwise be anything.

Following PLFA's Church-style raw syntax, we annotate `RLam` and `RMu` with the
type `Ty` of their bound variable, while variable occurrences are plain runtime
natural numbers `N.Nat` (unverified de Bruijn indices):

```haskell
-- | Untyped abstract syntax tree with runtime de Bruijn indices and binder annotations.
data RawTerm
  = RVar N.Nat
  | RLam Ty RawTerm
  | RApp RawTerm RawTerm
  | RZero
  | RSuc RawTerm
  | RCase RawTerm RawTerm RawTerm
  | RMu Ty RawTerm
  deriving (Show)
```

Notice what is *not* checked by `RawTerm`: `RVar 99` can refer out of bounds,
`RApp RZero RZero` can apply zero to zero, and `RCase RZero RZero (RLam TNat (RVar 0))`
can have mismatched branch types. Our certified `infer` function will reject all
of these and produce a `Term g a` only when every typing invariant holds.

## Decidable type equality (`decEqTy`)

When typechecking an application `RApp l m`, a `RCase` expression's two
branches, or a recursive `RMu a m`, we need to test whether two runtime types
`a` and `b` are equal—and, when they are, obtain a **propositional equality
proof** `a :~: b` so GHC knows `Term g a` and `Term g b` have the same type!

Because `Ty` is a simple inductive datatype, structural recursion on retained
`foreach (a :: Ty)` and `foreach (b :: Ty)` decides equality cleanly:

```haskell
-- | Decidable equality on simple types `Ty`.
decEqTy :: foreach (a b :: Ty) -> Either (Not (a :~: b)) (a :~: b)
decEqTy TNat         TNat         = Right Refl
decEqTy TNat         (TArr _ _)   = Left (\case {})
decEqTy (TArr _ _)   TNat         = Left (\case {})
decEqTy (TArr a1 a2) (TArr b1 b2) = case decEqTy a1 b1 of
  Left neq   -> Left (\Refl -> neq Refl)
  Right Refl -> case decEqTy a2 b2 of
    Left neq   -> Left (\Refl -> neq Refl)
    Right Refl -> Right Refl
```

## Dependent result packages & runtime context lookup

When `infer` succeeds on a raw term in context `g`, it does not know the
result type `a` in advance—it *discovers* `a` at runtime! We therefore package
the inferred runtime type `a :: Ty` (bound with `foreach` so callers can inspect
it!) together with the intrinsically typed term `Term g a` in a dependent pair
`Typed g`.

Likewise, looking up a raw de Bruijn number `n :: N.Nat` in a runtime context
`g :: Ctx` returns `Maybe (LookupRes g)`, pairing the discovered entry type `a`
with the verified de Bruijn pointer `Lookup g a`:

```haskell
-- | An inferred runtime type paired with its intrinsically typed term.
data Typed (g :: Ctx) where
  MkTyped :: foreach (a :: Ty) -> Term g a -> Typed g

-- | A successful context lookup: runtime type `a` and proof `Lookup g a`.
data LookupRes (g :: Ctx) where
  Found :: foreach (a :: Ty) -> Lookup g a -> LookupRes g

-- | Look up a runtime de Bruijn number in a runtime typing context `g`.
lookupCtx :: foreach (g :: Ctx) -> N.Nat -> Maybe (LookupRes g)
lookupCtx CEmpty     _          = Nothing
lookupCtx (CExt _ a) N.Zero     = Just (Found a Z)
lookupCtx (CExt g _) (N.Succ n) = case lookupCtx g n of
  Nothing          -> Nothing
  Just (Found b p) -> Just (Found b (S p))
```

## Certified Type Inference (`infer`) and Checking (`check`)

Now `infer` walks `RawTerm` structurally, combining `lookupCtx` and `decEqTy`:

- **`RVar n`**: look up `n` in `g`; if found at type `a` with pointer `p`, wrap
  `Var p`.
- **`RLam a body`**: extend the runtime context to `CExt g a`, infer `body`'s
  type `b`, and return `TArr a b` with `Lam body'`.
- **`RApp l m`**: infer `l`'s type `lTy`, match on `lTy` to ensure it is
  `TArr a b`, infer `m`'s type `a'`, and call `decEqTy a a'`! Matching
  `Right Refl` unifies `a` and `a'`, so GHC accepts `App l' m'` at type `b`!
- **`RZero` / `RSuc m`**: verify `m` has type `TNat`.
- **`RCase l m n`**: verify `l` has type `TNat`, infer `m`'s type `a` and `n`'s
  type `a'` in `CExt g TNat`, and unify `a` with `a'` via `decEqTy`.
- **`RMu a m`**: infer `m`'s type `a'` in `CExt g a` and verify `a :~: a'`.

Finally, `check` checks a raw term against a caller-supplied runtime type `a`
by running `infer` and comparing the inferred type `a'` with `a`:

```haskell
-- | Certified type inference: given a runtime context `g` and raw term,
-- infer a runtime type `a` and construct an intrinsically-typed `Term g a`.
infer :: foreach (g :: Ctx) -> RawTerm -> Maybe (Typed g)
infer g raw = case raw of
  RVar n -> case lookupCtx g n of
    Nothing          -> Nothing
    Just (Found a p) -> Just (MkTyped a (Var p))
  RLam a body -> case infer (CExt g a) body of
    Nothing                -> Nothing
    Just (MkTyped b body') -> Just (MkTyped (TArr a b) (Lam body'))
  RApp l m -> case infer g l of
    Nothing -> Nothing
    Just (MkTyped lTy l') -> case lTy of
      TNat     -> Nothing
      TArr a b -> case infer g m of
        Nothing -> Nothing
        Just (MkTyped a' m') -> case decEqTy a a' of
          Right Refl -> Just (MkTyped b (App l' m'))
          Left _     -> Nothing
  RZero -> Just (MkTyped TNat Zero)
  RSuc m -> case infer g m of
    Nothing -> Nothing
    Just (MkTyped mTy m') -> case mTy of
      TNat     -> Just (MkTyped TNat (Suc m'))
      TArr _ _ -> Nothing
  RCase l m n -> case infer g l of
    Nothing -> Nothing
    Just (MkTyped lTy l') -> case lTy of
      TArr _ _ -> Nothing
      TNat     -> case infer g m of
        Nothing -> Nothing
        Just (MkTyped a m') -> case infer (CExt g TNat) n of
          Nothing -> Nothing
          Just (MkTyped a' n') -> case decEqTy a a' of
            Right Refl -> Just (MkTyped a (Case l' m' n'))
            Left _     -> Nothing
  RMu a m -> case infer (CExt g a) m of
    Nothing -> Nothing
    Just (MkTyped a' m') -> case decEqTy a a' of
      Right Refl -> Just (MkTyped a (Mu m'))
      Left _     -> Nothing

-- | Certified type checking against an expected runtime type `a`.
check :: foreach (g :: Ctx) -> RawTerm -> foreach (a :: Ty) -> Maybe (Term g a)
check g raw a = case infer g raw of
  Just (MkTyped a' t) -> case decEqTy a a' of
    Right Refl -> Just t
    Left _     -> Nothing
  Nothing -> Nothing

-- | Example raw terms: `λ (x : Nat) -> x` and `2`.
rawIdNat :: RawTerm
rawIdNat = RLam TNat (RVar N.Zero)

rawTwo :: RawTerm
rawTwo = RSuc (RSuc RZero)
```

Notice what happens at runtime (tested in PLFH's executable smoke test):
- `infer CEmpty (RApp rawIdNat rawTwo)` returns `Just (MkTyped TNat (App (Lam (Var Z)) (Suc (Suc Zero))))`!
- `infer CEmpty (RApp RZero rawTwo)` returns `Nothing` (applying `0` to `2` is rejected)!
- `check CEmpty rawTwo TNat` returns `Just (Suc (Suc Zero))`, while `check CEmpty rawTwo (TArr TNat TNat)` returns `Nothing`.

## Bidirectional type inference with decidable soundness and completeness

Church-annotated `RawTerm` forces a type annotation on *every* lambda and
fixpoint, and returning `Maybe` proves only **soundness** (a `Just` result is a
valid derivation), not **completeness** (a `Nothing` result could in principle
be a bug in the checker!).

Following PLFA's full bidirectional design, we now split raw terms into two
mutually recursive grammars:
- **`TermPos` (`Term⁺`)** — *synthesizable* terms whose type flows **up**
  (variables `PVar n`, applications `PApp l m`, and explicit annotations
  `PAnn m a`);
- **`TermNeg` (`Term⁻`)** — *inheritable/checkable* terms whose type flows
  **down** (unannotated lambdas `NLam b`, `NZero`, `NSuc m`, `NCase l m n`,
  unannotated fixpoints `NMu m`, and synthesis-to-inheritance switches `NEmb m`).

Type annotations (`PAnn`) are needed **only** at β-redexes or top-level
declarations—an unannotated lambda `NLam (NEmb (PVar 0))` checks directly
against `TArr TNat TNat`! Moreover:
- `Synth g m a` (`Γ ⊢ M⁺ ↑ A`) and `Inherit g m a` (`Γ ⊢ M⁻ ↓ A`) record
  exact bidirectional derivations, erasing directly to intrinsically-typed
  `DeBruijn.Term g a` via `eraseSynth` / `eraseInherit`;
- `synthUnique` proves that every synthesizable term has at most one type;
- **`synthesize`** returns `SynthDec g m` (either a runtime type `a` with
  `Synth g m a`, or a formal proof `forall a. Not (Synth g m a)` that *no*
  derivation exists!), and **`inherit`** returns `Dec (Inherit g m a)`—certifying
  **both soundness and completeness** under `-Werror=incomplete-patterns`!

```haskell
-- | Bidirectional raw syntax: synthesizable (`Term⁺`) and inheritable (`Term⁻`).
data TermPos
  = PVar N.Nat
  | PApp TermPos TermNeg
  | PAnn TermNeg Ty
  deriving (Show)

data TermNeg
  = NLam TermNeg
  | NZero
  | NSuc TermNeg
  | NCase TermPos TermNeg TermNeg
  | NMu TermNeg
  | NEmb TermPos
  deriving (Show)

-- | Indexed context lookup proof: de Bruijn index `n` has type `a` in `g`.
type LookupAt :: Ctx -> N.Nat -> Ty -> Type
data LookupAt g n a where
  LAZ :: LookupAt (CExt g a) N.Zero a
  LAS :: LookupAt g n a -> LookupAt (CExt g b) (N.Succ n) a

eraseLookupAt :: LookupAt g n a -> Lookup g a
eraseLookupAt LAZ     = Z
eraseLookupAt (LAS p) = S (eraseLookupAt p)

lookupAtUnique :: LookupAt g n a -> LookupAt g n b -> a :~: b
lookupAtUnique LAZ      LAZ      = Refl
lookupAtUnique (LAS p1) (LAS p2) = lookupAtUnique p1 p2

-- | Sound and complete decision for de Bruijn context lookup.
data LookupDec (g :: Ctx) (n :: N.Nat) where
  LookupYes :: foreach (a :: Ty) -> LookupAt g n a -> LookupDec g n
  LookupNo  :: (forall (a :: Ty). Not (LookupAt g n a)) -> LookupDec g n

lookupDec :: foreach (g :: Ctx) -> foreach (n :: N.Nat) -> LookupDec g n
lookupDec CEmpty     = \_ -> LookupNo (\case {})
lookupDec (CExt g a) = \n -> case n of
  N.Zero    -> LookupYes a LAZ
  N.Succ n' -> case lookupDec g n' of
    LookupYes b p -> LookupYes b (LAS p)
    LookupNo neg  -> LookupNo (\(LAS p) -> neg p)

-- | Bidirectional typing derivations: synthesis (`Γ ⊢ M⁺ ↑ A`) and inheritance (`Γ ⊢ M⁻ ↓ A`).
type Synth :: Ctx -> TermPos -> Ty -> Type
data Synth g m a where
  SVar :: LookupAt g n a -> Synth g (PVar n) a
  SApp :: Synth g l (TArr a b) -> Inherit g m a -> Synth g (PApp l m) b
  SAnn :: Inherit g m a -> Synth g (PAnn m a) a

type Inherit :: Ctx -> TermNeg -> Ty -> Type
data Inherit g m a where
  ILam  :: Inherit (CExt g a) body b -> Inherit g (NLam body) (TArr a b)
  IZero :: Inherit g NZero TNat
  ISuc  :: Inherit g m TNat -> Inherit g (NSuc m) TNat
  ICase :: Synth g l TNat -> Inherit g m a -> Inherit (CExt g TNat) n a -> Inherit g (NCase l m n) a
  IMu   :: Inherit (CExt g a) m a -> Inherit g (NMu m) a
  IEmb  :: Synth g m a -> Inherit g (NEmb m) a

-- | Erase bidirectional derivations to intrinsically-typed `DeBruijn.Term g a`.
eraseSynth :: Synth g m a -> Term g a
eraseSynth (SVar p)   = Var (eraseLookupAt p)
eraseSynth (SApp l m) = App (eraseSynth l) (eraseInherit m)
eraseSynth (SAnn m)   = eraseInherit m

eraseInherit :: Inherit g m a -> Term g a
eraseInherit (ILam b)      = Lam (eraseInherit b)
eraseInherit IZero         = Zero
eraseInherit (ISuc m)      = Suc (eraseInherit m)
eraseInherit (ICase l m n) = Case (eraseSynth l) (eraseInherit m) (eraseInherit n)
eraseInherit (IMu m)       = Mu (eraseInherit m)
eraseInherit (IEmb m)      = eraseSynth m

-- | Synthesized types are unique (required for completeness refutations).
synthUnique :: Synth g m a -> Synth g m b -> a :~: b
synthUnique (SVar p1)   (SVar p2)   = lookupAtUnique p1 p2
synthUnique (SApp l1 _) (SApp l2 _) = case synthUnique l1 l2 of Refl -> Refl
synthUnique (SAnn _)    (SAnn _)    = Refl

-- | Sound and complete synthesis decision (`Dec (∃ A. Γ ⊢ M⁺ ↑ A)`).
data SynthDec (g :: Ctx) (m :: TermPos) where
  SynthYes :: foreach (a :: Ty) -> Synth g m a -> SynthDec g m
  SynthNo  :: (forall (a :: Ty). Not (Synth g m a)) -> SynthDec g m

-- | Refutation helpers for completeness branches (purely erased `Synth`/`Inherit`).
noAppNat :: Synth g l TNat -> Not (Synth g (PApp l arg) r)
noAppNat dl (SApp dl' _) = case synthUnique dl dl' of {}

noAppArg :: Synth g l (TArr a b) -> Not (Inherit g arg a) -> Not (Synth g (PApp l arg) r)
noAppArg dl negArg (SApp dl' dArg') = case synthUnique dl dl' of Refl -> negArg dArg'

noCaseArr :: Synth g l (TArr a b) -> Not (Inherit g (NCase l m n) r)
noCaseArr dl (ICase dl' _ _) = case synthUnique dl dl' of {}

noEmbSynth :: (forall (b :: Ty). Not (Synth g e b)) -> Not (Inherit g (NEmb e) a)
noEmbSynth negE (IEmb de) = negE de

noEmbNeq :: Synth g e a' -> Not (a :~: a') -> Not (Inherit g (NEmb e) a)
noEmbNeq de neq (IEmb de') = neq (synthUnique de' de)

-- | Sound and complete bidirectional type synthesis (`synthesize`).
synthesize :: foreach (g :: Ctx) -> foreach (m :: TermPos) -> SynthDec g m
synthesize g = \m -> case m of
  PVar n -> case lookupDec g n of
    LookupYes a p -> SynthYes a (SVar p)
    LookupNo neg  -> SynthNo (\(SVar p) -> neg p)
  PApp l arg -> case synthesize g l of
    SynthNo negL -> SynthNo (\(SApp dl _) -> negL dl)
    SynthYes lTy dl -> case lTy of
      TNat -> SynthNo (noAppNat dl)
      TArr a b -> case inherit g arg a of
        Yes dArg  -> SynthYes b (SApp dl dArg)
        No negArg -> SynthNo (noAppArg dl negArg)
  PAnn body a -> case inherit g body a of
    Yes dBody  -> SynthYes a (SAnn dBody)
    No negBody -> SynthNo (\(SAnn dBody') -> negBody dBody')

-- | Sound and complete bidirectional type checking (`inherit`).
inherit :: foreach (g :: Ctx) -> foreach (m :: TermNeg) -> foreach (a :: Ty) -> Dec (Inherit g m a)
inherit g = \m -> \a -> case m of
  NLam body -> case a of
    TNat       -> No (\case {})
    TArr a1 a2 -> case inherit (CExt g a1) body a2 of
      Yes dBody  -> Yes (ILam dBody)
      No negBody -> No (\(ILam dBody') -> negBody dBody')
  NZero -> case a of
    TNat     -> Yes IZero
    TArr _ _ -> No (\case {})
  NSuc k -> case a of
    TArr _ _ -> No (\case {})
    TNat     -> case inherit g k TNat of
      Yes dk  -> Yes (ISuc dk)
      No negK -> No (\(ISuc dk') -> negK dk')
  NCase l m0 n -> case synthesize g l of
    SynthNo negL -> No (\(ICase dl _ _) -> negL dl)
    SynthYes lTy dl -> case lTy of
      TArr _ _ -> No (noCaseArr dl)
      TNat -> case inherit g m0 a of
        No negM -> No (\(ICase _ dm _) -> negM dm)
        Yes dm  -> case inherit (CExt g TNat) n a of
          No negN -> No (\(ICase _ _ dn) -> negN dn)
          Yes dn  -> Yes (ICase dl dm dn)
  NMu body -> case inherit (CExt g a) body a of
    Yes dBody  -> Yes (IMu dBody)
    No negBody -> No (\(IMu dBody') -> negBody dBody')
  NEmb e -> case synthesize g e of
    SynthNo negE -> No (noEmbSynth negE)
    SynthYes a' de -> case decEqTy a a' of
      Right Refl -> Yes (IEmb de)
      Left neq   -> No (noEmbNeq de neq)

-- | Bidirectional example: `((λx. x) ↓ (Nat -> Nat)) · 2` (note the lambda
-- itself carries NO parameter annotation!).
bidirIdAppTwo :: TermPos
bidirIdAppTwo = PApp (PAnn (NLam (NEmb (PVar N.Zero))) (TArr TNat TNat)) (NSuc (NSuc NZero))
```

## Exercises

#### Exercise `erase` and round-trip soundness (recommended)

Define an erasure function `erase :: Term g a -> RawTerm` (or bidirectional
erasure to `TermNeg`) and check that `synthesize` / `inherit` recover an
equivalent intrinsically-typed derivation.

#### Exercise `Inference-errors` (practice)

Strengthen the `No` / `SynthNo` branches of `synthesize` and `inherit` so they
carry structured diagnostic messages alongside their formal refutation proofs.

## Changes from PLFA

- Adapted from [Inference](https://plfa.inf.ed.ac.uk/Inference/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part2/Inference.lagda.md)),
  licensed under CC BY 4.0.
- Implements **both** the introductory Church-annotated `infer`/`check` (`Maybe`)
  **and** PLFA's full **sound and complete bidirectional `Dec`-based type
  checker** (`TermPos`/`TermNeg`, `LookupAt`/`lookupDec`, `Synth`/`Inherit`,
  `eraseSynth`/`eraseInherit`, `synthUnique`, `synthesize`, and `inherit`)
  over de Bruijn STLC terms, compiled with `-Werror=incomplete-patterns`,
  `-dcore-lint -dstg-lint`, and zero promoted-constructor ticks.
