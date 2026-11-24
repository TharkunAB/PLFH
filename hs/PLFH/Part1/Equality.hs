-- Generated from content/part1/Equality.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE AllowAmbiguousTypes, DataKinds, ExperimentalDependentTypes #-}
{-# LANGUAGE GADTs, Modifiers, PolyKinds, RankNTypes, RequiredTypeArguments #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications, TypeOperators #-}
{-# LINE 14 "content/part1/Equality.md" #-}
module PLFH.Part1.Equality
  ( EqP (..)
  , symP
  , transP
  , congP
  , congAppP
  , substP
  , substU
  , beginEq
  , stepEq
  , qedEq
  , plusZeroChain
  , Leibniz
  , leibnizRefl
  , leibnizTrans
  , eqToLeibniz
  , leibnizToEq
  , LeibnizU
  , leibnizUSym
  , leibnizUToEq
  , evenComm
  ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import GHC.Exts (U)
import HaskLib (rewrite)
import HaskLib.Size (Size (..), congSucc, plus)
import PLFH.Part1.Induction (plusComm)
import PLFH.Part1.Relations (Even (..))

{-# LINE 60 "content/part1/Equality.md" #-}
-- | Kind-polymorphic propositional equality (matching Data.Type.Equality.:~:).
data EqP (x :: a) (y :: a) where
  ReflP :: EqP x x

{-# LINE 70 "content/part1/Equality.md" #-}
-- | Symmetry: if x = y then y = x.
symP :: EqP x y -> EqP y x
symP ReflP = ReflP

-- | Transitivity: if x = y and y = z then x = z.
transP :: EqP x y -> EqP y z -> EqP x z
transP ReflP q = q

{-# LINE 93 "content/part1/Equality.md" #-}
-- | Congruence: equal inputs yield equal outputs under any unmatchable function f.
congP :: forall {a} {b} (f :: a %U -> b) (x :: a) (y :: a).
         EqP x y -> EqP (f x) (f y)
congP ReflP = ReflP

-- | Application congruence: equal functions yield equal results at any input x.
congAppP :: forall {a} {b} (f :: a %U -> b) (g :: a %U -> b) (x :: a).
            EqP f g -> EqP (f x) (g x)
congAppP ReflP = ReflP

-- | Substitution for matchable predicates (e.g. GADTs like `Even`).
substP :: forall {a} (p :: a -> Type) (x :: a) (y :: a).
          EqP x y -> p x -> p y
substP ReflP px = px

-- | Substitution for unmatchable predicates (e.g. type lambdas or promoted functions).
substU :: forall {a} (p :: a %U -> Type) (x :: a) (y :: a).
          EqP x y -> p x -> p y
substU ReflP px = px

{-# LINE 121 "content/part1/Equality.md" #-}
-- | If m + n is even, then n + m is even.
evenComm :: foreach (m :: Size) -> foreach (n :: Size)
         -> Even (plus m n) -> Even (plus n m)
evenComm m n ev = rewrite (plusComm m n) ev

{-# LINE 151 "content/part1/Equality.md" #-}
-- | Start an equational reasoning chain from `x` to `y`.
beginEq :: forall x y -> x :~: y -> x :~: y
beginEq _ _ p = p

-- | End an equational reasoning chain at `x`.
qedEq :: forall x -> x :~: x
qedEq _ = Refl

-- | One reasoned step: from `x` to `y` by `p`, followed by `y` to `z`.
stepEq :: forall x y z -> x :~: y -> y :~: z -> x :~: z
stepEq _ _ _ Refl Refl = Refl

-- | Example equational chain proving `n + 0 = n`.
plusZeroChain :: foreach (n :: Size) -> plus n 'Zero :~: n
plusZeroChain Zero     = beginEq (type (plus 'Zero 'Zero)) (type 'Zero) (qedEq (type 'Zero))
plusZeroChain (Succ n) =
  stepEq (type (plus ('Succ n) 'Zero)) (type ('Succ (plus n 'Zero))) (type ('Succ n))
    Refl
    (stepEq (type ('Succ (plus n 'Zero))) (type ('Succ n)) (type ('Succ n))
      (congSucc (plusZeroChain n))
      (qedEq (type ('Succ n))))

{-# LINE 184 "content/part1/Equality.md" #-}
-- | Leibniz equality over matchable predicates `p :: a -> Type`.
type Leibniz (x :: a) (y :: a) = forall (p :: a -> Type). p x -> p y

leibnizRefl :: Leibniz x x
leibnizRefl px = px

leibnizTrans :: forall {a} (x :: a) (y :: a) (z :: a).
                Leibniz x y -> Leibniz y z -> Leibniz x z
leibnizTrans xy yz px = yz (xy px)

eqToLeibniz :: EqP x y -> Leibniz x y
eqToLeibniz ReflP px = px

leibnizToEq :: forall {a} (x :: a) (y :: a). Leibniz x y -> EqP x y
leibnizToEq f = f @(EqP x) ReflP

{-# LINE 207 "content/part1/Equality.md" #-}
-- | Leibniz equality over unmatchable predicates `p :: a %U -> Type`.
type LeibnizU (x :: a) (y :: a) = forall (p :: a %U -> Type). p x -> p y

-- | Symmetry of LeibnizU using an inline type-level lambda (R17)!
leibnizUSym :: forall {a} (x :: a) (y :: a). LeibnizU x y -> LeibnizU y x
leibnizUSym xy = case xy @(\z -> EqP z x) ReflP of
  ReflP -> \px -> px

-- | Recovering EqP from LeibnizU via an inline type-level lambda.
leibnizUToEq :: forall {a} (x :: a) (y :: a). LeibnizU x y -> EqP x y
leibnizUToEq f = f @(\z -> EqP x z) ReflP
