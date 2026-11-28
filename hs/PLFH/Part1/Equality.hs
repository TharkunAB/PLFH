-- Generated from content/part1/Equality.md by scripts/extract_and_sync.hs
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE AllowAmbiguousTypes, DependentTypes #-}
{-# LINE 31 "content/part1/Equality.md" #-}
module PLFH.Part1.Equality
  ( EqP (..)
  , toEqP
  , symP
  , transP
  , congP
  , cong2P
  , congAppP
  , substP
  , beginEq
  , stepEq
  , qedEq
  , plusZeroChain
  , plusCommRewrite
  , beginLE
  , stepLE
  , qedLE
  , Leibniz
  , leibnizRefl
  , leibnizSymAt
  , leibnizSym
  , leibnizTrans
  , eqToLeibniz
  , leibnizToEq
  , evenComm
  ) where

import Data.Kind (Type)
import Data.Nat.Dependent (Nat (..), plus)
import Data.Type.Equality ((:~:) (Refl))
import Data.Type.Equality.Dependent (Matchability, rewrite)
import GHC.Exts (U)
import PLFH.Part1.Induction (cong, plusComm, plusIdentityR, plusSuc)
import PLFH.Part1.Relations (Even (..), LE (..), leTrans)

{-# LINE 74 "content/part1/Equality.md" #-}
-- | Kind-polymorphic propositional equality (matching Data.Type.Equality.:~:).
data EqP (x :: a) (y :: a) where
  ReflP :: EqP x x

{-# LINE 92 "content/part1/Equality.md" #-}
-- | Symmetry: if x = y then y = x.
symP :: EqP x y -> EqP y x
symP ReflP = ReflP

-- | Transitivity: if x = y and y = z then x = z.
transP :: EqP x y -> EqP y z -> EqP x z
transP ReflP q = q

{-# LINE 131 "content/part1/Equality.md" #-}
-- | Agda-style matchability-polymorphic congruence: works for both constructors
-- (`congP Succ`) and promoted functions (`congP (plus m)`).
congP :: forall {a} {b} {m :: Matchability}.
         forall (f :: a %m -> b) -> forall (x :: a) (y :: a).
         EqP x y -> EqP (f x) (f y)
congP _ ReflP = ReflP

-- | Two-argument congruence (`cong₂`): equal arguments yield equal binary results.
cong2P :: forall {a} {b} {c} {m1 m2 :: Matchability}.
          forall (f :: a %m1 -> b %m2 -> c) -> forall (x :: a) (x' :: a) (y :: b) (y' :: b).
          EqP x x' -> EqP y y' -> EqP (f x y) (f x' y')
cong2P _ ReflP ReflP = ReflP

-- | Application congruence: equal functions yield equal results at any input x.
congAppP :: forall {a} {b} {m :: Matchability} (f :: a %m -> b) (g :: a %m -> b) (x :: a).
            EqP f g -> EqP (f x) (g x)
congAppP ReflP = ReflP

-- | Substitution for any predicate `p :: a %U -> Type` (matchable GADTs like `Even`
-- as well as unmatchable type lambdas or promoted functions).
substP :: forall {a} (p :: a %U -> Type) (x :: a) (y :: a).
          EqP x y -> p x -> p y
substP ReflP px = px

{-# LINE 163 "content/part1/Equality.md" #-}
-- | Convert standard `Data.Type.Equality.:~:` into our local `EqP`.
toEqP :: x :~: y -> EqP x y
toEqP Refl = ReflP

-- | If m + n is even, then n + m is even (PLFA's direct `subst even (+-comm m n)`).
evenComm :: foreach (m n :: Nat)
         -> Even (plus m n) -> Even (plus n m)
evenComm m n ev = substP @Even (toEqP (plusComm m n)) ev

{-# LINE 193 "content/part1/Equality.md" #-}
-- | Start an equational reasoning chain from `x` to `y`.
beginEq :: forall x y -> x :~: y -> x :~: y
beginEq _ _ p = p

-- | End an equational reasoning chain at `x`.
qedEq :: forall x -> x :~: x
qedEq _ = Refl

-- | One reasoned step: from `x` to `y` by `p`, followed by `y` to `z`.
stepEq :: forall x y z -> x :~: y -> y :~: z -> x :~: z
stepEq _ _ _ Refl Refl = Refl

{-# LINE 210 "content/part1/Equality.md" #-}
-- | Example equational chain proving `n + 0 = n`.
plusZeroChain :: foreach (n :: Nat) -> plus n Zero :~: n
plusZeroChain Zero     = beginEq (type (plus Zero Zero)) (type Zero) (qedEq (type Zero))
plusZeroChain (Succ n) =
  stepEq (type (plus (Succ n) Zero)) (type (Succ (plus n Zero))) (type (Succ n))
    Refl
    (stepEq (type (Succ (plus n Zero))) (type (Succ n)) (type (Succ n))
      (cong Succ (plusZeroChain n))
      (qedEq (type (Succ n))))

{-# LINE 236 "content/part1/Equality.md" #-}
-- | Multiple rewrites in one equation: `plus m (Succ n) = Succ (plus n m)` (`+-comm′`).
plusCommRewrite :: foreach (m n :: Nat) -> plus m n :~: plus n m
plusCommRewrite m Zero     = plusIdentityR m
plusCommRewrite m (Succ n) =
  rewrite (plusSuc m n) (rewrite (plusCommRewrite m n) Refl)

-- | Order-reasoning chains (`≤-Reasoning`) for `LE`.
beginLE :: forall (m n :: Nat) -> LE m n -> LE m n
beginLE _ _ p = p

qedLE :: foreach (n :: Nat) -> LE n n
qedLE Zero     = ZleN
qedLE (Succ n) = SleS (qedLE n)

stepLE :: forall (m n p :: Nat) -> LE m n -> LE n p -> LE m p
stepLE _ _ _ = leTrans

{-# LINE 288 "content/part1/Equality.md" #-}
-- | Leibniz equality over predicates `p :: a %U -> Type`
-- (accepts both matchable constructors like `EqP x` and type-level lambdas).
type Leibniz (x :: a) (y :: a) = forall (p :: a %U -> Type). p x -> p y

-- | Reflexivity of Leibniz equality is the identity function.
leibnizRefl :: Leibniz x x
leibnizRefl px = px

-- | Pure impredicative symmetry of Leibniz at a given predicate `p` (`sym-≐`):
-- instantiates `xy` with `@(\z -> p z -> p x)` and passes `\px -> px` (no `EqP` detour!).
leibnizSymAt :: forall {a} (x :: a) (y :: a) (p :: a %U -> Type).
                Leibniz x y -> p y -> p x
leibnizSymAt xy = xy @(\z -> p z -> p x) (\px -> px)

-- | Symmetry of Leibniz equality (`sym-≐`).
leibnizSym :: forall {a} (x :: a) (y :: a). Leibniz x y -> Leibniz y x
leibnizSym xy = leibnizSymAt @x @y xy

-- | Transitivity of Leibniz equality is function composition.
leibnizTrans :: forall {a} (x :: a) (y :: a) (z :: a).
                Leibniz x y -> Leibniz y z -> Leibniz x z
leibnizTrans xy yz px = yz (xy px)

-- | Martin-Löf equality implies Leibniz equality (indiscernibility of identicals).
eqToLeibniz :: EqP x y -> Leibniz x y
eqToLeibniz ReflP px = px

-- | Leibniz equality implies Martin-Löf equality (identity of indiscernibles):
-- instantiates `p :: a %U -> Type` directly with the matchable constructor `@(EqP x)`!
leibnizToEq :: forall {a} (x :: a) (y :: a). Leibniz x y -> EqP x y
leibnizToEq f = f @(EqP x) ReflP
