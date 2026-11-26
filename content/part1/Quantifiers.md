---
title: "Quantifiers: Universals and existentials"
prev: /Negation/
next: /Decidable/
src: content/part1/Quantifiers.md
module: PLFH.Part1.Quantifiers
plfaChapter: https://plfa.inf.ed.ac.uk/Quantifiers/
---

This chapter introduces **universal** (`∀`) and **existential** (`∃` / `Σ`)
quantification under *Propositions as Types*.

In Agda, both quantifiers are uniform dependent types: universal
quantification is the dependent function type `(x : A) → B x`, and
existential quantification is the dependent pair (dependent sum) type
`Σ[ x ∈ A ] B x`. In Dependent Haskell we distinguish explicitly between
**erased** (compile-time only) and **retained** (runtime + type-level)
quantifiers:

1. **Universals:** erased `forall (x :: a). p x` vs. retained
   `foreach (x :: a) -> p x`.
2. **Existentials:** erased `GHC.Exists.Exists p` (native Proposal `#473`
   `exists x | p x`, hiding a type-level witness `x :: a` erased at runtime,
   with combinators re-exported by `Data.Exists.Dependent`) vs.
   retained dependent pairs `GHC.Sigma.Sigma` (`some (x :: a) | p x`, or a GADT
   constructor carrying `foreach (x :: a) -> ...`), where the witness is
   available both at runtime and in types!

## Imports

We import `Type`, `(:~:)`, `GHC.Sigma`, `GHC.Exists`/`Data.Exists.Dependent`,
`rewrite` from `Data.Type.Equality.Dependent`, `Nat` and addition helpers from
`Data.Nat.Dependent`/`Data.Nat.Dependent.Properties`, unified `cong` from
[Induction](/Induction/), `Not` from [Decidable](/Decidable/), `Iff` from
[Isomorphism](/Isomorphism/), and `Even`/`Odd` from [Relations](/Relations/).

```haskell
{-# LANGUAGE DependentTypes, ListTuplePuns, UndecidableInstances #-}
module PLFH.Part1.Quantifiers
  ( Exists
  , SumPred (..)
  , existsDistribSum
  , existsCurryTo
  , existsCurryFrom
  , Forall (..)
  , ProdPred (..)
  , forallDistribProd
  , notExistsToForallNot
  , forallNotToNotExists
  , EvenSigma
  , evenZeroSigma
  , evenTwoSigma
  , SumSigma
  , sumSigmaTwo
  , EvenWitness (..)
  , evenWitnessZero
  , evenWitnessSuc2
  , evenDouble
  , evenToWitness
  , witnessToEven
  , evenIffWitness
  , OddWitness (..)
  , oddToWitness
  , witnessToOdd
  , oddIffWitness
  ) where

import Data.Exists.Dependent (data Pack, mapExists, withExists)
import Data.Kind (Type)
import Data.Nat.Dependent (Nat (..), plus)
import Data.Nat.Dependent.Properties (plusSucc)
import Data.Type.Equality ((:~:) (Refl))
import Data.Type.Equality.Dependent (rewrite)
import GHC.Exists (Exists)
import GHC.Sigma (Sigma (Pair))
import PLFH.Part1.Decidable (Not)
import PLFH.Part1.Induction (cong)
import PLFH.Part1.Isomorphism (Iff (..))
import PLFH.Part1.Relations (Even (..), Odd (..))
```

## Universals (`∀`)

We have been using universal quantification throughout Part 1—for instance,
in [Induction](/Induction/) we proved:

```text
plusAssoc :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
          -> plus (plus m n) p :~: plus m (plus n p)
```

Given a type `a` and a family of propositions `p :: a -> Type`, a proof of
the universally quantified proposition `forall (x :: a). p x` (or
`foreach (x :: a) -> p x` when `x` is inspected at runtime) is a **dependent
function** mapping any element `m :: a` to evidence of `p m`.

- **Introduction:** lambda abstraction `\x -> body`.
- **Elimination:** function application `f m` (generalizing *modus ponens*).

Ordinary implication `a -> b` is simply the special case where the return
type `b` does not mention the argument `x`. Dependent function types are
often called **dependent products** (`Π`), because if `a` is a finite type
with values `x₁, …, xₙ` and each `p xᵢ` has `mᵢ` inhabitants, then the
dependent function type has `m₁ × ⋯ × mₙ` inhabitants.

## Existentials (`∃` / `Σ`)

Dually, given a predicate `p :: a -> Type`, the existentially quantified
proposition *"there exists `x :: a` such that `p x`"* is evidenced by a
**dependent pair** bundling a witness `x` together with a proof of `p x`.

Dependent pair types are called **dependent sums** (`Σ`), because if `a` has
elements `x₁, …, xₙ` and each `p xᵢ` has `mᵢ` inhabitants, then the
dependent pair type has `m₁ + ⋯ + mₙ` inhabitants. Ordinary conjunction
`(a, b)` is the special case where `b` does not depend on the first component.

### Algebraic laws of `Exists` and `Forall`

Over an erased existential `Exists p` and a first-class universal `Forall p`,
all of PLFA's quantifier distribution, currying, and De Morgan laws hold
directly:

- **Existentials distribute over disjunction (`∃-distrib-⊎`):**
  `(∃ x. P x ∨ Q x) ⇔ (∃ x. P x) ∨ (∃ x. Q x)`.
- **Existential currying (`∀∃-currying`):**
  `((∃ x. P x) -> C) ⇔ (∀ x. P x -> C)`—just like `((a, b) -> c) ⇔ (a -> b -> c)`.
- **Universals distribute over conjunction (`∀-distrib-×`):**
  `(∀ x. P x ∧ Q x) ⇔ (∀ x. P x) ∧ (∀ x. Q x)`.
- **Quantifier De Morgan:**
  `¬(∃ x. P x) ⇔ ∀ x. ¬(P x)`.

```haskell
-- | Pointwise disjunction of predicates.
data SumPred (p :: a -> Type) (q :: a -> Type) (x :: a) where
  InL :: p x -> SumPred p q x
  InR :: q x -> SumPred p q x

-- | Existentials distribute over disjunction (`∃-distrib-⊎`):
-- (∃ x. P x ∨ Q x) ⇔ (∃ x. P x) ∨ (∃ x. Q x).
existsDistribSum
  :: forall a (p :: a -> Type) (q :: a -> Type).
     Iff (Exists (SumPred p q)) (Either (Exists p) (Exists q))
existsDistribSum = Iff toF fromF
  where
    packP :: forall (x :: a). p x -> Exists p
    packP px = Pack (type x) px

    packQ :: forall (x :: a). q x -> Exists q
    packQ qx = Pack (type x) qx

    toF :: Exists (SumPred p q) -> Either (Exists p) (Exists q)
    toF pkg = case pkg of
      Pack (type _) s -> case s of
        InL px -> Left (packP px)
        InR qx -> Right (packQ qx)

    fromF :: Either (Exists p) (Exists q) -> Exists (SumPred p q)
    fromF (Left pkg)  = mapExists (\_ px -> InL px) pkg
    fromF (Right pkg) = mapExists (\_ qx -> InR qx) pkg

-- | Currying for existentials (`∀∃-currying`): ((∃ x. P x) -> C) ⇔ (∀ x. P x -> C).
existsCurryTo
  :: forall a (p :: a -> Type) c.
     (Exists p -> c) -> (forall x. p x -> c)
existsCurryTo f (px :: p x) = f (Pack (type x) px)

existsCurryFrom
  :: forall a (p :: a -> Type) c.
     (forall x. p x -> c) -> (Exists p -> c)
existsCurryFrom g pkg = withExists pkg $ \_ px -> g px

-- | First-class wrapper for universal quantification and pointwise conjunction.
newtype Forall (p :: a -> Type) = MkForall { unForall :: forall x. p x }
newtype ProdPred (p :: a -> Type) (q :: a -> Type) (x :: a) =
  MkProdPred { unProdPred :: (p x, q x) }

-- | Universals distribute over conjunction (`∀-distrib-×`):
-- (∀ x. P x ∧ Q x) ⇔ (∀ x. P x) ∧ (∀ x. Q x).
forallDistribProd :: Iff (Forall (ProdPred p q)) (Forall p, Forall q)
forallDistribProd =
  Iff (\f -> ( MkForall (fst (unProdPred (unForall f)))
             , MkForall (snd (unProdPred (unForall f))) ))
      (\(fp, fq) -> MkForall (MkProdPred (unForall fp, unForall fq)))

-- | De Morgan for quantifiers: ¬(∃ x. P x) ⇔ ∀ x. ¬(P x).
notExistsToForallNot
  :: forall a (p :: a -> Type).
     Not (Exists p) -> (forall x. Not (p x))
notExistsToForallNot ne (px :: p x) = ne (Pack (type x) px)

forallNotToNotExists
  :: forall a (p :: a -> Type).
     (forall x. Not (p x)) -> Not (Exists p)
forallNotToNotExists fn pkg = withExists pkg $ \_ px -> fn px
```

## An existential example: `Even` and `Odd` as doubles

Recall the mutually inductive predicates `Even n` and `Odd n` from
[Relations](/Relations/). PLFA shows that a natural number is even if and
only if it is twice some natural `k`, and odd if and only if it is one more
than twice some natural `k`:

- `Even n  ⇔  ∃ k. k + k = n`
- `Odd n   ⇔  ∃ k. Succ (k + k) = n`

With GHC's retained dependent sum (`some (k :: Nat) | plus k k :~: n`,
requiring `UndecidableInstances` because the desugared type-lambda family
calls `plus k k`), we can write `EvenSigma`—as well as multi-binder sums like
`SumSigma` (`some (m k :: Nat) | plus m k :~: n`, desugaring right-associatively
to nested `Sigma` pairs)—directly using decimal numerals:

```haskell
-- | Retained dependent sum: there exists a runtime `k` with `k + k = n`.
type EvenSigma (n :: Nat) = some (k :: Nat) | plus k k :~: n

evenZeroSigma :: EvenSigma 0
evenZeroSigma = Pair Zero Refl

evenTwoSigma :: EvenSigma 2
evenTwoSigma = Pair 1 Refl

-- | Multi-binder retained sum: there exist runtime `m` and `k` with `m + k = n`.
type SumSigma (n :: Nat) = some (m k :: Nat) | plus m k :~: n

sumSigmaTwo :: SumSigma 2
sumSigmaTwo = Pair 1 (Pair 1 Refl)
```

Packaging the exact same retained witness as `EvenWitness n` and `OddWitness n`
(carrying `foreach (k :: Nat)` so the half `k` is available at runtime!), we
prove **both directions** of both equivalences (`evenIffWitness` and
`oddIffWitness`), using unified `cong Succ` and `rewrite (plusSucc k k)`:

```haskell
-- | Retained existential witness that `n` is double some runtime `k`.
data EvenWitness (n :: Nat) where
  MkEvenWitness :: foreach (k :: Nat) -> plus k k :~: n -> EvenWitness n

evenWitnessZero :: EvenWitness Zero
evenWitnessZero = MkEvenWitness Zero Refl

evenWitnessSuc2 :: EvenWitness n -> EvenWitness (Succ (Succ n))
evenWitnessSuc2 (MkEvenWitness k Refl) =
  MkEvenWitness (Succ k) (cong Succ (plusSucc k k))

-- | Every double `k + k` is even (proved directly using `rewrite`).
evenDouble :: foreach (k :: Nat) -> Even (plus k k)
evenDouble Zero     = EvenZ
evenDouble (Succ k) = rewrite (plusSucc k k) (EvenS (OddS (evenDouble k)))

-- | Every inductive `Even n` derivation yields a runtime half `k` with `k + k = n`.
evenToWitness :: Even n -> EvenWitness n
evenToWitness EvenZ              = evenWitnessZero
evenToWitness (EvenS (OddS evn)) = evenWitnessSuc2 (evenToWitness evn)

-- | Converse: a runtime witness `k + k = n` reconstructs `Even n`.
witnessToEven :: EvenWitness n -> Even n
witnessToEven (MkEvenWitness k Refl) = evenDouble k

-- | Full bi-implication: `Even n ⇔ (∃ k. k + k = n)`.
evenIffWitness :: Iff (Even n) (EvenWitness n)
evenIffWitness = Iff evenToWitness witnessToEven

-- | Retained existential witness that `n = Succ (k + k)` for some runtime `k`.
data OddWitness (n :: Nat) where
  MkOddWitness :: foreach (k :: Nat) -> Succ (plus k k) :~: n -> OddWitness n

oddToWitness :: Odd n -> OddWitness n
oddToWitness (OddS ev) = case evenToWitness ev of
  MkEvenWitness k Refl -> MkOddWitness k Refl

witnessToOdd :: OddWitness n -> Odd n
witnessToOdd (MkOddWitness k Refl) = OddS (evenDouble k)

-- | Full bi-implication: `Odd n ⇔ (∃ k. Succ (k + k) = n)`.
oddIffWitness :: Iff (Odd n) (OddWitness n)
oddIffWitness = Iff oddToWitness witnessToOdd
```

## Exercises

#### Exercise `⊎∀-implies-∀⊎` and `∃×-implies-×∃` (practice)

Show constructively that:

1. `Either (Forall p) (Forall q) -> Forall (SumPred p q)` (a disjunction of
   universals implies a universal of disjunctions). Does the converse hold?
2. `Exists (ProdPred p q) -> (Exists p, Exists q)` (an existential of
   conjunctions implies a conjunction of existentials). Why does the converse
   fail? (Think of `p = Even` and `q = Odd`!)

#### Exercise `∀-×` and `∃-⊎` on `Tri` (practice)

Given a 3-element datatype `data Tri = AA | BB | CC` and an indexed predicate
(GADT) `b :: Tri -> Type`, explain why `foreach (x :: Tri) -> b x` behaves like
the triple `(b AA, b BB, b CC)` while a **retained** dependent sum
`some (x :: Tri) | b x` (unlike erased `Exists b`, whose tag `x` cannot be
inspected at runtime!) behaves like the 3-way sum
`Either (b AA) (Either (b BB) (b CC))`.

## Changes from PLFA

- Adapted from [Quantifiers](https://plfa.inf.ed.ac.uk/Quantifiers/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part1/Quantifiers.lagda.md)),
  licensed under CC BY 4.0.
- Contrasts native Proposal `#473` erased existentials (`GHC.Exists.Exists` / `Data.Exists.Dependent`)
  with retained `GHC.Sigma` (`some ... | ...`)
  and `foreach`-carrying GADT witnesses (`EvenWitness`, `OddWitness`).
- Ports `existsDistribSum`, `existsCurryTo`/`From`,
  `forallDistribProd`, quantifier De Morgan (`notExistsToForallNot`,
  `forallNotToNotExists`), `EvenSigma`, and both directions of the parity
  witness equivalences (`evenIffWitness`, `oddIffWitness`), using unified
  `cong Succ`.
