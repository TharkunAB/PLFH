---
title: "Naturals: Natural numbers"
prev: /Setup/
next: /Induction/
src: content/part1/Naturals.md
module: PLFH.Part1.Naturals
plfaChapter: https://plfa.inf.ed.ac.uk/Naturals/
---

```haskell
{-# LANGUAGE DataKinds, ExplicitNamespaces, ExperimentalDependentTypes, GADTs, TypeOperators #-}
module PLFH.Part1.Naturals
  ( Nat (..)
  , plus
  , type (+)
  , times
  , monus
  , pow
  , Bin (..)
  , inc
  , toBin
  , fromBin
  , twoPlusThree
  , twoPlusThreeInfix
  , fiveAtRuntime
  , twoTimesThree
  , threePowFour
  , threeMonusTwo
  , twoMonusThree
  ) where

import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..), plus, type (+))
```

The night sky holds more stars than I can count, though fewer than five
thousand are visible to the naked eye. The observable universe contains
about seventy sextillion stars.

But the number of stars is finite, while natural numbers are infinite.
Count all the stars, and you will still have as many natural numbers
left over as you started with.

## The naturals are an inductive datatype

Everyone is familiar with the natural numbers

```text
0
1
2
3
...
```

and so on. We write `Nat` for the *type* of natural numbers, and say that
`0`, `1`, `2`, `3`, and so on are *values* of type `Nat`, indicated by
writing `0 :: Nat`, `1 :: Nat`, `2 :: Nat`, `3 :: Nat`, and so on.

The set of natural numbers is infinite, yet we can write down its
definition in just a few lines. Here is the definition as a pair of
inference rules:

<div class="inference-rule">
  <div class="premises">&nbsp;</div>
  <div class="conclusion">Zero :: Nat</div>
</div>
<div class="inference-rule">
  <div class="premises">m :: Nat</div>
  <div class="conclusion">Succ m :: Nat</div>
</div>

And here is the definition in Dependent Haskell (reused directly from
`HaskLib.Nat` so all chapters share one `Nat` type and decimal-numeral
instances):

```{.haskell .ignore}
data Nat where
  Zero :: Nat
  Succ :: Nat -> Nat
```

Here `Nat` is the name of the *datatype* we are defining, and `Zero` and
`Succ` (short for *successor*) are the *constructors* of the datatype.

Both definitions above tell us the same two things:

- *Base case*: `Zero` is a natural number.
- *Inductive case*: if `m` is a natural number, then `Succ m` is also a
  natural number.

Further, for finite inductive values, these two rules give the *only* ways
of creating natural numbers. Hence, the finite natural numbers are:

```text
Zero
Succ Zero
Succ (Succ Zero)
Succ (Succ (Succ Zero))
...
```

We write `0` as shorthand for `Zero`; `1` is shorthand for `Succ Zero`, the
successor of zero, that is, the natural that comes after zero; `2` is
shorthand for `Succ (Succ Zero)`, which is the same as `Succ 1`, the
successor of one; `3` is shorthand for the successor of two; and so on.

With `-XDataKinds` and `-XExperimentalDependentTypes`, `Nat` is simultaneously
an ordinary runtime algebraic datatype **and** a type-level kind whose promoted
constructors are `Zero` and `Succ`. Because neither `Zero` nor `Succ` collides
with any type constructor in scope, GHC lets us write `Zero` and `Succ` in
types directly without a leading quote (`'`).

<div class="note-box">
<strong>Totality note (Haskell vs. Agda):</strong>
In Agda, <code>ℕ</code> contains only finite inductive terms. In Haskell,
every lifted datatype also admits non-terminating expressions such as
<code>undefined</code> or infinite values like <code>let inf = Succ inf in inf</code>.
Our theorems in PLFH establish properties for all <em>finite</em>
inductive inputs; every proof is written by structural recursion without
bottoms, holes, or circular bindings.
</div>

#### Exercise `seven` (practice) {#seven}

Write out `7` in longhand using `Zero` and `Succ`. The suggestion below
typechecks but is, of course, incorrect:

```{.haskell .exercise}
seven :: Nat
seven = Zero
```

## Unpacking the inference rules

Let's unpack the inference rules. Each inference rule consists of zero or
more *judgments* written above a horizontal line, called the *hypotheses*,
and a single judgment written below, called the *conclusion*. The first rule
is the base case. It has no hypotheses, and the conclusion asserts that
`Zero` is a natural. The second rule is the inductive case. It has one
hypothesis, which assumes that `m` is a natural, and the conclusion asserts
that `Succ m` is also a natural.

## Unpacking the Haskell definition

Let's unpack the Haskell definition. The keyword `data` tells us this is an
inductive definition, that is, that we are defining a new datatype with
constructors. The keyword `where` (under `-XGADTs`) separates the declaration
of the datatype from the declaration of its constructors. Each constructor
is declared on a separate line, indented to indicate that it belongs to the
corresponding `data` declaration. The lines

```text
Zero :: Nat
Succ :: Nat -> Nat
```

give *signatures* specifying the types of the constructors `Zero` and `Succ`.
They tell us that `Zero` is a natural number and that `Succ` takes a natural
number as an argument and returns a natural number. (Equivalently, in classic
Haskell 98 syntax, we may write `data Nat = Zero | Succ Nat`.)

## The story of creation

Let's look again at the rules that define the natural numbers:

- *Base case*: `Zero` is a natural number.
- *Inductive case*: if `m` is a natural number, then `Succ m` is also a
  natural number.

Hold on! The second line defines natural numbers in terms of natural
numbers. How can that possibly be allowed? Isn't this as useless a
definition as "Brexit means Brexit"?

In fact, it is possible to assign our definition a meaning without
resorting to unpermitted circularities. Furthermore, we can do so while
only working with *finite* sets and never referring to the *infinite* set
of natural numbers.

We will think of it as a creation story. To start with, we know about no
natural numbers at all:

```text
-- In the beginning, there are no natural numbers.
```

Now, we apply the rules to all the natural numbers we know about. The base
case tells us that `Zero` is a natural number, so we add it to the set of
known natural numbers. The inductive case tells us that if `m` is a natural
number (on the day before today) then `Succ m` is also a natural number
(today). We didn't know about any natural numbers before today, so the
inductive case doesn't apply:

```text
-- On the first day, there is one natural number.
Zero :: Nat
```

Then we repeat the process. On the next day we know about all the numbers
from the day before, plus any numbers added by the rules. The base case
tells us that `Zero` is a natural number, but we already knew that. But now
the inductive case tells us that since `Zero` was a natural number
yesterday, then `Succ Zero` is a natural number today:

```text
-- On the second day, there are two natural numbers.
Zero :: Nat
Succ Zero :: Nat
```

And we repeat the process again. Now the inductive case tells us that since
`Zero` and `Succ Zero` are both natural numbers, then `Succ Zero` and
`Succ (Succ Zero)` are natural numbers. We already knew about the first of
these, but the second is new:

```text
-- On the third day, there are three natural numbers.
Zero :: Nat
Succ Zero :: Nat
Succ (Succ Zero) :: Nat
```

You've got the hang of it by now:

```text
-- On the fourth day, there are four natural numbers.
Zero :: Nat
Succ Zero :: Nat
Succ (Succ Zero) :: Nat
Succ (Succ (Succ Zero)) :: Nat
```

The process continues. On the *n*'th day there will be *n* distinct natural
numbers. Every natural number will appear on some given day. In particular,
the number *n* first appears on day *n + 1*. And we never actually define
the set of numbers in terms of itself. Instead, we define the set of
numbers on day *n + 1* in terms of the set of numbers on day *n*.

A process like this one is called *inductive*. We start with nothing, and
build up a potentially infinite set by applying rules that convert one
finite set into another finite set.

The rule defining zero is called a *base case*, because it introduces a
natural number even when we know no other natural numbers. The rule
defining successor is called an *inductive case*, because it introduces
more natural numbers once we already know some. Note the crucial role of
the base case. If we only had inductive rules, then we would have no
numbers in the beginning, and still no numbers on the second day, and on
the third, and so on. An inductive definition lacking a base case is
useless, as in the phrase "Brexit means Brexit".

## Philosophy and history

A philosopher might observe that our reference to the first day, second
day, and so on, implicitly involves an understanding of natural numbers. In
this sense, our definition might indeed be regarded as in some sense
circular, but we need not let this disturb us. Everyone possesses a good
informal understanding of the natural numbers, which we may take as a
foundation for their formal description.

While the natural numbers have been understood for as long as people can
count, the inductive definition of the natural numbers is relatively recent.
It can be traced back to Richard Dedekind's paper *"Was sind und was sollen
die Zahlen?"* (What are and what should be the numbers?), published in 1888,
and Giuseppe Peano's book *"Arithmetices principia, nova methodo exposita"*
(The principles of arithmetic presented by a new method), published the
following year.

## Pragmas and decimal numerals

In Haskell, as in Agda, any text following `--` or enclosed between `{-`
and `-}` is considered a *comment*, with one special kind of comment called
a *pragma*, enclosed between `{-#` and `#-}`. At the top of each chapter we
use a `LANGUAGE` pragma to enable Dependent Haskell extensions such as
`DataKinds`, `ExperimentalDependentTypes`, `GADTs`, and `TypeOperators`.

In PLFA, a `{-# BUILTIN NATURAL ℕ #-}` pragma enables typing `0`, `1`, `2`,
... as shorthand for `zero`, `suc zero`, `suc (suc zero)`, and so on. In
PLFH, `HaskLib.Nat` provides a `FromNatural` instance (at the type level)
and a `Num` instance (at the term level) for `Nat`. That gives us the exact
same shorthand—we can type `0`, `1`, `2`, `3`, `5`, ... directly in both
types and runtime expressions while continuing to pattern-match on `Zero`
and `Succ` in inductive definitions and proofs!

## Imports

Shortly we will want to write equations that hold between terms involving
natural numbers. At the top of this module we imported propositional
equality from `base`:

```{.haskell .ignore}
import Data.Type.Equality ((:~:) (Refl))
import HaskLib.Nat (Nat (..), plus, type (+))
```

Here `(:~:)` is the propositional equality type operator (playing the role
of Agda's `_≡_`), and `Refl` is its constructor providing evidence that two
terms are equal (playing the role of Agda's `refl`). We will define
propositional equality and equational reasoning chains from scratch in
Chapter [Equality](/Equality/).

## Operations on naturals are recursive functions {#plus}

Now that we have the natural numbers, what can we do with them? For
instance, can we define arithmetic operations such as addition and
multiplication?

As a child I spent much time memorising tables of addition and
multiplication. At first the rules seemed tricky and I would often make
mistakes. It came as a shock to me to discover *recursion*, a simple
technique by which every one of the infinite possible instances of addition
and multiplication can be specified in just a couple of lines.

Here is the definition of addition (reused from `HaskLib.Nat`, where infix
`type (+)` is also defined):

```{.haskell .ignore}
plus :: Nat -> Nat -> Nat
plus Zero     n = n
plus (Succ m) n = Succ (plus m n)
```

Let's unpack this definition. The first line is a signature specifying the
type of `plus`: `Nat -> Nat -> Nat` indicates that addition accepts two
naturals and returns a natural.

The definition has a base case and an inductive case, corresponding to
those for the natural numbers. The base case says that adding zero to a
number, `plus Zero n`, returns that number, `n`. The inductive case says
that adding the successor of a number to another number, `plus (Succ m) n`,
returns the successor of adding the two numbers, `Succ (plus m n)`. We say
we use *pattern matching* when constructors appear on the left-hand side of
an equation.

If we write `Zero` as `0` and `Succ m` as `1 + m`, the definition turns
into two familiar equations:

```text
0       + n  ≡  n
(1 + m) + n  ≡  1 + (m + n)
```

The first follows because zero is an identity for addition, and the second
because addition is associative. In its most general form, associativity is
written

```text
(m + n) + p  ≡  m + (n + p)
```

meaning that the location of parentheses is irrelevant. We get the second
equation from the third by taking `m` to be `1`, `n` to be `m`, and `p` to
be `n`. We write `=` for definitions, while we write `:~:` (or `≡` in prose)
for assertions that two already defined things are the same.

The definition is *recursive*, in that the last line defines addition in
terms of addition. As with the inductive definition of the naturals, the
apparent circularity is not a problem. It works because addition of larger
numbers is defined in terms of addition of smaller numbers. Such a
definition is called *well founded*.

For example, let's add two and three:

```text
  2 + 3
= (Succ (Succ Zero)) + (Succ (Succ (Succ Zero)))
= Succ ((Succ Zero) + (Succ (Succ (Succ Zero))))   -- inductive case
= Succ (Succ (Zero + (Succ (Succ (Succ Zero)))))   -- inductive case
= Succ (Succ (Succ (Succ (Succ Zero))))            -- base case
= 5
```

Or more compactly, expanding shorthand only as needed:

```text
  2 + 3
= Succ (1 + 3)          -- inductive case (m = 1, n = 3)
= Succ (Succ (0 + 3))   -- inductive case (m = 0, n = 3)
= Succ (Succ 3)         -- base case (n = 3)
= 5
```

Because `plus` is compiled with `-XExperimentalDependentTypes`, GHC records
its defining equations so we can compute with `plus` directly in **both**
type-level propositions and ordinary runtime code—without duplicating it as
a separate `type family`! GHC reduces `plus 2 3` directly to `5`, so `Refl`
suffices as ironclad evidence:

```haskell
-- | Evidence that 2 + 3 = 5 using ordinary Haskell `plus` and decimal numerals.
twoPlusThree :: plus 2 3 :~: 5
twoPlusThree = Refl

-- | The same proof using `HaskLib.Nat`'s infix type operator `(+)`.
twoPlusThreeInfix :: (2 + 3 :: Nat) :~: 5
twoPlusThreeInfix = Refl

-- | Ordinary runtime arithmetic using the same `Nat` and `Num` instance.
fiveAtRuntime :: Nat
fiveAtRuntime = 2 + 3
```

Here `plus 2 3 :~: 5` is a type, and `Refl` is a term of the given type;
alternatively, one can think of each term as *evidence* for the assertion
`2 + 3 ≡ 5`. This duality of interpretation—of a type as a proposition, and
of a term as evidence—is central to how we formalise concepts in Dependent
Haskell, and will be a running theme throughout this book.

Note that when we use the word *evidence* it is nothing equivocal. It is
not like testimony in a court which must be weighed to determine whether
the witness is trustworthy. Rather, it is ironclad. The other word for
evidence, which we will use interchangeably, is *proof*.

<div class="note-box">
<strong>HaskLib reuse:</strong>
<code>Nat</code>, <code>plus</code>, infix <code>type (+)</code>, and the
<code>FromNatural</code> / <code>Num</code> decimal-numeral instances are
reused directly from <code>HaskLib.Nat</code>.
</div>

#### Exercise `+-example` (practice) {#plus-example}

Compute `3 + 4`, writing out the reduction steps using the equations for
`plus`, and confirm `plus 3 4 :~: 7` with `Refl`.

```{.haskell .exercise}
-- Your code goes here
```

## Multiplication

Once we have defined addition, we can define multiplication as repeated
addition:

```haskell
-- | Multiply two natural numbers by recursion on the first argument.
times :: Nat -> Nat -> Nat
times Zero     n = Zero
times (Succ m) n = plus n (times m n)
```

Computing `times m n` returns the sum of `m` copies of `n`.

Again, rewriting turns the definition into two familiar equations:

```text
0       * n  ≡  0
(1 + m) * n  ≡  n + (m * n)
```

The first follows because zero times anything is zero, and the second
follows because multiplication distributes over addition. In its most
general form, distribution of multiplication over addition is written

```text
(m + n) * p  ≡  (m * p) + (n * p)
```

We get the second equation from the third by taking `m` to be `1`, `n` to
be `m`, and `p` to be `n`, and then using the fact that one is an identity
for multiplication, so `1 * n ≡ n`.

Again, the definition is well founded in that multiplication of larger
numbers is defined in terms of multiplication of smaller numbers.

For example, let's multiply two and three:

```text
  times 2 3
= plus 3 (times 1 3)           -- inductive case (m = 1, n = 3)
= plus 3 (plus 3 (times 0 3))  -- inductive case (m = 0, n = 3)
= plus 3 (plus 3 0)            -- base case (n = 3)
= 6
```

GHC checks `times 2 3 :~: 6` immediately using the defining equations of
`times`:

```haskell
-- | Evidence that 2 * 3 = 6 using ordinary `times` and decimal numerals.
twoTimesThree :: times 2 3 :~: 6
twoTimesThree = Refl
```

<div class="wip-notice">
<strong>[WIP NOTICE — Wildcard patterns break open source equations (R13/R16)]</strong>
Notice that we wrote <code>times Zero n = Zero</code> with a <em>named</em>
variable <code>n</code> rather than <code>times Zero _ = Zero</code>.
Currently, writing a wildcard <code>_</code> in
the base case silently prevents GHC from registering open source equations
for <code>times</code>, causing downstream proofs over unknown variables to
fail with <code>GHC-70565</code> (<em>Cannot evaluate 'times' in a type</em>).
See minimal reproducer
<a href="https://github.com/Tritlo/PLFH/blob/main/reproducers/R13_WildcardBreaksOpenEq.hs"><code>reproducers/R13_WildcardBreaksOpenEq.hs</code></a>.
</div>

#### Exercise `*-example` (practice) {#times-example}

Compute `3 * 4`, writing out the reduction steps using the equations for
`times`, and verify `times 3 4 :~: 12`.

```{.haskell .exercise}
-- Your code goes here
```

## Exponentiation (`_^_`) {#power}

PLFA poses exponentiation as a recommended exercise, given by the
equations:

```text
m ^ 0        =  1
m ^ (1 + n)  =  m * (m ^ n)
```

In Dependent Haskell we define `pow` directly by recursion on its second
argument:

```haskell
-- | Exponentiation by recursion on the second argument.
pow :: Nat -> Nat -> Nat
pow m Zero     = Succ Zero
pow m (Succ n) = times m (pow m n)
```

```haskell
-- | Concrete same-module exponentiation example: 3 ^ 4 = 81.
threePowFour :: pow 3 4 :~: 81
threePowFour = Refl
```

## Monus

We can also define subtraction. Since there are no negative natural
numbers, if we subtract a larger number from a smaller number we take the
result to be zero. This adaptation of subtraction to naturals is called
*monus* (a twist on *minus*, written `_∸_` in PLFA).

Monus is our first use of a definition that uses pattern matching against
both arguments:

```haskell
-- | Truncated subtraction (monus), matching PLFA's exact clause order.
monus :: Nat -> Nat -> Nat
monus m        Zero     = m
monus Zero     (Succ n) = Zero
monus (Succ m) (Succ n) = monus m n
```

We can do a simple analysis to show that all the cases are covered:

- Consider the second argument.
  - If it is `Zero`, then the first equation applies.
  - If it is `Succ n`, then consider the first argument.
    - If it is `Zero`, then the second equation applies.
    - If it is `Succ m`, then the third equation applies.

As with addition and multiplication, the recursive definition is well
founded because monus on bigger numbers is defined in terms of monus on
smaller numbers.

For example, subtracting two from three uses only the third and first
equations (`3 ∸ 2 = 2 ∸ 1 = 1 ∸ 0 = 1`), whereas subtracting three from two
also invokes the second equation (`2 ∸ 3 = 1 ∸ 2 = 0 ∸ 1 = 0`):

```haskell
-- | Concrete same-module truncated subtraction examples: 3 ∸ 2 = 1 and 2 ∸ 3 = 0.
threeMonusTwo :: monus 3 2 :~: 1
threeMonusTwo = Refl

twoMonusThree :: monus 2 3 :~: 0
twoMonusThree = Refl
```

Notice we defined `monus` so that the patterns are disjoint—exactly one
equation applies to any pair of inputs. If the second line were written
`monus Zero n = Zero`, then both the first and second equations would match
`monus Zero Zero` (in Haskell equations are tried top-to-bottom, whereas
disjoint clauses make the defining equations unambiguous in any order).

#### Exercise `∸-example₁` and `∸-example₂` (recommended) {#monus-examples}

Compute `5 ∸ 3` and `3 ∸ 5`, and verify `monus 5 3 :~: 2` and
`monus 3 5 :~: 0`.

```{.haskell .exercise}
-- Your code goes here
```

## Precedence and Currying

We often use *precedence* to avoid writing too many parentheses. Function
application *binds more tightly than* (or *has precedence over*) any infix
operator, so `Succ m + n` means `(Succ m) + n`. Similarly, multiplication
binds more tightly than addition (`infixl 7 *` vs. `infixl 6 +`), and
addition *associates to the left*, so `m + n + p` means `(m + n) + p`.

We have chosen to represent a function of two arguments in terms of a
function of the first argument that returns a function of the second
argument. This trick goes by the name *currying*.

Haskell, like Agda and ML, is designed to make currying easy to use.
Function arrows associate to the right and application associates to the
left:

- `Nat -> Nat -> Nat` stands for `Nat -> (Nat -> Nat)`, and
- `plus 2 3` stands for `(plus 2) 3`.

The term `plus 2` by itself stands for the function that adds two to its
argument, hence applying it to three yields five.

Currying is named for Haskell Curry, after whom the programming language
Haskell is also named. Curry's work dates to the 1930s. When Philip Wadler
first learned about currying, he was told it was misattributed, since the
same idea was previously proposed by Moses Schönfinkel in the 1920s—with
the joke: *"It should be called schönfinkeling, but currying is tastier"*.
Only later did he learn that the explanation of the misattribution was
itself a misattribution: the idea actually appears in the
*Begriffsschrift* of Gottlob Frege, published in 1879!

## The story of creation, revisited

Just as our inductive definition defines the naturals in terms of the
naturals, so does our recursive definition define addition in terms of
addition.

Again, it is possible to assign our definition a meaning without resorting
to unpermitted circularities. We do so by reducing our definition to
equivalent inference rules for judgments about equality:

<div class="inference-rule">
  <div class="premises">n :: Nat</div>
  <div class="conclusion">plus Zero n = n</div>
</div>
<div class="inference-rule">
  <div class="premises">plus m n = p</div>
  <div class="conclusion">plus (Succ m) n = Succ p</div>
</div>

Again we resort to a creation story, where this time we are concerned with
judgments about addition:

```text
-- In the beginning, we know nothing about addition.

-- On the first day, we know about addition of 0:
0 + 0 = 0     0 + 1 = 1     0 + 2 = 2     ...

-- On the second day, we know about addition of 0 and 1:
0 + 0 = 0     0 + 1 = 1     0 + 2 = 2     0 + 3 = 3     ...
1 + 0 = 1     1 + 1 = 2     1 + 2 = 3     1 + 3 = 4     ...

-- On the third day, we know about addition of 0, 1, and 2:
0 + 0 = 0     0 + 1 = 1     0 + 2 = 2     0 + 3 = 3     ...
1 + 0 = 1     1 + 1 = 2     1 + 2 = 3     1 + 3 = 4     ...
2 + 0 = 2     2 + 1 = 3     2 + 2 = 4     2 + 3 = 5     ...
```

On the *m*'th day we know all the equations where the first number is less
than *m*. As we can see, the reasoning that justifies inductive and
recursive definitions is quite similar—two sides of the same coin.

## The story of creation, finitely {#finite-creation}

The story above was told in a stratified way: first we created the infinite
set of naturals, and took that set as given when creating instances of
addition. Instead, we could choose to create both the naturals and the
instances of addition at the same time so that on any day there is only a
finite set of instances:

```text
-- On the first day, we know zero.
0 :: Nat

-- On the second day, we know one and all sums that yield zero.
0 :: Nat
1 :: Nat    0 + 0 = 0

-- On the third day, we know two and all sums that yield one.
0 :: Nat
1 :: Nat    0 + 0 = 0
2 :: Nat    0 + 1 = 1   1 + 0 = 1

-- On the fourth day, we know three and all sums that yield two.
0 :: Nat
1 :: Nat    0 + 0 = 0
2 :: Nat    0 + 1 = 1   1 + 0 = 1
3 :: Nat    0 + 2 = 2   1 + 1 = 2   2 + 0 = 2
```

On the *n*'th day there are *n* distinct natural numbers, and
*n × (n - 1) / 2* equations about addition. The number *n* and all
equations for addition of numbers less than *n* first appear by day *n + 1*.
This gives an entirely finitist view of infinite sets of data and equations
relating the data.

## Binary natural numbers (`Bin`, stretch exercise) {#Bin}

A more efficient representation of natural numbers uses a binary rather
than a unary system. We represent a number as a least-significant-bit-first
bitstring:

```haskell
-- | Least-significant-bit-first binary natural numbers.
data Bin
  = Nil
  | X0 Bin
  | X1 Bin
  deriving (Show)
```

For instance, the bitstring `1011` standing for the number eleven is
encoded (reading from least-significant bit outward) as
`X1 (X1 (X0 (X1 Nil)))` (written `⟨⟩ I O I I` in PLFA). Representations are
not unique due to leading zeros: eleven is also represented by `001011`,
encoded as `X1 (X1 (X0 (X1 (X0 (X0 Nil)))))`.

We define `inc` to convert a bitstring to the next higher number, together
with `toBin` and `fromBin` to convert between `Nat` and `Bin` (choosing no
leading zeros for positive naturals and representing zero by `X0 Nil`):

```haskell
-- | Increment a binary bitstring by one.
inc :: Bin -> Bin
inc Nil    = X1 Nil
inc (X0 b) = X1 b
inc (X1 b) = X0 (inc b)

-- | Convert unary `Nat` to `Bin`.
toBin :: Nat -> Bin
toBin Zero     = X0 Nil
toBin (Succ n) = inc (toBin n)

-- | Convert `Bin` back to unary `Nat`.
fromBin :: Bin -> Nat
fromBin Nil    = Zero
fromBin (X0 b) = plus (fromBin b) (fromBin b)
fromBin (X1 b) = Succ (plus (fromBin b) (fromBin b))
```

All three ordinary Haskell functions (`inc`, `toBin`, and `fromBin`)
automatically receive checked open source equations—so in
[Induction](/Induction/) we prove `fromBin (inc b) :~: Succ (fromBin b)`
and `fromBin (toBin n) :~: n` directly by induction, and in
[Relations](/Relations/) we complete the full bijection `Nat ≃ Can Bin`!

## Changes from PLFA

- Adapted from [Naturals](https://plfa.inf.ed.ac.uk/Naturals/)
  ([source](https://github.com/plfa/plfa.github.io/blob/dev/src/plfa/part1/Naturals.lagda.md)).
- Reused `Nat` (`Zero`/`Succ`), `plus`, infix `type (+)`, and decimal
  numerals (`FromNatural`/`Num`) from `HaskLib.Nat`.
- Implemented `times`, `pow`, `monus`, and `Bin`/`inc`/`toBin`/`fromBin` as
  ordinary Haskell functions checked directly in their defining module
  (`twoPlusThree`, `twoTimesThree`, `threePowFour`, `threeMonusTwo`,
  `twoMonusThree`).
- Omitted Agda's Emacs `agda-mode` keybinding walkthrough, `BUILTIN`
  pragmas, and Unicode input table, adding a Haskell totality note and the
  R13 wildcard note (`R13_WildcardBreaksOpenEq.hs`) instead.
