{-# LANGUAGE DataKinds, ExperimentalDependentTypes, ExplicitForAll, GADTs #-}
-- | Minimal reproducer (R13 / DataKinds unquoted promoted constructor):
-- Removing the leading tick `'` from a promoted data constructor passed as an
-- argument to a same-module promoted function (`f m x (TMu x m)`) causes GHC
-- to fail with GHC-68947 ("No checked equations are available for 'f' in a
-- type"), even though:
--   1. The exact same declaration with a tick (`f m x ('TMu x m)`) compiles
--      cleanly and synthesizes `SourceTable T:f` and `axiom D:T:f`.
--   2. Unquoted `TMu` in the outer GADT index `Step (TMu x m) ...` works fine.
--
-- Hit while removing unnecessary `'` ticks from promoted constructors in
-- `PLFH.Part2.Lambda` (`BetaMu :: forall x m. Step (TMu x m) (substTerm m x (TMu x m))`).
--
-- Expected: Under -XDataKinds -XExperimentalDependentTypes, promoted
-- constructors with no colliding type constructor should not require `'`
-- inside arguments to promoted value-level functions.
-- Actual (published 6c8ab7f7de): GHC-68947 on `f` in `BetaMuUnquoted`.
module R13_UnquotedConstructorBreaksOpenEq where

data Nat = Zero | Succ Nat

eqId :: Nat -> Nat -> Bool
eqId Zero     Zero     = True
eqId Zero     (Succ _) = False
eqId (Succ _) Zero     = False
eqId (Succ m) (Succ n) = eqId m n

data Term = TZero | TMu Nat Term

f :: Term -> Nat -> Term -> Term
f TZero     _ _ = TZero
f (TMu x n) y v = case eqId x y of
  True  -> TMu x n
  False -> TMu x (f n y v)

-- Control (compiles cleanly if StepUnquoted is removed):
-- data StepQuoted (m :: Term) (n :: Term) where
--   BetaMuQuoted :: forall x m. StepQuoted (TMu x m) (f m x ('TMu x m))

-- Fails with GHC-68947 solely because `TMu` inside `f`'s 3rd arg lacks `'`:
data StepUnquoted (m :: Term) (n :: Term) where
  BetaMuUnquoted :: forall x m. StepUnquoted (TMu x m) (f m x (TMu x m))
