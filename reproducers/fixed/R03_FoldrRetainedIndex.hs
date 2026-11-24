{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeApplications, TypeOperators #-}
{-# OPTIONS_GHC -fno-enable-rewrite-rules #-}
-- | Regression test (Serokell R03, fixed in c130ce0391):
-- Higher-order `foldrL plus Zero xs` as a retained runtime argument to `plusAssoc`.
module R03_FoldrRetainedIndex where

import Data.Type.Equality ((:~:) (Refl), sym, trans)
import HaskLib (cong)
import HaskLib.Nat (Nat (..), congSucc, plus)
import ReproOps (app, foldrL)

plusAssoc :: foreach (m :: Nat) -> foreach (n :: Nat) -> foreach (p :: Nat)
          -> plus (plus m n) p :~: plus m (plus n p)
plusAssoc Zero     _ _ = Refl
plusAssoc (Succ m) n p = congSucc (plusAssoc m n p)

foldrPlusAppend :: foreach (xs :: [Nat]) -> foreach (ys :: [Nat])
                -> foldrL plus Zero (app xs ys)
               :~: plus (foldrL plus Zero xs) (foldrL plus Zero ys)
foldrPlusAppend []       _  = Refl
foldrPlusAppend (x : xs) ys =
  trans (cong @(plus x) (foldrPlusAppend xs ys))
        (sym (plusAssoc x (foldrL plus Zero xs) (foldrL plus Zero ys)))
