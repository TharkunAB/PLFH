{-# LANGUAGE DataKinds, ExperimentalDependentTypes, GADTs, TypeOperators #-}
-- | Minimal reproducer (Serokell R03):
-- Higher-order `foldrL plus Zero xs` is accepted in the type signature,
-- but rejected as a retained runtime argument to `plusAssoc` (GHC-83605).
-- Blocks PLFA Lists `foldr-monoid-++`.
module R03_FoldrRetainedIndex where

import Data.Type.Equality ((:~:) (Refl), gcastWith)
import HaskLib.Size (Size (..), congSucc, plus)
import ReproOps (app, foldrL)

plusAssoc :: foreach (m :: Size) -> foreach (n :: Size) -> foreach (p :: Size)
          -> plus (plus m n) p :~: plus m (plus n p)
plusAssoc Zero     _ _ = Refl
plusAssoc (Succ m) n p = congSucc (plusAssoc m n p)

foldrPlusAppend :: foreach (xs :: [Size]) -> foreach (ys :: [Size])
                -> foldrL plus 'Zero (app xs ys)
               :~: plus (foldrL plus 'Zero xs) (foldrL plus 'Zero ys)
foldrPlusAppend []       _  = Refl
foldrPlusAppend (x : xs) ys =
  gcastWith (foldrPlusAppend xs ys)
    (plusAssoc x (foldrL plus Zero xs) (foldrL plus Zero ys))
