-- Generated from content/part2/Confluence.md by scripts/extract_and_sync.py
-- Do not edit directly; edit the literate Markdown chapter instead.

{-# LANGUAGE DataKinds, EmptyCase, ExperimentalDependentTypes, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures, TypeOperators #-}
{-# LINE 15 "content/part2/Confluence.md" #-}
module PLFH.Part2.Confluence
  ( bsTrans
  , bsApp1
  , bsApp2
  , bsLam
  , Par (..)
  , ParSteps (..)
  , psTrans
  , parToBetas
  , parsToBetas
  , omegaPar
  , Joinable (..)
  , strip
  , parConfluence
  , betasToPars
  , churchRosser
  ) where

import Data.Kind (Type)
import HaskLib.Nat (Nat (..))
import PLFH.Part2.Untyped
  ( BetaStep (..)
  , BetaSteps (..)
  , Fin (..)
  , OmegaTerm
  , SubstAtU (..)
  , UTerm (..)
  )

{-# LINE 65 "content/part2/Confluence.md" #-}
-- | Transitivity of multi-step β-reduction.
bsTrans :: BetaSteps s t -> BetaSteps t u -> BetaSteps s u
bsTrans BRefl       q = q
bsTrans (BCons s p) q = BCons s (bsTrans p q)

-- | Congruence of multi-step β-reduction in function, argument, and lambda body.
bsApp1 :: BetaSteps l l' -> BetaSteps ('UApp l m) ('UApp l' m)
bsApp1 BRefl       = BRefl
bsApp1 (BCons s p) = BCons (XiApp1 s) (bsApp1 p)

bsApp2 :: BetaSteps m m' -> BetaSteps ('UApp l m) ('UApp l m')
bsApp2 BRefl       = BRefl
bsApp2 (BCons s p) = BCons (XiApp2 s) (bsApp2 p)

bsLam :: BetaSteps b b' -> BetaSteps ('ULam b) ('ULam b')
bsLam BRefl       = BRefl
bsLam (BCons s p) = BCons (XiLam s) (bsLam p)

{-# LINE 91 "content/part2/Confluence.md" #-}
-- | Parallel β-reduction: contract any subset of redexes simultaneously.
type Par :: forall (n :: Nat). UTerm n -> UTerm n -> Type
data Par t t' where
  PVar  :: Par ('UVar x) ('UVar x)
  PLam  :: Par b b' -> Par ('ULam b) ('ULam b')
  PApp  :: Par l l' -> Par m m' -> Par ('UApp l m) ('UApp l' m')
  PBeta :: forall (n :: Nat) (b :: UTerm ('Succ n)) (b' :: UTerm ('Succ n))
                  (w :: UTerm n) (w' :: UTerm n) (r :: UTerm n).
           Par b b' -> Par w w' -> SubstAtU 'FZ w' b' r
        -> Par ('UApp ('ULam b) w) r

-- | Reflexive-transitive closure of parallel reduction (`_⇛*_`).
type ParSteps :: forall (n :: Nat). UTerm n -> UTerm n -> Type
data ParSteps t t' where
  PSRefl :: ParSteps t t
  PSCons :: Par s t -> ParSteps t u -> ParSteps s u

psTrans :: ParSteps x y -> ParSteps y z -> ParSteps x z
psTrans PSRefl        ys = ys
psTrans (PSCons x xs) ys = PSCons x (psTrans xs ys)

-- | Every parallel reduction step is simulated by zero or more β-steps!
parToBetas :: Par m n -> BetaSteps m n
parToBetas PVar              = BRefl
parToBetas (PLam p)          = bsLam (parToBetas p)
parToBetas (PApp pl pm)      = bsTrans (bsApp1 (parToBetas pl)) (bsApp2 (parToBetas pm))
parToBetas (PBeta pb pw sub) =
  bsTrans (bsApp1 (bsLam (parToBetas pb)))
    (bsTrans (bsApp2 (parToBetas pw)) (BCons (Beta sub) BRefl))

-- | Multi-step parallel reduction embeds into multi-step β-reduction.
parsToBetas :: ParSteps m n -> BetaSteps m n
parsToBetas PSRefl       = BRefl
parsToBetas (PSCons p q) = bsTrans (parToBetas p) (parsToBetas q)

-- | Concrete parallel reduction step: Ω ⇛ Ω.
omegaPar :: Par OmegaTerm OmegaTerm
omegaPar = PBeta (PApp PVar PVar) (PLam (PApp PVar PVar)) (SUApp SUEq SUEq)

{-# LINE 134 "content/part2/Confluence.md" #-}
-- | Two terms `m1` and `m2` are joinable under `rel` if they share a common reduct `n`.
type Joinable :: forall (n :: Nat). (UTerm n -> UTerm n -> Type) -> UTerm n -> UTerm n -> Type
data Joinable rel m1 m2 where
  Join :: rel m1 k -> rel m2 k -> Joinable rel m1 m2

-- | Strip Lemma: given the diamond property for `Par`, one `Par` step commutes
-- with any sequence of `ParSteps`!
strip :: forall (n :: Nat) (m :: UTerm n) (n1 :: UTerm n) (n2 :: UTerm n).
         (forall (a :: UTerm n) (b :: UTerm n) (c :: UTerm n).
            Par a b -> Par a c -> Joinable Par b c)
      -> Par m n1 -> ParSteps m n2 -> Joinable ParSteps n1 n2
strip _       p1 PSRefl         = Join PSRefl (PSCons p1 PSRefl)
strip diamond p1 (PSCons p2 ps) = case diamond p1 p2 of
  Join q1 q2 -> case strip diamond q2 ps of
    Join r1 r2 -> Join (PSCons q1 r1) r2

-- | Confluence of parallel reduction from the diamond property!
parConfluence :: forall (n :: Nat) (l :: UTerm n) (m1 :: UTerm n) (m2 :: UTerm n).
                 (forall (a :: UTerm n) (b :: UTerm n) (c :: UTerm n).
                    Par a b -> Par a c -> Joinable Par b c)
              -> ParSteps l m1 -> ParSteps l m2 -> Joinable ParSteps m1 m2
parConfluence _       PSRefl         ps2 = Join ps2 PSRefl
parConfluence diamond (PSCons p1 q1) ps2 = case strip diamond p1 ps2 of
  Join r1 r2 -> case parConfluence diamond q1 r1 of
    Join s1 s2 -> Join s1 (psTrans r2 s2)

-- | Lift a one-step embedding `BetaStep -> Par` to multi-step reduction.
betasToPars :: forall (n :: Nat) (m1 :: UTerm n) (m2 :: UTerm n).
               (forall (a :: UTerm n) (b :: UTerm n). BetaStep a b -> Par a b)
            -> BetaSteps m1 m2 -> ParSteps m1 m2
betasToPars _   BRefl        = PSRefl
betasToPars b2p (BCons s bs) = PSCons (b2p s) (betasToPars b2p bs)

-- | Church-Rosser Confluence for full β-reduction (`_—↠_`),
-- given `betaToPar` and the one-step diamond property for `Par`!
churchRosser :: forall (n :: Nat) (l :: UTerm n) (m1 :: UTerm n) (m2 :: UTerm n).
                (forall (a :: UTerm n) (b :: UTerm n). BetaStep a b -> Par a b)
             -> (forall (a :: UTerm n) (b :: UTerm n) (c :: UTerm n).
                   Par a b -> Par a c -> Joinable Par b c)
             -> BetaSteps l m1 -> BetaSteps l m2 -> Joinable BetaSteps m1 m2
churchRosser b2p diamond bs1 bs2 =
  case parConfluence diamond (betasToPars b2p bs1) (betasToPars b2p bs2) of
    Join ps1 ps2 -> Join (parsToBetas ps1) (parsToBetas ps2)
